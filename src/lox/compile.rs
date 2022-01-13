use crate::data::{self, List, SetValue};
use crate::heap::Handle;
use crate::inst::{self, Assembler, Label};
use crate::lox::scope::{CaptureFrom, ScopeSet, Var, VarKind, VarUse};
use crate::lox::syntax::{Decl, Expr, ForInit, LValue, Program, Stmt};
use crate::lox::token::Kind;
use crate::package::{Function, Global, Package, Type};
use crate::pos::{Error, LineMap, Pos};
use std::mem;

pub fn compile(ast: &Program, scopes: &ScopeSet, lmap: &LineMap) -> Result<Box<Package>, Error> {
    let mut cmp = Compiler::new(scopes, lmap);
    for decl in &ast.decls {
        cmp.compile_decl(decl)?;
    }
    cmp.finish()
}

struct Compiler<'a, 'b> {
    scopes: &'b ScopeSet<'a>,
    lmap: &'a LineMap,
    globals: Vec<Global>,
    functions: Vec<Function>,
    strings: Handle<List<data::String>>,
    string_index: Handle<data::HashMap<data::String, SetValue<u32>>>,
    types: Vec<Type>,
    asm_stack: Vec<Assembler>,
}

impl<'a, 'b> Compiler<'a, 'b> {
    fn new(scopes: &'b ScopeSet<'a>, lmap: &'a LineMap) -> Compiler<'a, 'b> {
        Compiler {
            scopes,
            lmap,
            globals: Vec::new(),
            functions: Vec::new(),
            strings: Handle::new(List::alloc()),
            string_index: Handle::new(data::HashMap::alloc()),
            types: Vec::new(),
            asm_stack: vec![Assembler::new()],
        }
    }

    fn finish(&mut self) -> Result<Box<Package>, Error> {
        self.asm().nil();
        self.asm().nanbox();
        self.asm().ret();
        let init_insts = self.asm().finish().map_err(|err| {
            let position = self.lmap.first_file();
            Error::wrap(position, &err)
        })?;
        let init = Function {
            name: String::from("init"),
            insts: init_insts,
            package: 0 as *mut Package,
            param_types: Vec::new(),
            cell_types: Vec::new(),
        };
        self.functions.push(init);

        let mut package = Box::new(Package {
            globals: Vec::new(),
            functions: Vec::new(),
            strings: Handle::empty(),
            types: Vec::new(),
        });

        for f in &mut self.functions {
            f.package = &*package;
        }
        mem::swap(&mut package.globals, &mut self.globals);
        mem::swap(&mut package.functions, &mut self.functions);
        package.strings = Handle::new(self.strings.slice_mut());
        mem::swap(&mut package.types, &mut self.types);
        Ok(package)
    }

    fn compile_decl(&mut self, decl: &Decl<'a>) -> Result<(), Error> {
        match decl {
            Decl::Var {
                name, init, var, ..
            } => {
                // Ensure storage for the varaible.
                let v = &self.scopes.vars[*var];
                let (begin_pos, end_pos) = decl.pos();
                self.compile_define_prepare(v, name.text, begin_pos, end_pos)?;

                // Compile the initializer, if any.
                if let Some(e) = init {
                    self.compile_expr(e)?;
                } else {
                    self.asm().nil();
                    self.asm().nanbox();
                }

                // Write the initializer value to the variable.
                self.compile_define(v);
            }
            Decl::Function {
                name,
                params,
                body,
                var,
                arg_scope,
                ..
            } => {
                // Start compiling the function.
                // Before anything else, move captured parameters into cells.
                self.asm_stack.push(Assembler::new());
                let mut cell_slot = 0;
                for param in params {
                    if self.scopes.vars[param.var].kind == VarKind::Capture {
                        let ty_index = self.ensure_type(
                            Type::Pointer(Box::new(Type::Nanbox)),
                            param.name.from,
                            param.name.to,
                        )?;
                        self.asm().alloc(ty_index);
                        self.asm().dup();
                        let arg_slot = self.scopes.vars[param.var].slot as u16;
                        self.asm().loadarg(arg_slot);
                        self.asm().store();
                        assert_eq!(self.scopes.vars[param.var].cell_slot, cell_slot);
                        cell_slot += 1;
                    }
                }

                // Compile the function body.
                for decl in &body.decls {
                    self.compile_decl(decl)?;
                }

                // If the function didn't end with a return statement,
                // return nil.
                match body.decls.last() {
                    Some(Decl::Stmt(Stmt::Return { .. })) => {}
                    _ => {
                        self.asm().nil();
                        self.asm().nanbox();
                        self.asm().ret();
                    }
                }

                // Finish building the function and add it to the package.
                let mut asm = self.asm_stack.pop().unwrap();
                let insts = asm.finish().map_err(|err| {
                    let (from, to) = decl.pos();
                    Error::wrap(self.lmap.position(from, to), &err)
                })?;
                let mut param_types = Vec::new();
                param_types.resize_with(params.len(), || Type::Nanbox);
                let mut cell_types = Vec::new();
                cell_types.resize_with(self.scopes.scopes[*arg_scope].captures.len(), || {
                    Type::Pointer(Box::new(Type::Nanbox))
                });
                let f = Function {
                    name: String::from(name.text),
                    insts,
                    package: 0 as *mut Package,
                    param_types,
                    cell_types,
                };
                let fn_index = u32::try_from(self.functions.len()).map_err(|_| {
                    let (begin_pos, end_pos) = decl.pos();
                    Error {
                        position: self.lmap.position(begin_pos, end_pos),
                        message: String::from("too many functions"),
                    }
                })?;
                self.functions.push(f);

                // Create a closure in the enclosing function.
                // The closure has pointers to cells of variables captured from
                // this function and enclosing functions.
                let (begin_pos, end_pos) = decl.pos();
                self.compile_define_prepare(
                    &self.scopes.vars[*var],
                    name.text,
                    begin_pos,
                    end_pos,
                )?;
                for capture in &self.scopes.scopes[*arg_scope].captures {
                    match capture.from {
                        CaptureFrom::Local => {
                            let slot = self.scopes.vars[capture.var].cell_slot as u16;
                            self.asm().loadlocal(slot);
                        }
                        CaptureFrom::Closure(slot) => {
                            self.asm().cell(slot as u16);
                        }
                    }
                }
                let capture_count = self.scopes.scopes[*arg_scope].captures.len();
                let capture_count = u16::try_from(capture_count).map_err(|_| {
                    let (begin_pos, end_pos) = decl.pos();
                    Error {
                        position: self.lmap.position(begin_pos, end_pos),
                        message: String::from("too many captures"),
                    }
                })?;
                self.asm().newclosure(fn_index, capture_count);
                self.asm().nanbox();

                // Store the closure in a variable.
                self.compile_define(&self.scopes.vars[*var]);
            }
            Decl::Class {
                name,
                methods,
                var,
                begin_pos,
                end_pos,
                ..
            } => {
                // Prepare storage for the class.
                self.compile_define_prepare(
                    &self.scopes.vars[*var],
                    name.text,
                    *begin_pos,
                    *end_pos,
                )?;

                // Create a prototype object.
                let cell_type = Type::Pointer(Box::new(Type::Nanbox));
                let cell_type_index = self.ensure_type(cell_type.clone(), *begin_pos, *end_pos)?;
                self.asm().alloc(cell_type_index);
                self.asm().dup();
                let prototype_type_index = self.ensure_type(Type::Object, *begin_pos, *end_pos)?;
                self.asm().alloc(prototype_type_index);
                self.asm().nanbox();
                self.asm().store();
                // TODO: store methods in the prototype.
                if !methods.is_empty() {
                    unimplemented!();
                }

                // Create a constructor closure which serves as the class value.
                // The constructor allocates a new objects, sets its prototype,
                // calls the initializer (if any), and returns the object.
                let mut ctor_asm = Assembler::new();
                let object_type_index = self.ensure_type(Type::Object, *begin_pos, *end_pos)?;
                ctor_asm.alloc(object_type_index);
                ctor_asm.nanbox();
                ctor_asm.dup();
                ctor_asm.cell(0);
                ctor_asm.load();
                ctor_asm.storeprototype();
                // TODO: call initializer.
                ctor_asm.ret();
                let ctor_insts = ctor_asm
                    .finish()
                    .map_err(|err| Error::wrap(self.lmap.position(*begin_pos, *end_pos), &err))?;
                let ctor = Function {
                    name: format!("·{}·constructor", name.text),
                    insts: ctor_insts,
                    package: 0 as *mut Package,
                    param_types: Vec::new(),
                    cell_types: vec![cell_type],
                };
                let ctor_index = self.functions.len().try_into().map_err(|_| Error {
                    position: self.lmap.position(*begin_pos, *end_pos),
                    message: String::from("too many functions"),
                })?;
                self.functions.push(ctor);
                self.asm().newclosure(ctor_index, 1);
                self.asm().nanbox();
                self.compile_define(&self.scopes.vars[*var]);
            }
            Decl::Stmt(stmt) => self.compile_stmt(stmt)?,
        }
        Ok(())
    }

    fn compile_stmt(&mut self, stmt: &Stmt<'a>) -> Result<(), Error> {
        match stmt {
            Stmt::Expr(e) => {
                self.compile_expr(e)?;
                self.asm().pop();
            }
            Stmt::Block(b) => {
                for decl in &b.decls {
                    self.compile_decl(decl)?;
                }
                self.pop_block(b.scope);
            }
            Stmt::Print { expr, .. } => {
                self.compile_expr(expr)?;
                self.asm().sys(inst::SYS_PRINT);
            }
            Stmt::If {
                cond,
                true_stmt,
                false_stmt,
                ..
            } => {
                self.compile_expr(cond)?;
                match false_stmt {
                    None => {
                        self.asm().not();
                        let mut after_label = Label::new();
                        self.asm().bif(&mut after_label);
                        self.compile_stmt(true_stmt)?;
                        self.asm().bind(&mut after_label);
                    }
                    Some(false_stmt) => {
                        let mut true_label = Label::new();
                        let mut after_label = Label::new();
                        self.asm().bif(&mut true_label);
                        self.compile_stmt(false_stmt)?;
                        self.asm().b(&mut after_label);
                        self.asm().bind(&mut true_label);
                        self.compile_stmt(true_stmt)?;
                        self.asm().bind(&mut after_label);
                    }
                }
            }
            Stmt::While { cond, body, .. } => {
                let mut body_label = Label::new();
                let mut cond_label = Label::new();
                self.asm().b(&mut cond_label);
                self.asm().bind(&mut body_label);
                self.compile_stmt(body)?;
                self.asm().bind(&mut cond_label);
                self.compile_expr(cond)?;
                self.asm().bif(&mut body_label);
            }
            Stmt::For {
                init,
                cond,
                incr,
                body,
                scope,
                ..
            } => {
                match init {
                    ForInit::Var(init) => {
                        self.compile_decl(init)?;
                    }
                    ForInit::Expr(init) => {
                        self.compile_expr(init)?;
                    }
                    _ => (),
                };
                let mut body_label = Label::new();
                let mut cond_label = Label::new();
                if cond.is_some() {
                    self.asm().b(&mut cond_label);
                }
                self.asm().bind(&mut body_label);
                self.compile_stmt(body)?;
                if let Some(incr) = incr {
                    self.compile_expr(incr)?;
                    self.asm().pop();
                }
                match cond {
                    Some(cond) => {
                        self.asm().bind(&mut cond_label);
                        self.compile_expr(cond)?;
                        self.asm().bif(&mut body_label);
                    }
                    None => {
                        self.asm().b(&mut body_label);
                    }
                }
                self.pop_block(*scope);
            }
            Stmt::Return { expr, .. } => {
                match expr {
                    Some(expr) => {
                        self.compile_expr(expr)?;
                    }
                    None => {
                        self.asm().nil();
                        self.asm().nanbox();
                    }
                }
                self.asm().ret();
            }
        }
        Ok(())
    }

    fn compile_expr(&mut self, expr: &Expr<'a>) -> Result<(), Error> {
        match expr {
            Expr::Nil(_) => {
                self.asm().nil();
                self.asm().nanbox();
            }
            Expr::Bool(t) => {
                match t.text {
                    "true" => {
                        self.asm().true_();
                        self.asm().nanbox();
                    }
                    "false" => {
                        self.asm().false_();
                        self.asm().nanbox();
                    }
                    _ => {
                        return Err(Error {
                            position: self.lmap.position(t.from, t.to),
                            message: format!("not a real bool: '{}'", t.text),
                        })
                    }
                };
            }
            Expr::Number(t) => {
                let n = t.text.parse().map_err(|_| Error {
                    position: self.lmap.position(t.from, t.to),
                    message: format!("could not express '{}' as 64-bit floating point", t.text),
                })?;
                self.asm().float64(n);
                self.asm().nanbox();
            }
            Expr::String(t) => {
                let raw = t.text.as_bytes();
                if raw.len() < 2 || raw[0] != b'"' || raw[raw.len() - 1] != b'"' {
                    return Err(Error {
                        position: self.lmap.position(t.from, t.to),
                        message: format!("not a real string: '{}'", t.text),
                    });
                }
                let index = self.ensure_string(&raw[1..raw.len() - 1], t.from, t.to)?;
                self.asm().string(index);
                self.asm().nanbox();
            }
            Expr::Var { var_use, .. } => {
                let vu = self.scopes.var_uses[*var_use];
                let v = &self.scopes.vars[vu.var];
                match v.kind {
                    VarKind::Global => self.asm().loadglobal(v.slot.try_into().unwrap()),
                    VarKind::Argument => self.asm().loadarg(v.slot.try_into().unwrap()),
                    VarKind::Local => self.asm().loadlocal(v.slot.try_into().unwrap()),
                    VarKind::Capture => {
                        match vu.cell {
                            Some(i) => {
                                // Captured from enclosing function.
                                // The cell pointing to the variable is embedded in
                                // this function's closure.
                                self.asm().cell(i.try_into().unwrap());
                            }
                            None => {
                                // Captured variable defined in this function.
                                // Load the cell from the stack.
                                self.asm().loadlocal(v.cell_slot.try_into().unwrap());
                            }
                        };
                        self.asm().load();
                    }
                }
            }
            Expr::Group { expr, .. } => {
                self.compile_expr(expr)?;
            }
            Expr::Call {
                callee, arguments, ..
            } => {
                let arg_count = u16::try_from(arguments.len()).map_err(|_| {
                    let (begin_pos, end_pos) = expr.pos();
                    Error {
                        position: self.lmap.position(begin_pos, end_pos),
                        message: String::from("too many arguments"),
                    }
                })?;
                self.compile_expr(callee)?;
                for arg in arguments {
                    self.compile_expr(arg)?;
                }
                self.asm().callvalue(arg_count);
                self.asm().swap();
                self.asm().pop();
            }
            Expr::Unary(op, e) => {
                self.compile_expr(e)?;
                match op.type_ {
                    Kind::Minus => self.asm().neg(),
                    Kind::Bang => self.asm().not(),
                    _ => {
                        return Err(Error {
                            position: self.lmap.position(op.from, op.to),
                            message: format!("unknown unary operator {}", op.text),
                        })
                    }
                }
            }
            Expr::Binary(l, op, r) => {
                self.compile_expr(l)?;
                match op.type_ {
                    Kind::And => {
                        let mut after_label = Label::new();
                        self.asm().dup();
                        self.asm().not();
                        self.asm().bif(&mut after_label);
                        self.asm().pop();
                        self.compile_expr(r)?;
                        self.asm().not(); // ensure r produces a bool
                        self.asm().not();
                        self.asm().bind(&mut after_label);
                    }
                    Kind::Or => {
                        let mut after_label = Label::new();
                        self.asm().dup();
                        self.asm().bif(&mut after_label);
                        self.asm().pop();
                        self.compile_expr(r)?;
                        self.asm().not(); // ensure r produces a bool
                        self.asm().not();
                        self.asm().bind(&mut after_label);
                    }
                    _ => {
                        self.compile_expr(r)?;
                        match op.type_ {
                            Kind::Eq => self.asm().eq(),
                            Kind::Ne => self.asm().ne(),
                            Kind::Lt => self.asm().lt(),
                            Kind::Le => self.asm().le(),
                            Kind::Gt => self.asm().gt(),
                            Kind::Ge => self.asm().ge(),
                            Kind::Plus => self.asm().add(),
                            Kind::Minus => self.asm().sub(),
                            Kind::Star => self.asm().mul(),
                            Kind::Slash => self.asm().div(),
                            _ => {
                                return Err(Error {
                                    position: self.lmap.position(op.from, op.to),
                                    message: format!("unknown binary operator {}", op.text),
                                })
                            }
                        }
                    }
                }
            }
            Expr::Assign(l, r) => {
                self.compile_expr(r)?;
                self.asm().dup(); // TODO: only dup if the value is being used
                match l {
                    LValue::Var { var_use, .. } => {
                        let var_use = self.scopes.var_uses[*var_use];
                        self.compile_assign(var_use);
                    }
                }
            }
        }
        Ok(())
    }

    fn compile_define_prepare(
        &mut self,
        var: &Var,
        name: &str,
        begin_pos: Pos,
        end_pos: Pos,
    ) -> Result<(), Error> {
        match var.kind {
            VarKind::Global => {
                *self.ensure_global(var.slot) = Global {
                    name: String::from(name),
                };
                Ok(())
            }
            VarKind::Local => Ok(()),
            VarKind::Capture => {
                let tyi =
                    self.ensure_type(Type::Pointer(Box::new(Type::Nanbox)), begin_pos, end_pos)?;
                self.asm().alloc(tyi);
                self.asm().dup();
                Ok(())
            }
            VarKind::Argument => unreachable!(),
        }
    }

    fn compile_define(&mut self, var: &Var) {
        match var.kind {
            VarKind::Global => self.asm().storeglobal(var.slot.try_into().unwrap()),
            VarKind::Local => {
                // When a local variable is defined, it's always assigned
                // to the top of the stack. Since the value being assigned
                // is already there, we don't need to emit an instruction.
            }
            VarKind::Capture => {
                self.asm().store();
            }
            VarKind::Argument => unreachable!(),
        }
    }

    fn compile_assign(&mut self, var_use: VarUse) {
        let v = &self.scopes.vars[var_use.var];
        match v.kind {
            VarKind::Global => self.asm().storeglobal(v.slot.try_into().unwrap()),
            VarKind::Argument => {
                self.asm().storearg(v.slot.try_into().unwrap());
            }
            VarKind::Local => {
                self.asm().storelocal(v.slot.try_into().unwrap());
            }
            VarKind::Capture => {
                match var_use.cell {
                    Some(i) => {
                        // Captured from enclosing function.
                        // The cell pointing to the variable is embedded in
                        // this function's closure.
                        self.asm().cell(i.try_into().unwrap());
                    }
                    None => {
                        // Captured variable defined in this function.
                        // Load the cell from the stack.
                        self.asm().loadlocal(v.cell_slot.try_into().unwrap());
                    }
                }
                self.asm().swap();
                self.asm().store();
            }
        }
    }

    fn ensure_global(&mut self, index: usize) -> &mut Global {
        if self.globals.len() <= index {
            self.globals.resize_with(index + 1, || Global {
                name: String::from(""),
            });
        }
        &mut self.globals[index]
    }

    fn pop_block(&mut self, scope: usize) {
        let slot_count = self.scopes.scopes[scope].vars.len();
        for _ in 0..slot_count {
            self.asm().pop();
        }
    }

    fn ensure_string(&mut self, s: &[u8], from: Pos, to: Pos) -> Result<u32, Error> {
        let hs = Handle::new(data::String::from_bytes(s));
        match self.string_index.get(&*hs) {
            Some(v) => Ok(v.value),
            None => {
                let i = u32::try_from((*self.strings).len()).map_err(|_| Error {
                    position: self.lmap.position(from, to),
                    message: format!("too many strings"),
                })?;
                (*self.strings).push(&*hs);
                (*self.string_index).insert(&*hs, &SetValue { value: i });
                Ok(i)
            }
        }
    }

    fn ensure_type(&mut self, type_: Type, from: Pos, to: Pos) -> Result<u32, Error> {
        // TODO: deduplicate types.
        let i = u32::try_from(self.types.len()).map_err(|_| Error {
            position: self.lmap.position(from, to),
            message: format!("too many types"),
        })?;
        self.types.push(type_);
        Ok(i)
    }

    fn asm(&mut self) -> &mut Assembler {
        self.asm_stack.last_mut().unwrap()
    }
}
