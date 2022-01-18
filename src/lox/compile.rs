use crate::data::{self, List, SetValue, Slice};
use crate::heap::Handle;
use crate::inst::{self, Assembler, Label};
use crate::lox::scope::{self, CaptureFrom, ScopeSet, Var, VarKind, VarUse};
use crate::lox::syntax::{self, Block, Decl, Expr, ForInit, LValue, Param, Program, Stmt};
use crate::lox::token::{self, Kind, Token};
use crate::package::{Function, Global, Package, Type};
use crate::pos::{Error, ErrorList, LineMap, Pos, Position};
use std::collections::HashMap;
use std::fs;
use std::mem;
use std::path::Path;

pub fn compile_file<'a>(path: &Path) -> Result<Box<Package>, ErrorList> {
    let data = fs::read(path).map_err(|err| {
        let position = Position::from(path);
        let wrapped = Error::wrap(position, &err);
        ErrorList(vec![wrapped])
    })?;
    let mut lmap = LineMap::new();
    let tokens = token::lex(path, &data, &mut lmap)?;
    let ast = syntax::parse(&tokens, &lmap)?;
    let scopes = scope::resolve(&ast, &lmap)?;
    compile_from_ast(&ast, &scopes, &lmap)
}

pub fn compile_from_ast(
    ast: &Program,
    scopes: &ScopeSet,
    lmap: &LineMap,
) -> Result<Box<Package>, ErrorList> {
    let mut cmp = Compiler::new(scopes, lmap);
    for decl in &ast.decls {
        cmp.compile_decl(decl);
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
    errors: Vec<Error>,
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
            errors: Vec::new(),
        }
    }

    fn finish(&mut self) -> Result<Box<Package>, ErrorList> {
        self.asm().nil();
        self.asm().nanbox();
        self.asm().ret();
        match self.asm().finish() {
            Ok(init_insts) => {
                self.functions.push(Function {
                    name: String::from("·init"),
                    insts: init_insts,
                    package: 0 as *mut Package,
                    param_types: Vec::new(),
                    cell_types: Vec::new(),
                });
            }
            Err(err) => {
                self.errors.push(Error::wrap(self.lmap.first_file(), &err));
            }
        }

        if !self.errors.is_empty() {
            let mut errors = Vec::new();
            mem::swap(&mut errors, &mut self.errors);
            return Err(ErrorList(errors));
        }

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
        package.strings = Handle::new(Slice::alloc());
        package.strings.init_from_list(&self.strings);
        mem::swap(&mut package.types, &mut self.types);
        Ok(package)
    }

    fn compile_decl(&mut self, decl: &Decl<'a>) {
        match decl {
            Decl::Var {
                name,
                init,
                var,
                pos,
                ..
            } => {
                // Ensure storage for the varaible.
                let v = &self.scopes.vars[*var];
                self.compile_define_prepare(v, name.text, *pos);

                // Compile the initializer, if any.
                if let Some(e) = init {
                    self.compile_expr(e);
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
                pos,
                ..
            } => {
                let fn_index = self.compile_function(*name, params, body, *arg_scope, false, *pos);
                // Create a closure in the enclosing function.
                // The closure has pointers to cells of variables captured from
                // this function and enclosing functions.
                self.compile_define_prepare(&self.scopes.vars[*var], name.text, *pos);
                self.compile_closure(fn_index, *arg_scope, *pos);

                // Store the closure in a variable.
                self.compile_define(&self.scopes.vars[*var]);
            }
            Decl::Class {
                name,
                methods,
                var,
                base_var_use,
                pos,
                ..
            } => {
                // Prepare storage for the class.
                self.compile_define_prepare(&self.scopes.vars[*var], name.text, *pos);

                // Create a constructor closure which serves as the class value.
                // The constructor allocates a new objects, sets its prototype,
                // calls the initializer (if any), and returns the object.
                // TODO: this should be a callable object, not a closure.
                // Not sure how to represent that yet. But in JavaScript,
                // a class is a constructor function with methods on the
                // prototype, and functions are special kinds of objects.
                let init_param_count = methods.iter().find_map(|m| match m {
                    Decl::Function { name, params, .. } if name.text == "init" => {
                        Some(params.len() as u16)
                    }
                    _ => None,
                });
                let mut ctor_asm = Assembler::new();
                let object_type_index = self.ensure_type(Type::Object, *pos);
                ctor_asm.alloc(object_type_index);
                ctor_asm.dup();
                ctor_asm.prototype();
                ctor_asm.storeprototype();
                ctor_asm.nanbox();
                if let Some(arg_count) = init_param_count {
                    ctor_asm.dup();
                    for i in 0..arg_count {
                        ctor_asm.loadarg(i);
                    }
                    let si = self.ensure_string(b"init", *pos);
                    ctor_asm.callnamedprop(si, arg_count);
                    ctor_asm.pop();
                }
                ctor_asm.ret();
                let ctor_insts = match ctor_asm.finish() {
                    Ok(insts) => insts,
                    Err(err) => {
                        self.errors
                            .push(Error::wrap(self.lmap.position(*pos), &err));
                        return;
                    }
                };
                let ctor = Function {
                    name: format!("·{}·constructor", name.text),
                    insts: ctor_insts,
                    package: 0 as *mut Package,
                    param_types: vec![Type::Nanbox; init_param_count.unwrap_or(0) as usize],
                    cell_types: Vec::new(),
                };
                let ctor_index = match self.functions.len().try_into() {
                    Ok(i) => i,
                    _ => {
                        self.error(*pos, String::from("too many functions"));
                        !0
                    }
                };
                self.functions.push(ctor);
                self.asm().newclosure(ctor_index, 0, 0);
                self.asm().dup();

                // Create a prototype object. Don't box it yet.
                let prototype_type_index = self.ensure_type(Type::Object, *pos);
                self.asm().alloc(prototype_type_index);

                // If there's a base class, load its prototype, and use it as
                // our prototype's prototype.
                if let Some(base_var_use) = base_var_use {
                    self.asm().dup();
                    self.compile_var_use(&self.scopes.var_uses[*base_var_use]);
                    self.asm().loadprototype();
                    self.asm().storeprototype();
                }

                // Store methods in the prototype.
                if !methods.is_empty() {
                    // Box the prototype. The methods are boxed, and the
                    // instructions below expect both receiver and value
                    // to be boxed or neither.
                    self.asm().dup();
                    self.asm().nanbox();
                }
                let mut method_names = HashMap::<&'a str, Pos>::new();
                for method in methods {
                    match method {
                        Decl::Function {
                            name,
                            params,
                            body,
                            arg_scope,
                            pos,
                            ..
                        } => {
                            if let Some(prev_pos) = method_names.get(name.text) {
                                self.error(
                                    *pos,
                                    format!(
                                        "duplicate definition of {}; previous definition at {}",
                                        name.text,
                                        self.lmap.position(*prev_pos)
                                    ),
                                );
                                continue;
                            }
                            self.asm().dup();
                            let fn_index =
                                self.compile_function(*name, params, body, *arg_scope, true, *pos);
                            self.compile_closure(fn_index, *arg_scope, *pos);
                            let name_index = self.ensure_string(name.text.as_bytes(), name.pos);
                            self.asm().storemethod(name_index);
                            method_names.insert(name.text, *pos);
                        }
                        _ => unreachable!(),
                    };
                }
                if !methods.is_empty() {
                    self.asm().pop(); // boxed prototype
                }

                // Store the prototype in the constructor closure,
                // box the constructor closure, and store it in a variable.
                self.asm().storeprototype();
                self.asm().nanbox();
                self.compile_define(&self.scopes.vars[*var]);
            }
            Decl::Stmt(stmt) => self.compile_stmt(stmt),
        }
    }

    fn compile_function(
        &mut self,
        name: Token<'a>,
        params: &Vec<Param<'a>>,
        body: &Block<'a>,
        arg_scope: usize,
        is_method: bool,
        pos: Pos,
    ) -> u32 {
        // Start compiling the function.
        // Before anything else, move captured parameters into cells.
        self.asm_stack.push(Assembler::new());
        let mut cell_slot = 0;
        for param in params {
            if self.scopes.vars[param.var].kind == VarKind::Capture {
                let ty_index =
                    self.ensure_type(Type::Pointer(Box::new(Type::Nanbox)), param.name.pos);
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
            self.compile_decl(decl);
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
        let insts = match asm.finish() {
            Ok(insts) => insts,
            Err(err) => {
                self.errors.push(Error::wrap(self.lmap.position(pos), &err));
                return !0;
            }
        };
        let param_count = params.len() + (if is_method { 1 } else { 0 });
        let mut param_types = Vec::new();
        param_types.resize_with(param_count, || Type::Nanbox);
        let mut cell_types = Vec::new();
        cell_types.resize_with(self.scopes.scopes[arg_scope].captures.len(), || {
            Type::Pointer(Box::new(Type::Nanbox))
        });
        let f = Function {
            name: String::from(name.text),
            insts,
            package: 0 as *mut Package,
            param_types,
            cell_types,
        };
        let fn_index: u32 = match self.functions.len().try_into() {
            Ok(i) => i,
            Err(_) => {
                self.error(pos, String::from("too many functions"));
                return !0;
            }
        };
        self.functions.push(f);
        fn_index
    }

    fn compile_closure(&mut self, fn_index: u32, arg_scope: usize, pos: Pos) {
        for capture in &self.scopes.scopes[arg_scope].captures {
            match capture.from {
                CaptureFrom::Local => {
                    let slot = self.scopes.vars[capture.var].cell_slot as u16;
                    self.asm().loadlocal(slot);
                }
                CaptureFrom::Closure(slot) => {
                    self.asm().capture(slot as u16);
                }
            }
        }
        let raw_capture_count = self.scopes.scopes[arg_scope].captures.len();
        let capture_count: u16 = match raw_capture_count.try_into() {
            Ok(i) => i,
            _ => {
                self.error(pos, String::from("too many captures"));
                return;
            }
        };
        self.asm().newclosure(fn_index, capture_count, 0);
        self.asm().nanbox();
    }

    fn compile_stmt(&mut self, stmt: &Stmt<'a>) {
        match stmt {
            Stmt::Expr(e) => {
                self.compile_expr(e);
                self.asm().pop();
            }
            Stmt::Block(b) => {
                for decl in &b.decls {
                    self.compile_decl(decl);
                }
                self.pop_block(b.scope);
            }
            Stmt::Print { expr, .. } => {
                self.compile_expr(expr);
                self.asm().sys(inst::SYS_PRINT);
            }
            Stmt::If {
                cond,
                true_stmt,
                false_stmt,
                ..
            } => {
                self.compile_expr(cond);
                match false_stmt {
                    None => {
                        self.asm().not();
                        let mut after_label = Label::new();
                        self.asm().bif(&mut after_label);
                        self.compile_stmt(true_stmt);
                        self.asm().bind(&mut after_label);
                    }
                    Some(false_stmt) => {
                        let mut true_label = Label::new();
                        let mut after_label = Label::new();
                        self.asm().bif(&mut true_label);
                        self.compile_stmt(false_stmt);
                        self.asm().b(&mut after_label);
                        self.asm().bind(&mut true_label);
                        self.compile_stmt(true_stmt);
                        self.asm().bind(&mut after_label);
                    }
                }
            }
            Stmt::While { cond, body, .. } => {
                let mut body_label = Label::new();
                let mut cond_label = Label::new();
                self.asm().b(&mut cond_label);
                self.asm().bind(&mut body_label);
                self.compile_stmt(body);
                self.asm().bind(&mut cond_label);
                self.compile_expr(cond);
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
                        self.compile_decl(init);
                    }
                    ForInit::Expr(init) => {
                        self.compile_expr(init);
                    }
                    _ => (),
                };
                let mut body_label = Label::new();
                let mut cond_label = Label::new();
                if cond.is_some() {
                    self.asm().b(&mut cond_label);
                }
                self.asm().bind(&mut body_label);
                self.compile_stmt(body);
                if let Some(incr) = incr {
                    self.compile_expr(incr);
                    self.asm().pop();
                }
                match cond {
                    Some(cond) => {
                        self.asm().bind(&mut cond_label);
                        self.compile_expr(cond);
                        self.asm().bif(&mut body_label);
                    }
                    None => {
                        self.asm().b(&mut body_label);
                    }
                }
                self.pop_block(*scope);
            }
            Stmt::Return { expr, .. } => {
                // TODO: stop assembling instructions after a return.
                match expr {
                    Some(expr) => {
                        self.compile_expr(expr);
                    }
                    None => {
                        self.asm().nil();
                        self.asm().nanbox();
                    }
                }
                self.asm().ret();
            }
        }
    }

    fn compile_expr(&mut self, expr: &Expr<'a>) {
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
                    _ => unreachable!(),
                };
            }
            Expr::Number(t) => {
                let n = t.text.parse().unwrap();
                self.asm().float64(n);
                self.asm().nanbox();
            }
            Expr::String(t) => {
                let raw = t.text.as_bytes();
                if raw.len() < 2 || raw[0] != b'"' || raw[raw.len() - 1] != b'"' {
                    unreachable!();
                }
                let index = self.ensure_string(&raw[1..raw.len() - 1], t.pos);
                self.asm().string(index);
                self.asm().nanbox();
            }
            Expr::Var { var_use, .. } | Expr::This { var_use, .. } => {
                self.compile_var_use(&self.scopes.var_uses[*var_use]);
            }
            Expr::Group { expr, .. } => {
                self.compile_expr(expr);
            }
            Expr::Call {
                callee, arguments, ..
            } => {
                let arg_count: u16 = match arguments.len().try_into() {
                    Ok(n) => n,
                    _ => {
                        self.error(expr.pos(), String::from("too many arguments"));
                        !0
                    }
                };
                match callee.as_ref() {
                    Expr::Property { receiver, name, .. } => {
                        self.compile_expr(receiver);
                        for arg in arguments {
                            self.compile_expr(arg);
                        }
                        let si = self.ensure_string(name.text.as_bytes(), name.pos);
                        self.asm().callnamedprop(si, arg_count);
                    }
                    Expr::Super { name, var_use, .. } => {
                        self.compile_var_use(&self.scopes.var_uses[*var_use]);
                        self.asm().dup();
                        self.asm().loadprototype();
                        self.asm().loadprototype();
                        for arg in arguments {
                            self.compile_expr(arg);
                        }
                        let si = self.ensure_string(name.text.as_bytes(), name.pos);
                        self.asm().callnamedpropwithprototype(si, arg_count);
                    }
                    _ => {
                        self.compile_expr(callee);
                        for arg in arguments {
                            self.compile_expr(arg);
                        }
                        self.asm().callvalue(arg_count);
                    }
                }
            }
            Expr::Unary(op, e) => {
                self.compile_expr(e);
                match op.type_ {
                    Kind::Minus => self.asm().neg(),
                    Kind::Bang => self.asm().not(),
                    _ => unreachable!(),
                }
            }
            Expr::Binary(l, op, r) => {
                self.compile_expr(l);
                match op.type_ {
                    Kind::And => {
                        let mut after_label = Label::new();
                        self.asm().dup();
                        self.asm().not();
                        self.asm().bif(&mut after_label);
                        self.asm().pop();
                        self.compile_expr(r);
                        self.asm().not(); // ensure r produces a bool
                        self.asm().not();
                        self.asm().bind(&mut after_label);
                    }
                    Kind::Or => {
                        let mut after_label = Label::new();
                        self.asm().dup();
                        self.asm().bif(&mut after_label);
                        self.asm().pop();
                        self.compile_expr(r);
                        self.asm().not(); // ensure r produces a bool
                        self.asm().not();
                        self.asm().bind(&mut after_label);
                    }
                    _ => {
                        self.compile_expr(r);
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
                            _ => unreachable!(),
                        }
                    }
                }
            }
            Expr::Property { receiver, name, .. } => {
                self.compile_expr(receiver);
                let si = self.ensure_string(name.text.as_bytes(), name.pos);
                self.asm().loadnamedprop(si);
            }
            Expr::Super { name, var_use, .. } => {
                self.compile_var_use(&self.scopes.var_uses[*var_use]);
                self.asm().loadprototype();
                let si = self.ensure_string(name.text.as_bytes(), name.pos);
                self.asm().loadnamedprop(si);
            }
            Expr::Assign(l, r) => {
                match l {
                    LValue::Var { var_use, .. } => {
                        self.compile_expr(r);
                        self.asm().dup(); // TODO: only dup if the value is being used
                        let var_use = self.scopes.var_uses[*var_use];
                        self.compile_assign(var_use);
                    }
                    LValue::Property { receiver, name, .. } => {
                        self.compile_expr(receiver);
                        self.compile_expr(r);
                        self.asm().dup(); // TODO: only dup if the value is being used
                        self.asm().swapn(1);
                        self.asm().swap();
                        let si = self.ensure_string(name.text.as_bytes(), name.pos);
                        self.asm().storenamedprop(si);
                    }
                }
            }
        }
    }

    fn compile_define_prepare(&mut self, var: &Var, name: &str, pos: Pos) {
        match var.kind {
            VarKind::Global => {
                *self.ensure_global(var.slot) = Global {
                    name: String::from(name),
                };
            }
            VarKind::Local => {}
            VarKind::Capture => {
                let tyi = self.ensure_type(Type::Pointer(Box::new(Type::Nanbox)), pos);
                self.asm().alloc(tyi);
                self.asm().dup();
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
                        self.asm().capture(i.try_into().unwrap());
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

    fn compile_var_use(&mut self, var_use: &VarUse) {
        let v = &self.scopes.vars[var_use.var];
        match v.kind {
            VarKind::Global => self.asm().loadglobal(v.slot.try_into().unwrap()),
            VarKind::Argument => self.asm().loadarg(v.slot.try_into().unwrap()),
            VarKind::Local => self.asm().loadlocal(v.slot.try_into().unwrap()),
            VarKind::Capture => {
                match var_use.cell {
                    Some(i) => {
                        // Captured from enclosing function.
                        // The cell pointing to the variable is embedded in
                        // this function's closure.
                        self.asm().capture(i.try_into().unwrap());
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

    fn ensure_string(&mut self, s: &[u8], pos: Pos) -> u32 {
        let hs = Handle::new(data::String::from_bytes(s));
        match self.string_index.get(&*hs) {
            Some(v) => v.value,
            None => {
                let i: u32 = match (*self.strings).len().try_into() {
                    Ok(i) => i,
                    _ => {
                        self.error(pos, String::from("too many strings"));
                        return !0;
                    }
                };
                (*self.strings).push(&*hs);
                (*self.string_index).insert(&*hs, &SetValue { value: i });
                i
            }
        }
    }

    fn ensure_type(&mut self, type_: Type, pos: Pos) -> u32 {
        // TODO: deduplicate types.
        let i: u32 = match self.types.len().try_into() {
            Ok(i) => i,
            _ => {
                self.error(pos, String::from("too many types"));
                return !0;
            }
        };
        self.types.push(type_);
        i
    }

    fn asm(&mut self) -> &mut Assembler {
        self.asm_stack.last_mut().unwrap()
    }

    fn error(&mut self, pos: Pos, message: String) {
        self.errors.push(Error {
            position: self.lmap.position(pos),
            message,
        })
    }
}
