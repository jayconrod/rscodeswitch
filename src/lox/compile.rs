use crate::data::{self, List, SetValue};
use crate::heap::Handle;
use crate::inst::{self, Assembler, Label};
use crate::lox::syntax::{Block, Decl, Expr, File, ForInit, LValue, Stmt};
use crate::lox::token::{Kind, Token};
use crate::package::{Function, Global, Package, Type};
use crate::pos::{Error, LineMap, Pos};
use std::collections::HashMap;
use std::mem;

pub fn compile(ast: &File, lmap: &LineMap) -> Result<Box<Package>, Error> {
    let mut cmp = Compiler::new(lmap);
    for decl in &ast.decls {
        if let Some(name) = decl.name() {
            let (begin_pos, end_pos) = decl.pos();
            cmp.declare_var(name, begin_pos, end_pos)?;
        }
    }
    for decl in &ast.decls {
        cmp.compile_decl(decl)?;
    }
    cmp.finish()
}

struct Compiler<'a> {
    lmap: &'a LineMap,
    globals: Vec<Global>,
    functions: Vec<Function>,
    strings: Handle<List<data::String>>,
    string_index: Handle<data::HashMap<data::String, SetValue<u32>>>,
    env_stack: Vec<Env<'a>>,
}

struct Env<'a> {
    asm: Assembler,
    scope: HashMap<&'a str, ScopeEntry>,
    next: u32,
    kind: EnvKind,
}

impl<'a> Env<'a> {
    fn new(kind: EnvKind) -> Env<'a> {
        Env {
            asm: Assembler::new(),
            scope: HashMap::new(),
            next: 0,
            kind,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EnvKind {
    Global,
    Function,
    Block,
}

struct ScopeEntry {
    def_begin_pos: Pos,
    def_end_pos: Pos,
    storage: Storage,
    defined: bool,
}

#[derive(Clone, Copy)]
enum Storage {
    Global(u32),
    Arg(u16),
    Local(u16),
}

impl<'a> Compiler<'a> {
    fn new(lmap: &'a LineMap) -> Compiler {
        Compiler {
            lmap: lmap,
            globals: Vec::new(),
            functions: Vec::new(),
            strings: Handle::new(List::alloc()),
            string_index: Handle::new(data::HashMap::alloc()),
            env_stack: vec![Env::new(EnvKind::Global)],
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
        };
        self.functions.push(init);

        let mut package = Box::new(Package {
            globals: Vec::new(),
            functions: Vec::new(),
            strings: Handle::empty(),
        });

        for f in &mut self.functions {
            f.package = &*package;
        }
        mem::swap(&mut package.globals, &mut self.globals);
        mem::swap(&mut package.functions, &mut self.functions);
        package.strings = Handle::new(self.strings.slice_mut());
        Ok(package)
    }

    /// declare creates storage for a new variable and binds it within the
    /// current scope. If the new variable is global, declare creates a Global
    /// and adds it to the package; the global's index will match the storage
    /// index. If the variable's name is already bound, declare returns an
    /// error.
    fn declare_var(
        &mut self,
        name: Token<'a>,
        begin_pos: Pos,
        end_pos: Pos,
    ) -> Result<Storage, Error> {
        if let Some(prev) = self.env().scope.get(name.text) {
            let begin = prev.def_begin_pos;
            let end = prev.def_end_pos;
            return Err(Error {
                position: self.lmap.position(name.from, name.to),
                message: format!(
                    "duplication definition of {}; previous definition at {}",
                    name.text,
                    self.lmap.position(begin, end)
                ),
            });
        }
        let storage = match self.env().kind {
            EnvKind::Global => {
                assert_eq!(self.env().next as usize, self.globals.len());
                let i = self.env().next;
                self.globals.push(Global {
                    name: String::from(name.text),
                });
                Storage::Global(i)
            }
            EnvKind::Function => {
                let i = u16::try_from(self.env().next).map_err(|_| Error {
                    position: self.lmap.position(name.from, name.to),
                    message: format!("too many parameters"),
                })?;
                Storage::Arg(i)
            }
            EnvKind::Block => {
                let i = u16::try_from(self.env().next).map_err(|_| Error {
                    position: self.lmap.position(name.from, name.to),
                    message: format!("too many local variables"),
                })?;
                Storage::Local(i)
            }
        };
        self.env().scope.insert(
            name.text,
            ScopeEntry {
                def_begin_pos: begin_pos,
                def_end_pos: end_pos,
                storage,
                defined: true,
            },
        );
        self.env().next += 1;
        Ok(storage)
    }

    fn compile_decl(&mut self, decl: &Decl<'a>) -> Result<(), Error> {
        let (begin_pos, end_pos) = decl.pos();
        match decl {
            Decl::Var { name, init, .. } => {
                if let Some(e) = init {
                    self.compile_expr(e)?;
                } else {
                    self.asm().nil();
                    self.asm().nanbox();
                }
                if self.env().kind != EnvKind::Global {
                    // Globals are already declared, so we won't repeat the
                    // declaration here.
                    self.declare_var(*name, begin_pos, end_pos)?;
                }
                self.compile_assign(*name, true)?;
            }
            Decl::Function {
                name,
                param_names,
                body,
                ..
            } => {
                self.env_stack.push(Env::new(EnvKind::Function));
                for name in param_names {
                    self.declare_var(*name, name.from, name.to)?;
                }
                self.enter_block();
                for decl in &body.decls {
                    self.compile_decl(decl)?;
                }
                self.leave_block();
                match body.decls.last() {
                    Some(Decl::Stmt(Stmt::Return { .. })) => {}
                    _ => {
                        self.asm().nil();
                        self.asm().nanbox();
                        self.asm().ret();
                    }
                }

                let mut env = self.env_stack.pop().unwrap();
                let insts = env.asm.finish().map_err(|err| {
                    let (from, to) = decl.pos();
                    Error::wrap(self.lmap.position(from, to), &err)
                })?;
                let mut param_types = Vec::new();
                param_types.resize(param_names.len(), Type::Nanbox);
                let f = Function {
                    name: String::from(name.text),
                    insts,
                    package: 0 as *mut Package,
                    param_types,
                };
                let index = u32::try_from(self.functions.len()).map_err(|_| {
                    let (begin_pos, end_pos) = decl.pos();
                    Error {
                        position: self.lmap.position(begin_pos, end_pos),
                        message: String::from("too many functions"),
                    }
                })?;
                self.functions.push(f);

                self.asm().function(index);
                self.asm().nanbox();
                self.compile_assign(*name, true)?;
            }
            Decl::Stmt(stmt) => self.compile_stmt(stmt)?,
        }
        Ok(())
    }

    fn compile_block(&mut self, block: &Block<'a>) -> Result<(), Error> {
        self.enter_block();
        for decl in &block.decls {
            self.compile_decl(decl)?;
        }
        self.leave_block();
        Ok(())
    }

    fn compile_stmt(&mut self, stmt: &Stmt<'a>) -> Result<(), Error> {
        match stmt {
            Stmt::Expr(e) => {
                self.compile_expr(e)?;
                self.asm().pop();
            }
            Stmt::Block(b) => {
                self.compile_block(b)?;
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
                ..
            } => {
                match init {
                    ForInit::Var(init) => {
                        self.enter_block();
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
                if let ForInit::Var(_) = init {
                    self.leave_block();
                }
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
                let s = Handle::new(data::String::from_bytes(&raw[1..raw.len() - 1]));
                let index = match self.string_index.get(&*s) {
                    Some(v) => v.value,
                    None => {
                        let i = u32::try_from((*self.strings).len()).map_err(|_| Error {
                            position: self.lmap.position(t.from, t.to),
                            message: format!("too many strings"),
                        })?;
                        (*self.strings).push(&*s);
                        (*self.string_index).insert(&*s, &SetValue { value: i });
                        i
                    }
                };
                self.asm().string(index);
                self.asm().nanbox();
            }
            Expr::Var(t) => match self.resolve(*t)? {
                Storage::Global(i) => {
                    self.asm().loadglobal(i);
                }
                Storage::Arg(i) => {
                    self.asm().loadarg(i);
                }
                Storage::Local(i) => {
                    self.asm().loadlocal(i);
                }
            },
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
            Expr::Assign(l, r) => {
                self.compile_expr(r)?;
                self.asm().dup(); // TODO: only dup if the value is being used
                match l {
                    LValue::Var(t) => {
                        self.compile_assign(*t, false)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn compile_assign(&mut self, name: Token<'a>, in_def: bool) -> Result<(), Error> {
        match self.resolve(name)? {
            Storage::Global(i) => {
                self.asm().storeglobal(i);
            }
            Storage::Arg(i) => {
                assert!(!in_def);
                self.asm().storearg(i);
            }
            Storage::Local(i) => {
                if !in_def {
                    self.asm().storelocal(i);
                }
            }
        }
        Ok(())
    }

    fn env(&mut self) -> &mut Env<'a> {
        self.env_stack.last_mut().unwrap()
    }

    fn asm(&mut self) -> &mut Assembler {
        let mut i = self.env_stack.len() - 1;
        loop {
            if self.env_stack[i].kind != EnvKind::Block {
                return &mut self.env_stack[i].asm;
            }
            assert!(i > 0);
            i -= 1;
        }
    }

    fn enter_block(&mut self) {
        let last_env = self.env();
        let next = match last_env.kind {
            EnvKind::Block => last_env.next,
            EnvKind::Function | EnvKind::Global => 0,
        };
        let mut env = Env::new(EnvKind::Block);
        env.next = next;
        self.env_stack.push(env);
    }

    fn leave_block(&mut self) {
        let env = self.env_stack.pop().unwrap();
        assert!(env.kind == EnvKind::Block);
        let last_env = self.env();
        let slot_count = match last_env.kind {
            EnvKind::Block => env.next - last_env.next,
            EnvKind::Function | EnvKind::Global => env.next,
        };
        for _ in 0..slot_count {
            self.asm().pop();
        }
    }

    fn resolve(&mut self, t: Token<'a>) -> Result<Storage, Error> {
        let ent = self
            .env_stack
            .iter_mut()
            .rev()
            .find_map(|env| env.scope.get_mut(t.text))
            .ok_or_else(|| Error {
                position: self.lmap.position(t.from, t.to),
                message: format!("undefined symbol '{}'", t.text),
            })?;
        if !ent.defined {
            let begin = ent.def_begin_pos;
            let end = ent.def_end_pos;
            let def_position = self.lmap.position(begin, end);
            return Err(Error {
                position: self.lmap.position(t.from, t.to),
                message: format!(
                    "variable '{}' declared at {} is not yet defined",
                    t.text, def_position
                ),
            });
        }
        Ok(ent.storage)
    }
}
