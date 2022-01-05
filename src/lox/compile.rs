use crate::data::{self, List, SetValue};
use crate::heap::Handle;
use crate::inst::{self, Assembler, Label};
use crate::lox::syntax::{Block, Decl, Expr, File, LValue, Stmt};
use crate::lox::token::{Token, Type};
use crate::package::{Function, Global, Package};
use crate::pos::{Error, LineMap, Pos};
use std::collections::HashMap;
use std::mem;

pub fn compile(ast: &File, lmap: &LineMap) -> Result<Box<Package>, Error> {
    let mut cmp = Compiler::new(lmap);
    for decl in &ast.decls {
        cmp.declare(decl)?;
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
        self.asm().ret();
        let init_insts = self.asm().finish().map_err(|err| {
            let position = self.lmap.first_file();
            Error::wrap(position, &err)
        })?;
        let init = Function {
            name: String::from("init"),
            insts: init_insts,
            package: 0 as *mut Package,
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

    fn declare(&mut self, decl: &Decl<'a>) -> Result<(), Error> {
        let name = match decl.name() {
            Some(t) => t,
            None => return Ok(()),
        };
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
        let (def_begin_pos, def_end_pos) = decl.pos();
        let storage = match self.env().kind {
            EnvKind::Global => Storage::Global(self.env().next),
            EnvKind::Function | EnvKind::Block => {
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
                def_begin_pos,
                def_end_pos,
                storage,
                defined: true,
            },
        );
        self.env().next += 1;
        Ok(())
    }

    fn compile_decl(&mut self, decl: &Decl<'a>) -> Result<(), Error> {
        match decl {
            Decl::Var { name, init, .. } => {
                if let Some(e) = init {
                    self.compile_expr(e)?;
                } else {
                    // TODO: nil
                    unimplemented!();
                }
                if self.env().kind != EnvKind::Global {
                    // Globals must be declared before anything is compiled.
                    // Everything else gets declared here.
                    self.declare(decl)?;
                }
                let mut ent = self.env().scope.get_mut(name.text).unwrap();
                ent.defined = true;
                match ent.storage {
                    Storage::Global(i) => {
                        self.asm().storeglobal(i);
                        self.globals.push(Global {
                            name: String::from(name.text),
                        });
                    }
                    Storage::Local(_) => {
                        // Skip the storelocal instruction. We should be storing
                        // into the last slot, and there should be no other
                        // temporaries, so storelocal would be a no-op.
                    }
                }
            }
            Decl::Function { name, body, .. } => {
                self.env_stack.push(Env::new(EnvKind::Function));
                for decl in &body.decls {
                    self.compile_decl(decl)?;
                }
                self.asm().ret();

                let mut env = self.env_stack.pop().unwrap();
                let insts = env.asm.finish().map_err(|err| {
                    let (from, to) = decl.pos();
                    Error::wrap(self.lmap.position(from, to), &err)
                })?;
                let f = Function {
                    name: String::from(name.text),
                    insts,
                    package: 0 as *mut Package,
                };
                self.functions.push(f);
            }
            Decl::Stmt(stmt) => self.compile_stmt(stmt)?,
        }
        Ok(())
    }

    fn compile_block(&mut self, block: &Block<'a>) -> Result<(), Error> {
        let next = self.env().next;
        self.env_stack.push(Env::new(EnvKind::Block));
        self.env().next = next;
        for decl in &block.decls {
            self.compile_decl(decl)?;
        }
        let delta = self.env().next - next;
        self.env_stack.pop();
        for _ in 0..delta {
            self.asm().pop();
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
                self.compile_block(b)?;
            }
            Stmt::Print { expr, .. } => {
                self.compile_expr(expr)?;
                self.asm().sys(inst::SYS_PRINT);
            }
            Stmt::If {
                cond,
                true_block,
                false_block,
                ..
            } => {
                self.compile_expr(cond)?;
                match false_block {
                    None => {
                        self.asm().not();
                        let mut after_label = Label::new();
                        self.asm().bif(&mut after_label);
                        self.compile_block(true_block)?;
                        self.asm().bind(&mut after_label);
                    }
                    Some(b) => {
                        let mut true_label = Label::new();
                        let mut after_label = Label::new();
                        self.asm().bif(&mut true_label);
                        self.compile_block(b)?;
                        self.asm().b(&mut after_label);
                        self.asm().bind(&mut true_label);
                        self.compile_block(true_block)?;
                        self.asm().bind(&mut after_label);
                    }
                }
            }
        }
        Ok(())
    }

    fn compile_expr(&mut self, expr: &Expr<'a>) -> Result<(), Error> {
        match expr {
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
            Expr::Var(t) => match self.resolve(t)? {
                Storage::Global(i) => {
                    self.asm().loadglobal(i);
                }
                Storage::Local(i) => {
                    self.asm().loadlocal(i);
                }
            },
            Expr::Group { expr, .. } => {
                self.compile_expr(expr)?;
            }
            Expr::Unary(op, e) => {
                self.compile_expr(e)?;
                match op.type_ {
                    Type::Minus => self.asm().neg(),
                    Type::Bang => self.asm().not(),
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
                    Type::Eq => self.asm().eq(),
                    Type::Ne => self.asm().ne(),
                    Type::Lt => self.asm().lt(),
                    Type::Le => self.asm().le(),
                    Type::Gt => self.asm().gt(),
                    Type::Ge => self.asm().ge(),
                    Type::Plus => self.asm().add(),
                    Type::Minus => self.asm().sub(),
                    Type::Star => self.asm().mul(),
                    Type::Slash => self.asm().div(),
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
                match l {
                    LValue::Var(t) => match self.resolve(t)? {
                        Storage::Global(i) => {
                            self.asm().dup();
                            self.asm().storeglobal(i);
                        }
                        Storage::Local(i) => {
                            self.asm().dup();
                            self.asm().storelocal(i);
                        }
                    },
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

    fn resolve(&mut self, t: &Token<'a>) -> Result<Storage, Error> {
        let ent = self
            .env_stack
            .iter()
            .rev()
            .find_map(|env| env.scope.get(t.text))
            .ok_or_else(|| Error {
                position: self.lmap.position(t.from, t.to),
                message: format!("undefined variable '{}'", t.text),
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
