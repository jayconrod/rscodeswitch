use crate::inst;
use crate::inst::Assembler;
use crate::lox::syntax::{Decl, Expr, File, LValue, Stmt};
use crate::lox::token::Token;
use crate::package::{Function, Global, Package};
use crate::pos::{Error, LineMap, Pos};
use std::collections::HashMap;
use std::mem::swap;

pub fn compile(ast: &File, lmap: &LineMap) -> Result<Box<Package>, Error> {
    let mut cmp = Compiler::new(lmap);
    for decl in &ast.decls {
        cmp.declare(decl)?;
    }
    for decl in &ast.decls {
        cmp.compile_decl(decl)?;
    }
    Ok(cmp.finish())
}

struct Compiler<'a> {
    lmap: &'a LineMap,
    globals: Vec<Global>,
    functions: Vec<Function>,
    env_stack: Vec<Env<'a>>,
}

struct Env<'a> {
    asm: Assembler,
    scope: HashMap<&'a str, ScopeEntry>,
    next: u32,
}

impl<'a> Env<'a> {
    fn new() -> Env<'a> {
        Env {
            asm: Assembler::new(),
            scope: HashMap::new(),
            next: 0,
        }
    }
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
}

impl<'a> Compiler<'a> {
    fn new(lmap: &'a LineMap) -> Compiler {
        Compiler {
            lmap: lmap,
            globals: Vec::new(),
            functions: Vec::new(),
            env_stack: vec![Env::new()],
        }
    }

    fn finish(&mut self) -> Box<Package> {
        self.env().asm.ret();
        let init = Function {
            name: String::from("init"),
            insts: self.env().asm.finish(),
            package: 0 as *mut Package,
        };
        self.functions.push(init);

        let mut package = Box::new(Package {
            globals: Vec::new(),
            functions: Vec::new(),
        });
        for f in &mut self.functions {
            f.package = &*package;
        }
        swap(&mut package.globals, &mut self.globals);
        swap(&mut package.functions, &mut self.functions);
        package
    }

    fn declare(&mut self, decl: &Decl<'a>) -> Result<(), Error> {
        let name = decl.name();
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
        let mut env = self.env();
        env.scope.insert(
            name.text,
            ScopeEntry {
                def_begin_pos: decl.begin_pos(),
                def_end_pos: decl.end_pos(),
                storage: Storage::Global(env.next),
                defined: true,
            },
        );
        env.next += 1;
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
                let mut ent = self.env().scope.get_mut(name.text).unwrap();
                ent.defined = true;
                match ent.storage {
                    Storage::Global(i) => self.env().asm.storeglobal(i),
                }

                self.globals.push(Global {
                    name: String::from(name.text),
                });
            }
            Decl::Function { name, body, .. } => {
                self.env_stack.push(Env::new());
                for stmt in &body.stmts {
                    self.compile_stmt(stmt)?;
                }

                self.env().asm.ret();

                let mut env = self.env_stack.pop().unwrap();
                let f = Function {
                    name: String::from(name.text),
                    insts: env.asm.finish(),
                    package: 0 as *mut Package,
                };
                self.functions.push(f);
            }
        }
        Ok(())
    }

    fn compile_stmt(&mut self, stmt: &Stmt<'a>) -> Result<(), Error> {
        match stmt {
            Stmt::Expr(e) => {
                self.compile_expr(e)?;
                self.env().asm.pop();
            }
            Stmt::Print(e) => {
                self.compile_expr(e)?;
                self.env().asm.sys(inst::SYS_PRINT);
            }
        }
        Ok(())
    }

    fn compile_expr(&mut self, expr: &Expr<'a>) -> Result<(), Error> {
        match expr {
            Expr::Bool(t) => {
                match t.text {
                    "true" => {
                        self.env().asm.true_();
                    }
                    "false" => {
                        self.env().asm.false_();
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
                self.env().asm.float64(n);
                self.env().asm.nanbox();
            }
            Expr::Var(t) => match self.resolve(t)? {
                Storage::Global(i) => {
                    self.env().asm.loadglobal(i);
                }
            },
            Expr::Assign(l, r) => {
                self.compile_expr(r)?;
                match l {
                    LValue::Var(t) => match self.resolve(t)? {
                        Storage::Global(i) => {
                            self.env().asm.storeglobal(i);
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
