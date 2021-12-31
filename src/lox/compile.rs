use crate::inst;
use crate::inst::Assembler;
use crate::lox::syntax::{Decl, Expr, File, Stmt};
use crate::package::{Function, Package};
use crate::pos::{Error, LineMap};

pub fn compile(ast: &File, lmap: &LineMap) -> Result<Package, Error> {
    let mut cmp = Compiler::new(lmap);
    for decl in &ast.decls {
        cmp.compile_decl(decl)?;
    }
    Ok(Package {
        functions: cmp.functions,
    })
}

struct Compiler<'a> {
    lmap: &'a LineMap,
    functions: Vec<Function>,
    env_stack: Vec<Env>,
}

struct Env {
    asm: Assembler,
}

impl<'a> Compiler<'a> {
    fn new(lmap: &'a LineMap) -> Compiler {
        Compiler {
            lmap: lmap,
            functions: Vec::new(),
            env_stack: Vec::new(),
        }
    }

    fn compile_decl(&mut self, decl: &Decl) -> Result<(), Error> {
        match decl {
            Decl::Function { name, body, .. } => {
                self.env_stack.push(Env {
                    asm: Assembler::new(),
                });
                for stmt in &body.stmts {
                    self.compile_stmt(stmt)?;
                }

                self.env().asm.float64(0.);
                self.env().asm.ret();

                let mut env = self.env_stack.pop().unwrap();
                let f = Function {
                    name: String::from(name.text),
                    insts: env.asm.finish(),
                };
                self.functions.push(f);
            }
        }
        Ok(())
    }

    fn compile_stmt(&mut self, stmt: &Stmt) -> Result<(), Error> {
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

    fn compile_expr(&mut self, expr: &Expr) -> Result<(), Error> {
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
        }
        Ok(())
    }

    fn env(&mut self) -> &mut Env {
        self.env_stack.last_mut().unwrap()
    }
}
