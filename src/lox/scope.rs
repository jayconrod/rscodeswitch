use crate::lox::syntax::{Decl, Expr, ForInit, LValue, Program, Stmt};
use crate::lox::token::Token;
use crate::pos::{Error, LineMap, Pos};

use std::collections::HashMap;

/// ScopeSet contains information about all the scopes, definitions, and uses
/// in a program.
pub struct ScopeSet<'a> {
    /// scopes is the complete list of scopes in a program. It's indexed by
    /// an id assigned by the parser (for example, Decl::Function::body_scope).
    pub scopes: Vec<Scope<'a>>,

    /// vars is the complete list of definitions in the program. It's indexed
    /// by an id assigned by the parser (for example, Decl::Var::var).
    pub vars: Vec<Var>,

    /// var_uses is the complete list of references to variables. It's indexed
    /// by an id assigned by the parser (for example, Expr::Var::var_use).
    /// The elements are indices into vars.
    pub var_uses: Vec<usize>,
}

impl<'a> ScopeSet<'a> {
    fn new() -> ScopeSet<'a> {
        ScopeSet {
            scopes: Vec::new(),
            vars: Vec::new(),
            var_uses: Vec::new(),
        }
    }

    fn ensure_scope(&mut self, scope: usize) -> &mut Scope<'a> {
        if self.scopes.len() <= scope {
            self.scopes.resize_with(scope + 1, Scope::default);
        }
        &mut self.scopes[scope]
    }

    fn ensure_var(&mut self, var: usize) -> &mut Var {
        if self.vars.len() <= var {
            self.vars.resize_with(var + 1, Var::default);
        }
        &mut self.vars[var]
    }

    fn ensure_var_use(&mut self, var_use: usize) -> &mut usize {
        if self.var_uses.len() <= var_use {
            self.var_uses.resize(var_use + 1, !0);
        }
        &mut self.var_uses[var_use]
    }
}

/// Scope describes the relationship between names and variables within a
/// function body, block, or other program scope.
pub struct Scope<'a> {
    /// kind indicates the type of definition this scope belongs to.
    /// This affects variable storage and capturing.
    pub kind: Kind,

    /// vars maps names to indices into the ScopeSet's vars list.
    pub vars: HashMap<&'a str, usize>,

    /// next_slot indicates the next available slot number to store a
    /// variable. This is used to set Var::slot for new variables.
    next_slot: usize,
}

impl<'a> Scope<'a> {
    fn next_slot(&mut self) -> usize {
        let slot = self.next_slot;
        self.next_slot += 1;
        slot
    }
}

impl<'a> Default for Scope<'a> {
    fn default() -> Scope<'a> {
        Scope {
            kind: Kind::Global,
            vars: HashMap::new(),
            next_slot: 0,
        }
    }
}

/// Var describes a variable definition and how it's stored in memory.
pub struct Var {
    /// kind indicates how the variable is stored. If kind is Global,
    /// slot is the index into the package's list of global variables.
    /// If kind is Argument, slot is the index of the argument. If kind is
    /// Local, slot is the index of the local variable.
    pub kind: Kind,

    /// slot indicates the index of the variable within its storage (see kind).
    pub slot: usize,

    pub begin_pos: Pos,
    pub end_pos: Pos,
}

impl Default for Var {
    fn default() -> Var {
        Var {
            kind: Kind::Global,
            slot: !0,
            begin_pos: Pos { offset: !0 },
            end_pos: Pos { offset: !0 },
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum Kind {
    Global,
    Argument,
    Local,
}

pub fn resolve<'a>(prog: &Program<'a>, lmap: &LineMap) -> Result<ScopeSet<'a>, Error> {
    let mut r = Resolver::new(lmap);
    r.resolve_program(prog)?;
    Ok(r.ss)
}

/// Resolver traverses a program's syntax tree and builds a ScopeSet containing
/// the program's scopes, variable definitions, and uses.
struct Resolver<'a, 'b> {
    lmap: &'b LineMap,
    ss: ScopeSet<'a>,
    scope_stack: Vec<usize>,
}

impl<'a, 'b> Resolver<'a, 'b> {
    fn new(lmap: &'b LineMap) -> Resolver<'a, 'b> {
        Resolver {
            lmap,
            ss: ScopeSet::new(),
            scope_stack: Vec::new(),
        }
    }

    fn resolve_program(&mut self, prog: &Program<'a>) -> Result<(), Error> {
        self.enter(prog.scope, Kind::Global);

        // Declare global variables before resolving anything. As a special
        // case, global variables may be used in the file before
        // they're declared.
        for decl in &prog.decls {
            let (begin_pos, end_pos) = decl.pos();
            match decl {
                Decl::Var { name, var, .. } => {
                    self.declare(*var, *name, begin_pos, end_pos)?;
                }
                Decl::Function { name, var, .. } => {
                    self.declare(*var, *name, begin_pos, end_pos)?;
                }
                _ => (),
            };
        }

        for decl in &prog.decls {
            self.resolve_decl(decl)?;
        }

        self.leave();
        Ok(())
    }

    fn resolve_decl(&mut self, decl: &Decl<'a>) -> Result<(), Error> {
        let is_global = self.ss.scopes[*self.scope_stack.last().unwrap()].kind == Kind::Global;
        match decl {
            Decl::Var {
                name, init, var, ..
            } => {
                if let Some(init) = init {
                    self.resolve_expr(init)?;
                }
                if !is_global {
                    let (begin_pos, end_pos) = decl.pos();
                    self.declare(*var, *name, begin_pos, end_pos)?;
                }
                Ok(())
            }
            Decl::Function {
                name,
                params,
                body,
                arg_scope,
                body_scope,
                var,
                ..
            } => {
                if !is_global {
                    let (begin_pos, end_pos) = decl.pos();
                    self.declare(*var, *name, begin_pos, end_pos)?;
                }
                self.enter(*arg_scope, Kind::Argument);
                for param in params {
                    self.declare(param.var, param.name, param.name.from, param.name.to)?;
                }
                self.enter(*body_scope, Kind::Local);
                for decl in &body.decls {
                    self.resolve_decl(decl)?;
                }
                self.leave();
                self.leave();
                Ok(())
            }
            Decl::Stmt(stmt) => self.resolve_stmt(stmt),
        }
    }

    fn resolve_stmt(&mut self, stmt: &Stmt<'a>) -> Result<(), Error> {
        match stmt {
            Stmt::Expr(expr) => self.resolve_expr(expr),
            Stmt::Block(b) => {
                self.enter(b.scope, Kind::Local);
                for decl in &b.decls {
                    self.resolve_decl(decl)?;
                }
                self.leave();
                Ok(())
            }
            Stmt::Print { expr, .. } => self.resolve_expr(expr),
            Stmt::If {
                cond,
                true_stmt,
                false_stmt,
                ..
            } => {
                self.resolve_expr(cond)?;
                self.resolve_stmt(true_stmt)?;
                if let Some(false_stmt) = false_stmt {
                    self.resolve_stmt(false_stmt)?;
                }
                Ok(())
            }
            Stmt::While { cond, body, .. } => {
                self.resolve_expr(cond)?;
                self.resolve_stmt(body)
            }
            Stmt::For {
                init,
                cond,
                incr,
                body,
                scope,
                ..
            } => {
                self.enter(*scope, Kind::Local);
                match init {
                    ForInit::Var(decl) => {
                        self.resolve_decl(decl)?;
                    }
                    ForInit::Expr(expr) => {
                        self.resolve_expr(expr)?;
                    }
                    _ => (),
                };
                if let Some(cond) = cond {
                    self.resolve_expr(cond)?;
                }
                if let Some(incr) = incr {
                    self.resolve_expr(incr)?;
                }
                self.resolve_stmt(body)?;
                self.leave();
                Ok(())
            }
            Stmt::Return { expr, .. } => {
                if let Some(expr) = expr {
                    self.resolve_expr(expr)?;
                }
                Ok(())
            }
        }
    }

    fn resolve_expr(&mut self, expr: &Expr<'a>) -> Result<(), Error> {
        match expr {
            Expr::Var { name, var_use, .. } => self.resolve(*name, *var_use),
            Expr::Group { expr, .. } => self.resolve_expr(expr),
            Expr::Call {
                callee, arguments, ..
            } => {
                self.resolve_expr(callee)?;
                arguments.iter().try_for_each(|arg| self.resolve_expr(arg))
            }
            Expr::Unary(_, expr) => self.resolve_expr(expr),
            Expr::Binary(l, _, r) => {
                self.resolve_expr(l)?;
                self.resolve_expr(r)
            }
            Expr::Assign(l, r) => {
                self.resolve_lvalue(l)?;
                self.resolve_expr(r)
            }
            _ => Ok(()),
        }
    }

    fn resolve_lvalue(&mut self, lvalue: &LValue<'a>) -> Result<(), Error> {
        match lvalue {
            LValue::Var { name, var_use, .. } => self.resolve(*name, *var_use),
        }
    }

    /// enter creates a new scope with the given index and kind and pushes it
    /// onto the scope stack.
    fn enter(&mut self, sid: usize, kind: Kind) {
        let next_slot = if let Some(&prev_sid) = self.scope_stack.last() {
            if self.ss.scopes[prev_sid].kind == Kind::Local && kind == Kind::Local {
                self.ss.scopes[prev_sid].next_slot
            } else {
                0
            }
        } else {
            0
        };
        let scope = self.ss.ensure_scope(sid);
        scope.kind = kind;
        scope.next_slot = next_slot;
        self.scope_stack.push(sid);
    }

    fn leave(&mut self) {
        self.scope_stack.pop();
    }

    /// declare creates a new variable within the scope on top of the
    /// scope stack. declare returns an error if something is already defined
    /// in this scope with the same name.
    fn declare(
        &mut self,
        var_id: usize,
        name: Token<'a>,
        begin_pos: Pos,
        end_pos: Pos,
    ) -> Result<(), Error> {
        let scope = &mut self.ss.scopes[*self.scope_stack.last().unwrap()];
        if let Some(prev) = scope.vars.get(name.text) {
            let prev_var = &self.ss.vars[*prev];
            return Err(Error {
                position: self.lmap.position(name.from, name.to),
                message: format!(
                    "duplicate definition of {}; previous definition at {}",
                    name.text,
                    self.lmap.position(prev_var.begin_pos, prev_var.end_pos)
                ),
            });
        }
        let slot = scope.next_slot();
        let too_many_err = match scope.kind {
            Kind::Global if slot > u32::MAX as usize => Some("too many global variables"),
            Kind::Argument if slot > u16::MAX as usize => Some("too many arguments"),
            Kind::Local if slot > u16::MAX as usize => Some("too many local variables"),
            _ => None,
        };
        if let Some(msg) = too_many_err {
            return Err(Error {
                position: self.lmap.position(name.from, name.to),
                message: String::from(msg),
            });
        }

        scope.vars.insert(name.text, var_id);
        let var = Var {
            kind: scope.kind,
            slot,
            begin_pos,
            end_pos,
        };
        *self.ss.ensure_var(var_id) = var;
        Ok(())
    }

    /// resolve looks up the variable with the given name in the scopes on the
    /// scope stack, then records the variable's index in var_uses. resolve
    /// returns an error if there's no such variable or if it can't be used.
    fn resolve(&mut self, name: Token<'a>, var_use: usize) -> Result<(), Error> {
        let mut i = self.scope_stack.len() - 1;
        loop {
            let scope = &mut self.ss.scopes[self.scope_stack[i]];
            if let Some(var) = scope.vars.get(name.text) {
                *self.ss.ensure_var_use(var_use) = *var;
                return Ok(());
            }
            if i == 0 {
                break;
            }
            i -= 1;
        }
        Err(Error {
            position: self.lmap.position(name.from, name.to),
            message: format!("undefined symbol: {}", name.text),
        })
    }
}
