use crate::lua::syntax::{Chunk, Expr, LValue, ScopeID, Stmt, VarID, VarUseID};
use crate::lua::token::Token;
use crate::pos::{Error, LineMap, Pos};

use std::collections::HashMap;

/// Contains information about scopes, variable definitions, and variable uses
/// within a chunk.
pub struct ScopeSet<'src> {
    /// Complete list of scopes in a chunk. Indexed by syntax::ScopeID.
    pub scopes: Vec<Scope<'src>>,

    /// Complete list of variables in a chunk. Indexed by syntax::VarID.
    pub vars: Vec<Var>,

    /// Complete list of variable references in a chunk. Indexed by
    /// syntax::VarUseID.
    pub var_uses: Vec<VarUse>,
}

impl<'src> ScopeSet<'src> {
    fn new() -> ScopeSet<'src> {
        ScopeSet {
            scopes: Vec::new(),
            vars: Vec::new(),
            var_uses: Vec::new(),
        }
    }

    fn ensure_scope(&mut self, id: ScopeID) -> &mut Scope<'src> {
        if self.scopes.len() <= id.0 {
            self.scopes.resize_with(id.0 + 1, || Scope {
                kind: ScopeKind::Function,
                vars: HashMap::new(),
                captures: Vec::new(),
                next_slot: 0,
            });
        }
        &mut self.scopes[id.0]
    }

    fn ensure_var(&mut self, id: VarID) -> &mut Var {
        if self.vars.len() <= id.0 {
            self.vars.resize_with(id.0 + 1, || Var {
                kind: VarKind::Local,
                attr: Attr::None,
                slot: 0,
                cell_slot: 0,
                pos: Pos { begin: 0, end: 0 },
            });
        }
        &mut self.vars[id.0]
    }

    fn ensure_var_use(&mut self, id: VarUseID) -> &mut VarUse {
        if self.var_uses.len() <= id.0 {
            self.var_uses.resize_with(id.0 + 1, || VarUse {
                var: None,
                cell: None,
            });
        }
        &mut self.var_uses[id.0]
    }
}

/// Describes the relationship between names and variables within a block.
pub struct Scope<'src> {
    /// Indicates the type of definition this scope belongs to. This affects
    /// storage and capturing.
    pub kind: ScopeKind,

    /// Maps names to variable definitions.
    pub vars: HashMap<&'src str, VarID>,

    /// List of variables defined in an enclosing scope that are captured by
    /// this scope. Captured variables might be referenced in this scope or in
    /// a child scope. Only filled for a scope with kind Function. Used to
    /// construct closures.
    pub captures: Vec<Capture>,

    /// The next available slot number to store a variable. Used to set
    /// Var::slot for new variables.
    next_slot: usize,
}

impl<'src> Scope<'src> {
    fn next_slot(&mut self) -> usize {
        let i = self.next_slot;
        self.next_slot += 1;
        i
    }
}

/// Describes a variable definition and how it's stored in memory.
pub struct Var {
    /// Indicates how the variable is stored. If kind is Parameter, slot is the
    /// index of the parameter. If kind is Local, slot is the index of the local
    /// variable. If kind is Capture, cell_slot is the index of the local slot
    /// containing the pointer to storage. For captured parameters, slot
    /// indicates the parameter that is moved into the cell.
    pub kind: VarKind,

    /// The attribute the variable was declared with, if any.
    pub attr: Attr,

    /// The index of the variable within its storage.
    pub slot: usize,

    /// For captured variables, the index of the local slot containing a pointer
    /// to storage.
    pub cell_slot: usize,

    pub pos: Pos,
}

/// Variable attributes, declared in a local statement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Attr {
    None,

    /// The variable may not be assigned after its declaration.
    Const,

    /// The variable's __close metamethod will be called when it goes out of
    /// scope. Like Const, Close variables may not be assigned.
    /// TODO: implement Close
    Close,
}

impl Attr {
    pub fn is_const(self) -> bool {
        self == Attr::Const || self == Attr::Close
    }
}

/// Describes a reference to a variable.
pub struct VarUse {
    /// The index of the referenced variable, if known. If there's no referenced
    /// variable, the reference is to a field of the global _ENV table.
    pub var: Option<VarID>,

    /// Index of the cell in the closure containing the reference. Only set for
    /// captured variables defined outside the closure containing the reference.
    pub cell: Option<usize>,
}

/// Describes how a closure captures a variable from an enclosing scope.
/// Used to construct the closure.
pub struct Capture {
    /// Index of the captured variable in ScopeSet::vars.
    pub var: VarID,

    /// Where the compiler can find the captured variable.
    pub from: CaptureFrom,
}

/// Where the compiler can find a captured variable when constructing a closure.
pub enum CaptureFrom {
    /// Indicates the captured variable is defined in the function directly
    /// containing the closure. The captured variable is in a local stack slot
    /// indicated by Var::cell_slot.
    Local,

    /// Indicates there are other functions between the defining function and
    /// the capturing closure. The cell comes from the constructing function's
    /// closure object. The value is a cell index into that closure.
    Closure(usize),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum ScopeKind {
    Function,
    Local,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum VarKind {
    Global,
    Parameter,
    Local,
    Capture,
}

pub fn resolve<'src>(
    chunk: &Chunk<'src>,
    lmap: &LineMap,
    errors: &mut Vec<Error>,
) -> ScopeSet<'src> {
    let mut r = Resolver::new(lmap);
    r.resolve_chunk(chunk);
    errors.extend(r.errors);
    r.scope_set
}

struct Resolver<'src, 'lm> {
    lmap: &'lm LineMap,
    scope_set: ScopeSet<'src>,
    scope_stack: Vec<ScopeID>,
    errors: Vec<Error>,
}

impl<'src, 'lm> Resolver<'src, 'lm> {
    fn new(lmap: &'lm LineMap) -> Resolver<'src, 'lm> {
        Resolver {
            lmap,
            scope_set: ScopeSet::new(),
            scope_stack: Vec::new(),
            errors: Vec::new(),
        }
    }

    fn resolve_chunk(&mut self, chunk: &Chunk<'src>) {
        self.enter(chunk.scope, ScopeKind::Local);
        self.declare(
            chunk.env_var,
            "_ENV",
            VarKind::Global,
            Attr::None,
            chunk.pos(),
        );
        for stmt in &chunk.stmts {
            self.resolve_stmt(stmt);
        }
        self.leave();
    }

    fn resolve_stmt(&mut self, stmt: &Stmt<'src>) {
        match stmt {
            Stmt::Empty(_) => (),
            Stmt::Assign { left, right, .. } => {
                for r in right {
                    self.resolve_expr(r);
                }
                for l in left {
                    self.resolve_lvalue(l);
                }
            }
            Stmt::Local { left, right, .. } => {
                for r in right {
                    self.resolve_expr(r);
                }
                let mut close_count = 0;
                for l in left {
                    let attr = match l.attr {
                        None => Attr::None,
                        Some(t) if t.text == "const" => Attr::Const,
                        Some(t) if t.text == "close" => {
                            // TODO: implement close
                            close_count += 1;
                            self.error(t.pos(), format!("close is not implemented yet"));
                            Attr::None
                        }
                        Some(t) => {
                            self.error(t.pos(), format!("unknown attribute: '{}'", t.text));
                            Attr::None
                        }
                    };
                    self.declare(l.var, l.name.text, VarKind::Local, attr, l.pos);
                }
                if close_count > 1 {
                    self.error(
                        stmt.pos(),
                        format!("multiple variables have 'close' attribute"),
                    );
                }
            }
            Stmt::Print { expr, .. } => {
                self.resolve_expr(expr);
            }
        }
    }

    fn resolve_expr(&mut self, expr: &Expr<'src>) {
        match expr {
            Expr::Literal(_) => (),
            Expr::Var { name, var_use, .. } => {
                self.resolve(*name, *var_use);
            }
            Expr::Unary(_, expr) => {
                self.resolve_expr(expr);
            }
            Expr::Binary(left, _, right) => {
                self.resolve_expr(left);
                self.resolve_expr(right);
            }
            Expr::Group { expr, .. } => {
                self.resolve_expr(expr);
            }
        }
    }

    fn resolve_lvalue(&mut self, lvalue: &LValue<'src>) {
        match lvalue {
            LValue::Var {
                name,
                var_use: vuid,
                ..
            } => {
                self.resolve(*name, *vuid);
                let var_use = &self.scope_set.var_uses[vuid.0];
                if let Some(vid) = var_use.var {
                    let var = &self.scope_set.vars[vid.0];
                    if var.attr.is_const() {
                        self.error(
                            lvalue.pos(),
                            format!("attempt to assign to const variable '{}'", name.text),
                        );
                    }
                }
            }
        }
    }

    fn declare(&mut self, vid: VarID, name: &'src str, kind: VarKind, attr: Attr, pos: Pos) {
        let scope = &mut self.scope_set.scopes[self.scope_stack.last().unwrap().0];
        let slot = if kind == VarKind::Global {
            debug_assert_eq!(name, "_ENV");
            0
        } else {
            scope.next_slot()
        };
        let too_many_err = match kind {
            VarKind::Global if slot > u32::MAX as usize => Some("too many global variables"),
            VarKind::Parameter if slot > u16::MAX as usize => Some("too many parameters"),
            VarKind::Local if slot > u16::MAX as usize => Some("too many local variables"),
            _ => None,
        };
        if let Some(msg) = too_many_err {
            self.errors.push(Error {
                position: self.lmap.position(pos),
                message: String::from(msg),
            });
            return;
        }

        scope.vars.insert(name, vid);
        let var = Var {
            kind,
            attr,
            slot,
            cell_slot: 0,
            pos,
        };
        *self.scope_set.ensure_var(vid) = var;
    }

    fn resolve(&mut self, name: Token<'src>, vuid: VarUseID) {
        let mut may_need_capture = false;
        let mut stack_def_index = self.scope_stack.len() - 1;
        loop {
            let sid = self.scope_stack[stack_def_index];
            if let Some(&vid) = self.scope_set.scopes[sid.0].vars.get(name.text) {
                *self.scope_set.ensure_var_use(vuid) = VarUse {
                    var: Some(vid),
                    cell: None,
                };
                if may_need_capture {
                    unimplemented!();
                }
                return;
            }
            if stack_def_index == 0 {
                break;
            }
            if self.scope_set.scopes[sid.0].kind == ScopeKind::Function {
                may_need_capture = true;
            }
            stack_def_index -= 1;
        }
        *self.scope_set.ensure_var_use(vuid) = VarUse {
            var: None,
            cell: None,
        };
    }

    fn enter(&mut self, id: ScopeID, kind: ScopeKind) {
        let next_slot = if let Some(&prev_id) = self.scope_stack.last() {
            let prev = &self.scope_set.scopes[prev_id.0];
            if prev.kind == ScopeKind::Local && kind == ScopeKind::Local {
                prev.next_slot
            } else {
                0
            }
        } else {
            0
        };
        let scope = self.scope_set.ensure_scope(id);
        scope.kind = kind;
        scope.next_slot = next_slot;
        self.scope_stack.push(id);
    }

    fn leave(&mut self) {
        self.scope_stack.pop();
    }
    fn error(&mut self, pos: Pos, message: String) {
        self.errors.push(Error {
            position: self.lmap.position(pos),
            message,
        })
    }
}
