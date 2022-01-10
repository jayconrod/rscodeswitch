use crate::lox::syntax::{Block, Decl, Expr, ForInit, LValue, Param, Program, Stmt};
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
    pub var_uses: Vec<VarUse>,
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

    fn ensure_var_use(&mut self, var_use: usize) -> &mut VarUse {
        if self.var_uses.len() <= var_use {
            self.var_uses.resize_with(var_use + 1, VarUse::default);
        }
        &mut self.var_uses[var_use]
    }
}

/// Scope describes the relationship between names and variables within a
/// function body, block, or other program scope.
pub struct Scope<'a> {
    /// kind indicates the type of definition this scope belongs to.
    /// This affects variable storage and capturing.
    pub kind: ScopeKind,

    /// vars maps names to indices into the ScopeSet's vars list.
    pub vars: HashMap<&'a str, usize>,

    /// captures is a list of variables captured by this scope. Only filled for
    /// a scope with kind Function. Used to construct closures.
    pub captures: Vec<Capture>,

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
            kind: ScopeKind::Global,
            vars: HashMap::new(),
            captures: Vec::new(),
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
    pub kind: VarKind,

    /// slot indicates the index of the variable within its storage (see kind).
    pub slot: usize,

    /// cell_slot indicates the index of the local slot containing the cell
    /// for a captured argument. Only set for a variable with kind Capture in
    /// a scope with kind Function.
    pub cell_slot: usize,

    pub begin_pos: Pos,
    pub end_pos: Pos,
}

impl Default for Var {
    fn default() -> Var {
        Var {
            kind: VarKind::Global,
            slot: !0,
            cell_slot: !0,
            begin_pos: Pos { offset: !0 },
            end_pos: Pos { offset: !0 },
        }
    }
}

/// VarUse describes a reference to a variable.
#[derive(Clone, Copy)]
pub struct VarUse {
    /// var is the index of the variable in ScopeSet::vars.
    pub var: usize,

    /// cell is the index of the cell in the closure containing the reference.
    /// Only set for variables with kind Capture.
    pub cell: Option<usize>,
}

/// Capture describes a function capturing a variable from an enclosing
/// function. It is used to construct a closure for the function containing
/// the capture.
#[derive(Clone, Copy)]
pub struct Capture {
    /// var is the index of the captured variable in ScopeSet::vars.
    pub var: usize,

    // from indicates where the compiler can find the captured variable when
    // building the closure.
    pub from: CaptureFrom,
}

/// CaptureFrom indicates where the compiler can find a captured variable
/// when constructing a closure.
#[derive(Clone, Copy)]
pub enum CaptureFrom {
    /// Local indicates the captured variable is in a local stack slot. This is
    /// true when the enclosing function contains the variable definition. The
    /// stack slot is Var::cell_slot.
    Local,

    /// Closure indicates the function constructing the closure is not the
    /// function definining the variable, so the cell must come from the
    /// constructing function's closure. The value is a cell index.
    Closure(usize),
}

impl Default for VarUse {
    fn default() -> VarUse {
        VarUse {
            var: !0,
            cell: None,
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ScopeKind {
    Global,
    Function,
    Local,
}

impl ScopeKind {
    fn var_kind(self) -> VarKind {
        match self {
            ScopeKind::Global => VarKind::Global,
            ScopeKind::Function => VarKind::Argument,
            ScopeKind::Local => VarKind::Local,
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum VarKind {
    Global,
    Argument,
    Local,
    Capture,
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
        self.enter(prog.scope, ScopeKind::Global);

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
        let is_global = self.ss.scopes[*self.scope_stack.last().unwrap()].kind == ScopeKind::Global;
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
                self.enter(*arg_scope, ScopeKind::Function);
                for param in params {
                    self.declare(param.var, param.name, param.name.from, param.name.to)?;
                }
                self.enter(*body_scope, ScopeKind::Local);
                for decl in &body.decls {
                    self.resolve_decl(decl)?;
                }
                self.leave();
                self.leave();
                self.shift_captured_params_in_function(params, body, *body_scope);
                Ok(())
            }
            Decl::Stmt(stmt) => self.resolve_stmt(stmt),
        }
    }

    fn resolve_stmt(&mut self, stmt: &Stmt<'a>) -> Result<(), Error> {
        match stmt {
            Stmt::Expr(expr) => self.resolve_expr(expr),
            Stmt::Block(b) => {
                self.enter(b.scope, ScopeKind::Local);
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
                self.enter(*scope, ScopeKind::Local);
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
    fn enter(&mut self, sid: usize, kind: ScopeKind) {
        let next_slot = if let Some(&prev_sid) = self.scope_stack.last() {
            if self.ss.scopes[prev_sid].kind == ScopeKind::Local && kind == ScopeKind::Local {
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
        let kind = scope.kind.var_kind();
        let too_many_err = match kind {
            VarKind::Global if slot > u32::MAX as usize => Some("too many global variables"),
            VarKind::Argument if slot > u16::MAX as usize => Some("too many arguments"),
            VarKind::Local if slot > u16::MAX as usize => Some("too many local variables"),
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
            kind,
            slot,
            cell_slot: !0,
            begin_pos,
            end_pos,
        };
        *self.ss.ensure_var(var_id) = var;
        Ok(())
    }

    /// resolve looks up the variable with the given name in the scopes on the
    /// scope stack, then records the variable's index in var_uses. If the
    /// variable is not available within the referenced scope, it is captured
    /// (see capture). resolve/ returns an error if there's no such variable or
    /// if it can't be used.
    fn resolve(&mut self, name: Token<'a>, var_use: usize) -> Result<(), Error> {
        let mut may_need_capture = false;
        let mut stack_def_index = self.scope_stack.len() - 1;
        loop {
            let sid = self.scope_stack[stack_def_index];
            if self.ss.scopes[sid].kind == ScopeKind::Global {
                may_need_capture = false;
            }
            if let Some(&var) = self.ss.scopes[sid].vars.get(name.text) {
                *self.ss.ensure_var_use(var_use) = VarUse { var, cell: None };
                if may_need_capture {
                    self.capture(var, var_use, stack_def_index);
                }
                return Ok(());
            }
            if stack_def_index == 0 {
                break;
            }
            if self.ss.scopes[sid].kind == ScopeKind::Function {
                may_need_capture = true;
            }
            stack_def_index -= 1;
        }
        Err(Error {
            position: self.lmap.position(name.from, name.to),
            message: format!("undefined symbol: {}", name.text),
        })
    }

    fn capture(&mut self, var: usize, var_use: usize, stack_def_index: usize) {
        // Mark the variable as captured, if it wasn't captured already.
        // This will cause the compiler to move it into the heap.
        match self.ss.vars[var].kind {
            VarKind::Global => panic!("global variable can't be captured"),
            VarKind::Local | VarKind::Argument => {
                // When a local variable is captured, it uses the same stack
                // slot to hold the cell instead of the variable's value.
                // So we set cell_slot equal to slot.
                //
                // When an argument is captured, we allocate a new local slot
                // and copy the argument into it because we don't want to
                // change the actual type of the argument slot. We're
                // effectively defining a local variable that shadows the
                // argument, and that new local slot needs to be before other
                // local variables, since we won't write to it with storelocal.
                // So we'll need to shift other locals back. That's done in
                // shift_captured_params_in_function.
                self.ss.vars[var].kind = VarKind::Capture;
                self.ss.vars[var].cell_slot = self.ss.vars[var].slot;
            }
            VarKind::Capture => (),
        }

        // Ensure the variable is available in each enclosing function.
        // This causes closures to be allocated with the correct cells.
        let mut capture_from = CaptureFrom::Local;
        for stack_capture_index in stack_def_index + 1..self.scope_stack.len() {
            let scope = &mut self.ss.scopes[self.scope_stack[stack_capture_index]];
            if scope.kind != ScopeKind::Function {
                continue;
            }
            match scope.captures.iter().position(|c| c.var == var) {
                Some(slot) => capture_from = CaptureFrom::Closure(slot),
                None => {
                    let slot = scope.captures.len();
                    scope.captures.push(Capture {
                        var,
                        from: capture_from,
                    });
                    capture_from = CaptureFrom::Closure(slot);
                }
            }
        }

        // Make the reference use the closure's cell.
        let cell = match capture_from {
            CaptureFrom::Local => None,
            CaptureFrom::Closure(cell) => Some(cell),
        };
        self.ss.var_uses[var_use].cell = cell;
    }

    /// shift_captured_params_in_function moves local variables to higher stack
    /// slots to ensure that captured parameters may use the lowest slots for
    /// their cells. We don't reuse the parameter stack slot, since that would
    /// change the type of the slot.
    ///
    /// When a parameter is captured, we allocate a new local slot, then copy
    /// the parameter into it. The sequence looks like this:
    ///
    /// ```csw
    /// alloc n // where n is index of type *Nanbox
    /// dup
    /// loadarg 0
    /// store
    /// // allocated cell address remains on stack
    /// ```
    ///
    /// Since we write to a new local slot on top of the stack and since later
    /// variable definitions do the same (storelocal instruction not used),
    /// we need to ensure the parameter's cell stack slot comes before
    /// other local variable stack slots.
    ///
    /// At the time we're resolving local variables, we don't know how many
    /// parameters will be captured; they might be captured at the end of the
    /// function. So shift_captured_params_in_function is called when we finish
    /// resolving a function. It traverses the function's scopes again
    /// (but not scopes in nested functions) and increments local variable
    /// slots by the number of captured parameters.
    fn shift_captured_params_in_function(
        &mut self,
        params: &Vec<Param<'a>>,
        body: &Block<'a>,
        body_scope: usize,
    ) {
        let param_capture_count = params
            .iter()
            .filter(|p| self.ss.vars[p.var].kind == VarKind::Capture)
            .count();
        self.shift_vars_in_scope(body_scope, param_capture_count);
        for decl in &body.decls {
            self.shift_vars_in_decl(decl, param_capture_count);
        }
    }

    fn shift_vars_in_decl(&mut self, decl: &Decl<'a>, shift: usize) {
        match decl {
            Decl::Stmt(stmt) => self.shift_vars_in_stmt(stmt, shift),
            _ => (),
        }
    }

    fn shift_vars_in_stmt(&mut self, stmt: &Stmt<'a>, shift: usize) {
        match stmt {
            Stmt::Block(block) => {
                self.shift_vars_in_scope(block.scope, shift);
            }
            Stmt::If {
                true_stmt,
                false_stmt,
                ..
            } => {
                self.shift_vars_in_stmt(true_stmt, shift);
                if let Some(false_stmt) = false_stmt {
                    self.shift_vars_in_stmt(false_stmt, shift);
                }
            }
            Stmt::While { body, .. } => {
                self.shift_vars_in_stmt(body, shift);
            }
            Stmt::For { scope, body, .. } => {
                self.shift_vars_in_scope(*scope, shift);
                self.shift_vars_in_stmt(body, shift);
            }
            _ => (),
        }
    }

    fn shift_vars_in_scope(&mut self, sid: usize, shift: usize) {
        for &vid in self.ss.scopes[sid].vars.values() {
            let var = &mut self.ss.vars[vid];
            var.slot += shift;
            if var.kind == VarKind::Capture {
                var.cell_slot += shift;
            }
        }
    }
}
