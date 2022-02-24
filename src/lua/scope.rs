use crate::lua::syntax::{
    Call, Chunk, Expr, LValue, LabelID, LabelUseID, MethodName, Param, ScopeID, Stmt, TableField,
    VarID, VarUseID,
};
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

    /// Complete list of labels in a chunk. Indexed by syntax::LabelID.
    pub labels: Vec<Label>,

    /// Complete list of label references in a chunk. Indexed by
    /// syntax::LabelUseID.
    pub label_uses: Vec<LabelUse>,
}

impl<'src> ScopeSet<'src> {
    fn new() -> ScopeSet<'src> {
        ScopeSet {
            scopes: Vec::new(),
            vars: Vec::new(),
            var_uses: Vec::new(),
            labels: Vec::new(),
            label_uses: Vec::new(),
        }
    }

    fn ensure_scope(&mut self, id: ScopeID) -> &mut Scope<'src> {
        if self.scopes.len() <= id.0 {
            self.scopes.resize_with(id.0 + 1, || Scope {
                kind: ScopeKind::Function,
                vars: Vec::new(),
                bindings: HashMap::new(),
                labels: HashMap::new(),
                break_label: None,
                captures: Vec::new(),
                next_slot: 0,
                slot_count: 0,
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

    fn ensure_label(&mut self, id: LabelID) -> &mut Label {
        if self.labels.len() <= id.0 {
            self.labels.resize_with(id.0 + 1, || Label {
                slot_count: 0,
                pos: Pos { begin: 0, end: 0 },
            })
        }
        &mut self.labels[id.0]
    }

    fn ensure_label_use(&mut self, id: LabelUseID) -> &mut LabelUse {
        if self.label_uses.len() <= id.0 {
            self.label_uses.resize_with(id.0 + 1, || LabelUse {
                label: None,
                slot_count: 0,
            });
        }
        &mut self.label_uses[id.0]
    }
}

/// Describes the relationship between names and variables within a block.
pub struct Scope<'src> {
    /// Indicates the type of definition this scope belongs to. This affects
    /// storage and capturing.
    pub kind: ScopeKind,

    /// All variables defined in the scope, including hidden variables
    /// without bindings.
    pub vars: Vec<VarID>,

    /// Maps variable names to variable definitions.
    pub bindings: HashMap<&'src str, VarID>,

    /// Maps label names to labels.
    pub labels: HashMap<&'src str, LabelID>,

    /// An implicit label for the end of the loop, which may be referenced by
    /// a break statement. Only set for local loop scopes.
    pub break_label: Option<LabelID>,

    /// List of variables defined in an enclosing scope that are captured by
    /// this scope. Captured variables might be referenced in this scope or in
    /// a child scope. Only filled for a scope with kind Function. Used to
    /// construct closures.
    pub captures: Vec<Capture>,

    /// The next available slot number to store a variable. Used to set
    /// Var::slot for new variables.
    next_slot: usize,

    /// Number of slots in this scope. May different from vars.len(),
    /// for example, because there are hidden variables not in vars.
    pub slot_count: usize,
}

impl<'src> Scope<'src> {
    fn next_slot(&mut self) -> usize {
        let i = self.next_slot;
        self.next_slot += 1;
        self.slot_count += 1;
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

/// Describes a declared label, which may be the target of a goto.
pub struct Label {
    // The number of local variables in scope where the label is declared.
    // This count does not include variables in scopes outside the current
    // function, nor does it include parameters.
    pub slot_count: usize,

    pub pos: Pos,
}

/// Describes a reference to a declared label.
pub struct LabelUse {
    /// The referenced label. None if no label with that name was visible.
    pub label: Option<LabelID>,

    /// The number of local variables in scope where the label was referenced.
    /// If this is less than Label::slot_count, it indicates a branch across a
    /// local variable definition, which is an error.
    pub slot_count: usize,
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
    Global,
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
        self.enter(chunk.global_scope, ScopeKind::Global);
        self.declare(
            chunk.env_var,
            "_ENV",
            VarKind::Global,
            Attr::None,
            chunk.pos(),
        );
        self.declare(chunk.g_var, "_G", VarKind::Global, Attr::None, chunk.pos());
        self.enter(chunk.chunk_scope, ScopeKind::Local);
        self.declare_labels(&chunk.stmts);
        for stmt in &chunk.stmts {
            self.resolve_stmt(stmt);
        }
        self.leave();
        self.leave();
    }

    fn declare_break_label(&mut self, lid: LabelID) {
        let scope = &mut self.scope_set.scopes[self.scope_stack.last().unwrap().0];
        let slot_count = scope.next_slot;
        scope.break_label = Some(lid);
        *self.scope_set.ensure_label(lid) = Label {
            slot_count,
            pos: Pos { begin: 0, end: 0 },
        };
    }

    fn declare_labels(&mut self, stmts: &[Stmt<'src>]) {
        let scope_stack_depth = self.scope_stack.len();
        let mut slot_count = if scope_stack_depth >= 2 {
            let parent = &self.scope_set.scopes[self.scope_stack[scope_stack_depth - 2].0];
            if parent.kind == ScopeKind::Local {
                parent.next_slot
            } else {
                0
            }
        } else {
            0
        };

        for stmt in stmts {
            match stmt {
                Stmt::Local { left, .. } => {
                    slot_count += left.len();
                }
                Stmt::Label {
                    name, label, pos, ..
                } => {
                    for sid in self.scope_stack.iter().rev() {
                        let scope = &self.scope_set.scopes[sid.0];
                        if scope.kind != ScopeKind::Local {
                            break;
                        }
                        if let Some(prev_lid) = scope.labels.get(name.text) {
                            let prev_pos = self.scope_set.labels[prev_lid.0].pos;
                            let prev_position = self.lmap.position(prev_pos);
                            self.error(
                                *pos,
                                format!(
                                    "label {} has the same name as another visible label at {}",
                                    name.text, prev_position,
                                ),
                            );
                            break;
                        }
                    }
                    let top_sid = self.scope_stack.last().unwrap();
                    *self.scope_set.ensure_label(*label) = Label {
                        slot_count,
                        pos: *pos,
                    };
                    self.scope_set.scopes[top_sid.0]
                        .labels
                        .insert(name.text, *label);
                }
                _ => (),
            }
        }
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
            Stmt::Do { stmts, scope, .. } => {
                self.enter(*scope, ScopeKind::Local);
                self.declare_labels(stmts);
                for stmt in stmts {
                    self.resolve_stmt(stmt);
                }
                self.leave();
            }
            Stmt::If {
                cond_stmts,
                false_stmt,
                ..
            } => {
                for (cond, stmt) in cond_stmts {
                    self.resolve_expr(cond);
                    self.resolve_stmt(stmt);
                }
                if let Some(false_stmt) = false_stmt {
                    self.resolve_stmt(false_stmt);
                }
            }
            Stmt::While {
                cond,
                body,
                scope,
                break_label,
                ..
            } => {
                self.resolve_expr(cond);
                self.enter(*scope, ScopeKind::Local);
                self.declare_break_label(*break_label);
                self.declare_labels(body);
                for stmt in body {
                    self.resolve_stmt(stmt);
                }
                self.leave();
            }
            Stmt::Repeat {
                body,
                cond,
                scope,
                break_label,
                ..
            } => {
                self.enter(*scope, ScopeKind::Local);
                self.declare_break_label(*break_label);
                self.declare_labels(body);
                for stmt in body {
                    self.resolve_stmt(stmt);
                }
                self.resolve_expr(cond);
                self.leave();
            }
            Stmt::For {
                name,
                init,
                limit,
                step,
                body,
                ind_scope,
                body_scope,
                ind_var,
                limit_var,
                step_var,
                body_var,
                break_label,
                ..
            } => {
                self.resolve_expr(init);
                self.resolve_expr(limit);
                if let Some(step) = step {
                    self.resolve_expr(step);
                }
                self.enter(*ind_scope, ScopeKind::Local);
                self.declare_break_label(*break_label);
                self.declare_hidden(*ind_var, Attr::None);
                self.declare_hidden(*limit_var, Attr::None);
                self.declare_hidden(*step_var, Attr::None);
                self.enter(*body_scope, ScopeKind::Local);
                self.declare(*body_var, name.text, VarKind::Local, Attr::None, name.pos());
                self.declare_labels(body);
                for stmt in body {
                    self.resolve_stmt(stmt);
                }
                self.leave();
                self.leave();
            }
            Stmt::ForIn {
                names,
                exprs,
                body,
                ind_scope,
                body_scope,
                vars,
                iter_var,
                state_var,
                control_var,
                close_var,
                break_label,
                ..
            } => {
                for expr in exprs {
                    self.resolve_expr(expr);
                }
                self.enter(*ind_scope, ScopeKind::Local);
                self.declare_break_label(*break_label);
                self.declare_hidden(*iter_var, Attr::None);
                self.declare_hidden(*state_var, Attr::None);
                self.declare_hidden(*control_var, Attr::None);
                self.declare_hidden(*close_var, Attr::Close);
                self.enter(*body_scope, ScopeKind::Local);
                for (name, var) in names.iter().zip(vars.iter()) {
                    self.declare(*var, name.text, VarKind::Local, Attr::None, name.pos());
                }
                self.declare_labels(body);
                for stmt in body {
                    self.resolve_stmt(stmt);
                }
                self.leave();
                self.leave();
            }
            Stmt::Break { label_use, pos, .. } => self.resolve_break(*label_use, *pos),
            Stmt::Label { .. } => (),
            Stmt::Goto {
                name,
                label_use,
                pos,
                ..
            } => {
                self.resolve_label(*name, *label_use, *pos);
            }
            Stmt::Function {
                name,
                parameters,
                body,
                param_scope,
                body_scope,
                ..
            } => {
                self.resolve(name.name, name.var_use);
                self.resolve_function_parameters_and_body(
                    name.method_name,
                    *param_scope,
                    parameters,
                    *body_scope,
                    body,
                );
            }
            Stmt::LocalFunction {
                name,
                parameters,
                body,
                var,
                param_scope,
                body_scope,
                ..
            } => {
                self.declare(*var, name.text, VarKind::Local, Attr::None, name.pos());
                self.resolve_function_parameters_and_body(
                    None,
                    *param_scope,
                    parameters,
                    *body_scope,
                    body,
                );
            }
            Stmt::Call(Call {
                callee, arguments, ..
            }) => {
                self.resolve_expr(callee);
                for a in arguments {
                    self.resolve_expr(a);
                }
            }
            Stmt::Return { exprs, .. } => {
                for expr in exprs {
                    self.resolve_expr(expr);
                }
            }
        }
    }

    fn resolve_expr(&mut self, expr: &Expr<'src>) {
        match expr {
            Expr::Literal(_) | Expr::VarArgs(_) => (),
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
            Expr::Function {
                parameters,
                body,
                param_scope,
                body_scope,
                ..
            } => {
                self.resolve_function_parameters_and_body(
                    None,
                    *param_scope,
                    parameters,
                    *body_scope,
                    body,
                );
            }
            Expr::Call(Call {
                callee, arguments, ..
            }) => {
                self.resolve_expr(callee);
                for a in arguments {
                    self.resolve_expr(a);
                }
            }
            Expr::Table { fields, .. } => {
                for field in fields {
                    match field {
                        TableField::NameField(_, value) | TableField::CountField(value) => {
                            self.resolve_expr(value)
                        }
                        TableField::ExprField(key, value) => {
                            self.resolve_expr(key);
                            self.resolve_expr(value);
                        }
                    }
                }
            }
            Expr::Dot { expr, .. } => {
                self.resolve_expr(expr);
            }
            Expr::Index { expr, index, .. } => {
                self.resolve_expr(expr);
                self.resolve_expr(index);
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
            LValue::Dot { expr, .. } => self.resolve_expr(expr),
            LValue::Index { expr, index, .. } => {
                self.resolve_expr(expr);
                self.resolve_expr(index);
            }
        }
    }

    fn resolve_function_parameters_and_body(
        &mut self,
        method_name: Option<MethodName<'src>>,
        param_scope: ScopeID,
        parameters: &[Param<'src>],
        body_scope: ScopeID,
        body: &[Stmt<'src>],
    ) {
        self.enter(param_scope, ScopeKind::Function);
        if let Some(m) = method_name {
            self.declare(
                m.receiver_var,
                "self",
                VarKind::Parameter,
                Attr::None,
                m.name.pos(),
            );
        }
        for p in parameters {
            self.declare(
                p.var,
                p.name.text,
                VarKind::Parameter,
                Attr::None,
                p.name.pos(),
            );
        }
        self.enter(body_scope, ScopeKind::Local);
        self.declare_labels(body);
        for stmt in body {
            self.resolve_stmt(stmt);
        }
        self.leave();
        self.leave();
        self.shift_captured_parameters_in_function(parameters, body, body_scope);
    }

    fn declare(&mut self, vid: VarID, name: &'src str, kind: VarKind, attr: Attr, pos: Pos) {
        let scope = &mut self.scope_set.scopes[self.scope_stack.last().unwrap().0];
        let slot = scope.next_slot();
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

        if name != "" {
            scope.bindings.insert(name, vid);
        }
        scope.vars.push(vid);
        let var = Var {
            kind,
            attr,
            slot,
            cell_slot: 0,
            pos,
        };
        *self.scope_set.ensure_var(vid) = var;
    }

    fn declare_hidden(&mut self, vid: VarID, attr: Attr) {
        self.declare(vid, "", VarKind::Local, attr, Pos { begin: 0, end: 0 })
    }

    fn resolve(&mut self, name: Token<'src>, vuid: VarUseID) {
        let mut may_need_capture = false;
        let mut stack_def_index = self.scope_stack.len() - 1;
        loop {
            let sid = self.scope_stack[stack_def_index];
            if let Some(&vid) = self.scope_set.scopes[sid.0].bindings.get(name.text) {
                *self.scope_set.ensure_var_use(vuid) = VarUse {
                    var: Some(vid),
                    cell: None,
                };
                if may_need_capture {
                    self.capture(vid, vuid, stack_def_index);
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

    fn capture(&mut self, vid: VarID, vuid: VarUseID, stack_def_index: usize) {
        // Mark the variable as captured, if it wasn't captured already.
        // This will cause the compiler to allocate a cell for it when
        // it's defined.
        let var = &mut self.scope_set.vars[vid.0];
        match var.kind {
            VarKind::Global => unreachable!(),
            VarKind::Parameter => {
                // When a parameter is captured, we allocate a new local slot
                // and copy the value into it. We don't want to change the
                // actual type of the parameter slot. We're effectively
                // defining a local variable that shadows the parameter.
                // The local slot needs to be before other local variables,
                // since we won't write it with storelocal. So we'll shift
                // other locals to higher stack slots. This is done in
                // shift_captured_params_in_function, which also assigns the
                // captured parameter's cell slot.
                var.kind = VarKind::Capture;
            }
            VarKind::Local => {
                // When a local variable is captured, the compiler uses the
                // same stack slot to hold the cell instead of the variable's
                // value. So we set cell_slot to slot.
                var.kind = VarKind::Capture;
                var.cell_slot = var.slot;
            }
            VarKind::Capture => (),
        }

        // Ensure the captured variable is available in each enclosing function.
        // This ensures closures can be created with cells needed to create
        // nested, capturing closures.
        let mut capture_from = CaptureFrom::Local;
        for stack_capture_index in (stack_def_index + 1)..self.scope_stack.len() {
            let sid = self.scope_stack[stack_capture_index];
            let scope = &mut self.scope_set.scopes[sid.0];
            if scope.kind != ScopeKind::Function {
                continue;
            }
            match scope.captures.iter().position(|c| c.var == vid) {
                Some(slot) => capture_from = CaptureFrom::Closure(slot),
                None => {
                    let slot = scope.captures.len();
                    scope.captures.push(Capture {
                        var: vid,
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
        self.scope_set.var_uses[vuid.0].cell = cell;
    }

    /// Shifts all variables defined within a function body to higher slots,
    /// making room for slots to contain captured parameters.
    fn shift_captured_parameters_in_function(
        &mut self,
        params: &[Param<'src>],
        body: &[Stmt<'src>],
        body_scope: ScopeID,
    ) {
        let param_capture_count = params
            .iter()
            .filter(|p| self.scope_set.vars[p.var.0].kind == VarKind::Capture)
            .count();
        self.shift_vars_in_scope(body_scope, param_capture_count);
        for stmt in body {
            self.shift_vars_in_stmt(stmt, param_capture_count);
        }
        let mut cell_slot = 0;
        for p in params {
            let var = &mut self.scope_set.vars[p.var.0];
            if var.kind == VarKind::Capture {
                var.cell_slot = cell_slot;
                cell_slot += 1;
            }
        }
    }

    fn shift_vars_in_scope(&mut self, sid: ScopeID, shift: usize) {
        for vid in &self.scope_set.scopes[sid.0].vars {
            let var = &mut self.scope_set.vars[vid.0];
            var.slot += shift;
            if var.kind == VarKind::Capture {
                var.cell_slot += shift;
            }
        }
    }

    fn shift_vars_in_stmt(&mut self, stmt: &Stmt<'src>, shift: usize) {
        match stmt {
            Stmt::Empty(_)
            | Stmt::Assign { .. }
            | Stmt::Local { .. }
            | Stmt::Break { .. }
            | Stmt::Label { .. }
            | Stmt::Goto { .. }
            | Stmt::Function { .. }
            | Stmt::LocalFunction { .. }
            | Stmt::Call(_)
            | Stmt::Return { .. } => (),
            Stmt::Do { scope, stmts, .. } => {
                self.shift_vars_in_scope(*scope, shift);
                for stmt in stmts {
                    self.shift_vars_in_stmt(stmt, shift);
                }
            }
            Stmt::If {
                cond_stmts,
                false_stmt,
                ..
            } => {
                for (_, stmt) in cond_stmts {
                    self.shift_vars_in_stmt(stmt, shift);
                }
                if let Some(false_stmt) = false_stmt {
                    self.shift_vars_in_stmt(false_stmt, shift);
                }
            }
            Stmt::While { body, scope, .. } | Stmt::Repeat { body, scope, .. } => {
                self.shift_vars_in_scope(*scope, shift);
                for stmt in body {
                    self.shift_vars_in_stmt(stmt, shift);
                }
            }
            Stmt::For {
                body,
                ind_scope,
                body_scope,
                ..
            } => {
                self.shift_vars_in_scope(*ind_scope, shift);
                self.shift_vars_in_scope(*body_scope, shift);
                for stmt in body {
                    self.shift_vars_in_stmt(stmt, shift);
                }
            }
            Stmt::ForIn {
                body,
                ind_scope,
                body_scope,
                ..
            } => {
                self.shift_vars_in_scope(*ind_scope, shift);
                self.shift_vars_in_scope(*body_scope, shift);
                for stmt in body {
                    self.shift_vars_in_stmt(stmt, shift);
                }
            }
        }
    }

    fn resolve_label(&mut self, name: Token<'src>, luid: LabelUseID, pos: Pos) {
        let slot_count = if self.top().kind == ScopeKind::Local {
            self.top().next_slot
        } else {
            0
        };
        let mut stack_def_index = self.scope_stack.len() - 1;
        loop {
            let sid = self.scope_stack[stack_def_index];
            let scope = &self.scope_set.scopes[sid.0];
            if scope.kind != ScopeKind::Local {
                break;
            }
            if let Some(&lid) = scope.labels.get(name.text) {
                let label = &self.scope_set.labels[lid.0];
                if label.slot_count > slot_count {
                    self.error(
                        pos,
                        format!(
                            "cannot jump to label '{}' across local variable declaration",
                            name.text
                        ),
                    )
                }
                *self.scope_set.ensure_label_use(luid) = LabelUse {
                    label: Some(lid),
                    slot_count,
                };
                return;
            }
            if stack_def_index == 0 {
                break;
            }
            stack_def_index -= 1;
        }
        self.error(pos, format!("undefined label: '{}'", name.text));
        *self.scope_set.ensure_label_use(luid) = LabelUse {
            label: None,
            slot_count,
        };
    }

    fn resolve_break(&mut self, luid: LabelUseID, pos: Pos) {
        let slot_count = if self.top().kind == ScopeKind::Local {
            self.top().next_slot
        } else {
            0
        };
        let mut stack_def_index = self.scope_stack.len() - 1;
        loop {
            let sid = self.scope_stack[stack_def_index];
            let scope = &self.scope_set.scopes[sid.0];
            if scope.kind != ScopeKind::Local {
                break;
            }
            if let Some(break_label) = scope.break_label {
                *self.scope_set.ensure_label_use(luid) = LabelUse {
                    label: Some(break_label),
                    slot_count,
                };
                return;
            }
            if stack_def_index == 0 {
                break;
            }
            stack_def_index -= 1;
        }
        self.error(pos, format!("break statement used outside of loop"));
        *self.scope_set.ensure_label_use(luid) = LabelUse {
            label: None,
            slot_count,
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

    fn top(&mut self) -> &Scope {
        &self.scope_set.scopes[self.scope_stack.last().unwrap().0]
    }

    fn error(&mut self, pos: Pos, message: String) {
        self.errors.push(Error {
            position: self.lmap.position(pos),
            message,
        })
    }
}
