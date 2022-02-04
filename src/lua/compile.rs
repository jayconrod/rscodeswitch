use crate::data::{self, List, SetValue, Slice};
use crate::heap::Handle;
use crate::inst::{self, Assembler, Label};
use crate::lua::scope::{self, ScopeSet, Var, VarKind, VarUse};
use crate::lua::syntax::{self, Chunk, Expr, LValue, LabelID, ScopeID, Stmt};
use crate::lua::token::{self, Number, Token};
use crate::nanbox;
use crate::package::{Function, Global, Object, Package};
use crate::pos::{Error, ErrorList, LineMap, PackageLineMap, Pos, Position};

use std::fs;
use std::mem;
use std::path::Path;

pub fn compile_file(path: &Path) -> Result<Box<Package>, ErrorList> {
    let data = fs::read(path).map_err(|err| {
        let position = Position::from(path);
        let wrapped = Error::wrap(position, &err);
        ErrorList(vec![wrapped])
    })?;
    let mut lmap = LineMap::new();
    let mut errors = Vec::new();
    let tokens = token::lex(path, &data, &mut lmap, &mut errors);
    let chunk = syntax::parse(&tokens, &lmap, &mut errors);
    let scope_set = scope::resolve(&chunk, &lmap, &mut errors);
    if let Some(package) = compile_chunk(&chunk, &scope_set, &lmap, &mut errors) {
        Ok(package)
    } else {
        errors.sort_by(|l, r| l.position.cmp(&r.position));
        Err(ErrorList(errors))
    }
}

pub fn compile_chunk(
    chunk: &Chunk,
    scope_set: &ScopeSet,
    lmap: &LineMap,
    errors: &mut Vec<Error>,
) -> Option<Box<Package>> {
    let mut cmp = Compiler::new(scope_set, lmap, errors);
    cmp.compile_chunk(chunk);
    cmp.finish()
}

struct Compiler<'src, 'ss, 'lm, 'err> {
    scope_set: &'ss ScopeSet<'src>,
    lmap: &'lm LineMap,
    globals: Vec<Global>,
    functions: Vec<Function>,
    strings: Handle<List<data::String>>,
    string_index: Handle<data::HashMap<data::String, SetValue<u32>>>,
    named_labels: Vec<inst::Label>,
    asm_stack: Vec<Assembler>,
    errors: &'err mut Vec<Error>,
}

impl<'src, 'ss, 'lm, 'err> Compiler<'src, 'ss, 'lm, 'err> {
    fn new(
        scope_set: &'ss ScopeSet<'src>,
        lmap: &'lm LineMap,
        errors: &'err mut Vec<Error>,
    ) -> Compiler<'src, 'ss, 'lm, 'err> {
        Compiler {
            scope_set,
            lmap,
            globals: Vec::new(),
            functions: Vec::new(),
            strings: Handle::new(List::alloc()),
            string_index: Handle::new(data::HashMap::alloc()),
            named_labels: Vec::new(),
            asm_stack: vec![Assembler::new()],
            errors,
        }
    }

    fn finish(mut self) -> Option<Box<Package>> {
        self.asm().constzero();
        self.asm().mode(inst::MODE_PTR);
        self.asm().nanbox();
        self.asm().ret();
        match self.asm_stack.pop().unwrap().finish() {
            Ok((insts, line_map)) => {
                self.functions.push(Function {
                    name: String::from("·init"),
                    insts,
                    package: 0 as *mut Package,
                    param_types: Vec::new(),
                    cell_types: Vec::new(),
                    line_map,
                });
            }
            Err(err) => {
                self.errors.push(Error::wrap(self.lmap.first_file(), &err));
            }
        }

        if !self.errors.is_empty() {
            return None;
        }

        let mut package = Box::new(Package {
            globals: self.globals,
            functions: Vec::new(),
            strings: Handle::empty(),
            line_map: PackageLineMap::from(self.lmap),
        });
        for f in &mut self.functions {
            f.package = &*package;
        }
        package.functions = self.functions;
        package.strings = Handle::new(Slice::alloc());
        package.strings.init_from_list(&self.strings);
        Some(package)
    }

    fn compile_chunk(&mut self, chunk: &Chunk<'src>) {
        // Create the global object.
        let env_var = &self.scope_set.vars[chunk.env_var.0];
        assert_eq!(env_var.slot, 0);
        self.globals.push(Global {
            name: String::from("_ENV"),
        });
        let object_size = mem::size_of::<Object>() as u32;
        self.asm().alloc(object_size);
        self.asm().mode(inst::MODE_OBJECT);
        self.asm().nanbox();
        self.asm().storeglobal(env_var.slot as u32);

        // Compile statements.
        for stmt in &chunk.stmts {
            self.compile_stmt(stmt);
        }
    }

    fn compile_stmt(&mut self, stmt: &Stmt<'src>) {
        self.line(stmt.pos());
        match stmt {
            Stmt::Empty(_) => (),
            Stmt::Assign { left, right, .. } => {
                // Compile expressions on the left before the right, but don't
                // assign anything yet. The reference doesn't say anything about
                // the order these should be evaluated, but the main Lua
                // interpreter goes left to right.
                for l in left {
                    self.compile_lvalue(l);
                }
                for r in right {
                    self.compile_expr(r);
                }

                // If there are extra expressions on the right, drop them.
                // If there aren't enough, add nils.
                // TODO: if the last expression in an assignment is a function
                // call, append all the returned values to the list of values
                // being assigned before this adjustment.
                if left.len() < right.len() {
                    for _ in 0..right.len() - left.len() {
                        self.asm().pop();
                    }
                } else {
                    for _ in 0..left.len() - right.len() {
                        self.asm().constzero();
                        self.asm().mode(inst::MODE_PTR);
                        self.asm().nanbox();
                    }
                }

                // Perform the actual assignment, right to left.
                // Again, the reference doesn't say what should happen here if
                // the same location is assigned multiple times. This is what
                // the main Lua interpreter does.
                for l in left.iter().rev() {
                    self.compile_assign(l);
                }
            }
            Stmt::Local { left, right, .. } => {
                // Compile and assign each expression that has a corresponding
                // variable.
                for (l, r) in left.iter().zip(right.iter()) {
                    let var = &self.scope_set.vars[l.var.0];
                    self.compile_define_prepare(var);
                    self.compile_expr(r);
                    self.compile_define(var);
                }

                // If there are extra variables, assign nil.
                // If there are extra expressions, compile and pop them.
                if left.len() > right.len() {
                    for l in left.iter().skip(right.len()) {
                        let var = &self.scope_set.vars[l.var.0];
                        self.compile_define_prepare(var);
                        self.asm().constzero();
                        self.asm().mode(inst::MODE_PTR);
                        self.asm().nanbox();
                        self.compile_define(var);
                    }
                } else if left.len() < right.len() {
                    for r in right.iter().skip(left.len()) {
                        self.compile_expr(r);
                        self.asm().pop();
                    }
                }
            }
            Stmt::Do { stmts, scope, .. } => {
                for stmt in stmts {
                    self.compile_stmt(stmt);
                }
                self.pop_block(*scope);
            }
            Stmt::If {
                cond_stmts,
                false_stmt,
                ..
            } => {
                let mut end_label = Label::new();
                for (cond, stmt) in cond_stmts {
                    let mut next_label = Label::new();
                    self.compile_expr(cond);
                    self.asm().mode(inst::MODE_LUA);
                    self.asm().not();
                    self.asm().mode(inst::MODE_LUA);
                    self.asm().bif(&mut next_label);
                    self.compile_stmt(stmt);
                    self.asm().b(&mut end_label);
                    self.asm().bind(&mut next_label);
                }
                if let Some(false_stmt) = false_stmt {
                    self.compile_stmt(false_stmt);
                }
                self.asm().bind(&mut end_label);
            }
            Stmt::While {
                cond,
                body,
                break_label: break_lid,
                scope,
                ..
            } => {
                let mut cond_label = Label::new();
                let mut body_label = Label::new();
                self.asm().b(&mut cond_label);
                self.asm().bind(&mut body_label);
                for stmt in body {
                    self.compile_stmt(stmt);
                }
                self.pop_block(*scope);
                self.asm().bind(&mut cond_label);
                self.compile_expr(cond);
                self.asm().mode(inst::MODE_LUA);
                self.asm().bif(&mut body_label);
                self.bind_named_label(*break_lid);
            }
            Stmt::Repeat {
                body,
                cond,
                break_label: break_lid,
                scope,
                ..
            } => {
                let mut body_label = Label::new();
                self.asm().bind(&mut body_label);
                for stmt in body {
                    self.compile_stmt(stmt);
                }
                self.compile_expr(cond);
                self.asm().mode(inst::MODE_LUA);
                self.asm().not();
                let slot_count = self.scope_set.scopes[scope.0].slot_count;
                for _ in 0..slot_count {
                    self.asm().swap();
                    self.asm().pop();
                }
                self.asm().mode(inst::MODE_LUA);
                self.asm().bif(&mut body_label);
                self.bind_named_label(*break_lid);
            }
            Stmt::For {
                init,
                limit,
                step,
                body,
                ind_scope,
                body_scope,
                ind_var: ind_vid,
                limit_var: limit_vid,
                step_var: step_vid,
                body_var: body_vid,
                break_label: break_lid,
                ..
            } => {
                let ind_var = &self.scope_set.vars[ind_vid.0];
                let limit_var = &self.scope_set.vars[limit_vid.0];
                let step_var = &self.scope_set.vars[step_vid.0];
                let body_var = &self.scope_set.vars[body_vid.0];
                let mut body_label = Label::new();
                let mut cond_label = Label::new();

                // Evaluate the init, limit, and step expressions.
                // Check that step is a non-negative number.
                // Assign to hidden variables.
                self.compile_define_prepare(ind_var);
                self.compile_expr(init);
                self.compile_define(ind_var);
                self.compile_define_prepare(limit_var);
                self.compile_expr(limit);
                self.compile_define(limit_var);
                self.compile_define_prepare(step_var);
                match step {
                    Some(step) => {
                        let mut step_ok_label = Label::new();
                        self.compile_expr(step);
                        self.asm().dup();
                        self.asm().const_(0);
                        self.asm().nanbox();
                        self.asm().ne();
                        self.asm().bif(&mut step_ok_label);
                        let si = self.ensure_string(b"'for' step is zero", step.pos());
                        self.asm().string(si);
                        self.asm().mode(inst::MODE_STRING);
                        self.asm().panic();
                        self.asm().bind(&mut step_ok_label);
                    }
                    None => {
                        self.asm().const_(1);
                        self.asm().nanbox();
                    }
                }
                self.compile_define(step_var);

                // If either initial value or step are not integers, attempt
                // to convert both to float.
                let mut ind_is_int_label = Label::new();
                let mut ind_and_step_are_int_label = Label::new();
                let mut convert_float_label = Label::new();
                let mut check_limit_label = Label::new();
                let mut limit_ok_label = Label::new();
                self.line(init.pos());
                self.compile_load_var(ind_var);
                self.asm().mode(inst::MODE_LUA);
                self.asm().typeof_();
                self.asm().dup();
                self.asm().const_(nanbox::TAG_SMALL_INT);
                self.asm().eq();
                self.asm().bif(&mut ind_is_int_label);
                self.asm().dup();
                self.asm().const_(nanbox::TAG_BIG_INT);
                self.asm().ne();
                self.asm().bif(&mut convert_float_label);

                self.asm().bind(&mut ind_is_int_label);
                if let Some(step) = step {
                    self.line(step.pos());
                    self.asm().pop(); // type of ind
                    self.compile_load_var(step_var);
                    self.asm().mode(inst::MODE_LUA);
                    self.asm().typeof_();
                    self.asm().dup();
                    self.asm().const_(nanbox::TAG_SMALL_INT);
                    self.asm().eq();
                    self.asm().bif(&mut ind_and_step_are_int_label);
                    self.asm().dup();
                    self.asm().const_(nanbox::TAG_BIG_INT);
                    self.asm().ne();
                    self.asm().bif(&mut convert_float_label);
                    // TODO: panic on zero step
                }

                self.asm().bind(&mut ind_and_step_are_int_label);
                self.asm().pop(); // type of step or ind
                self.asm().b(&mut check_limit_label);

                self.line(init.pos());
                self.asm().bind(&mut convert_float_label);
                self.asm().pop(); // type of step or ind
                self.compile_store_var_prepare(ind_var);
                self.compile_load_var(ind_var);
                self.asm().mode(inst::MODE_LUA);
                self.asm().tofloat();
                self.asm().mode(inst::MODE_F64);
                self.asm().nanbox();
                self.compile_store_var(ind_var);
                self.compile_store_var_prepare(step_var);
                self.compile_load_var(step_var);
                self.asm().mode(inst::MODE_LUA);
                self.asm().tofloat();
                self.asm().mode(inst::MODE_F64);
                self.asm().nanbox();
                self.compile_store_var(step_var);

                // Also check that limit is a number. We don't convert it
                // to a float if init and step were floats though.
                self.asm().bind(&mut check_limit_label);
                self.compile_load_var(limit_var);
                self.asm().mode(inst::MODE_LUA);
                self.asm().typeof_();
                self.asm().dup();
                self.asm().const_(nanbox::TAG_SMALL_INT);
                self.asm().eq();
                self.asm().bif(&mut limit_ok_label);
                self.asm().dup();
                self.asm().const_(nanbox::TAG_BIG_INT);
                self.asm().eq();
                self.asm().bif(&mut limit_ok_label);
                self.asm().dup();
                self.asm().const_(nanbox::TAG_FLOAT);
                self.asm().eq();
                self.asm().bif(&mut limit_ok_label);
                let si = self.ensure_string(b"'for' limit is not a number", limit.pos());
                self.asm().string(si);
                self.asm().mode(inst::MODE_STRING);
                self.asm().panic();
                self.asm().bind(&mut limit_ok_label);
                self.asm().pop(); // typeof limit
                self.asm().b(&mut cond_label);

                // Compile the loop body. The condition is checked at the
                // bottom, so the body comes first. We copy the hidden induction
                // variable to the visible variable first.
                self.asm().bind(&mut body_label);
                self.compile_define_prepare(body_var);
                self.compile_load_var(ind_var);
                self.compile_define(body_var);
                for stmt in body {
                    self.compile_stmt(stmt);
                }
                self.pop_block(*body_scope);

                // Increment the induction variable by step.
                // If step is an integer, check that the induction variable
                // did not overflow to float. That should terminate the loop.
                let mut step_inc_ok_label = Label::new();
                self.line(init.pos());
                self.compile_store_var_prepare(ind_var);
                self.compile_load_var(ind_var);
                self.compile_load_var(step_var);
                self.asm().mode(inst::MODE_LUA);
                self.asm().add();
                self.compile_load_var(step_var);
                self.asm().mode(inst::MODE_LUA);
                self.asm().typeof_();
                self.asm().const_(nanbox::TAG_FLOAT);
                self.asm().eq();
                self.asm().bif(&mut step_inc_ok_label);
                self.asm().dup();
                self.asm().mode(inst::MODE_LUA);
                self.asm().typeof_();
                self.asm().const_(nanbox::TAG_FLOAT);
                self.asm().ne();
                self.asm().bif(&mut step_inc_ok_label);
                self.asm().pop();
                self.b_named_label(*break_lid);
                self.asm().bind(&mut step_inc_ok_label);
                self.compile_store_var(ind_var);

                // Check the condition.
                // If step is positive, we check ind <= limit.
                // Otherwise, we check ind >= limit.
                let mut negative_cond_label = Label::new();
                self.line(limit.pos());
                self.asm().bind(&mut cond_label);
                self.compile_load_var(ind_var);
                self.compile_load_var(limit_var);
                self.compile_load_var(step_var);
                self.asm().constzero();
                self.asm().nanbox();
                self.asm().mode(inst::MODE_LUA);
                self.asm().lt();
                self.asm().mode(inst::MODE_LUA);
                self.asm().bif(&mut negative_cond_label);
                self.asm().mode(inst::MODE_LUA);
                self.asm().le();
                self.asm().mode(inst::MODE_LUA);
                self.asm().bif(&mut body_label);
                self.b_named_label(*break_lid);
                self.asm().bind(&mut negative_cond_label);
                self.asm().mode(inst::MODE_LUA);
                self.asm().ge();
                self.asm().mode(inst::MODE_LUA);
                self.asm().bif(&mut body_label);

                // End of the loop.
                self.bind_named_label(*break_lid);
                self.pop_block(*ind_scope);
            }
            Stmt::Break {
                label_use: luid, ..
            } => {
                let label_use = &self.scope_set.label_uses[luid.0];
                if let Some(lid) = label_use.label {
                    let label = &self.scope_set.labels[lid.0];
                    for _ in 0..(label_use.slot_count - label.slot_count) {
                        self.asm().pop();
                    }
                    self.ensure_label(lid);
                    let last_asm_index = self.asm_stack.len() - 1;
                    self.asm_stack[last_asm_index].b(&mut self.named_labels[lid.0]);
                }
            }
            Stmt::Label { label: lid, .. } => {
                self.bind_named_label(*lid);
            }
            Stmt::Goto {
                label_use: luid, ..
            } => {
                let label_use = &self.scope_set.label_uses[luid.0];
                if let Some(lid) = label_use.label {
                    let label = &self.scope_set.labels[lid.0];
                    if label.slot_count < label_use.slot_count {
                        for _ in 0..(label_use.slot_count - label.slot_count) {
                            self.asm().pop();
                        }
                    }
                    self.ensure_label(lid);
                    let last_asm_index = self.asm_stack.len() - 1;
                    self.asm_stack[last_asm_index].b(&mut self.named_labels[lid.0]);
                }
            }
            Stmt::Print { expr, .. } => {
                self.compile_expr(expr);
                self.asm().mode(inst::MODE_LUA);
                self.asm().sys(inst::SYS_PRINT);
            }
        }
    }

    fn compile_expr(&mut self, expr: &Expr<'src>) {
        self.line(expr.pos());
        match expr {
            Expr::Literal(t) => {
                match t.kind {
                    token::Kind::Nil => {
                        self.asm().constzero();
                        self.asm().mode(inst::MODE_PTR);
                    }
                    token::Kind::True => {
                        self.asm().const_(1);
                        self.asm().mode(inst::MODE_BOOL);
                    }
                    token::Kind::False => {
                        self.asm().constzero();
                        self.asm().mode(inst::MODE_BOOL);
                    }
                    token::Kind::Number => match token::convert_number(t.text) {
                        Number::Int(n) if n == 0 => {
                            self.asm().constzero();
                        }
                        Number::Int(n) => {
                            self.asm().const_(n as u64);
                        }
                        Number::Float(n) => {
                            self.asm().const_(n.to_bits());
                            self.asm().mode(inst::MODE_F64);
                        }
                        Number::Malformed => {
                            self.error(t.pos(), format!("malformed number"));
                        }
                    },
                    token::Kind::String => {
                        let s = match token::unquote_string(t.text) {
                            Some(s) => s,
                            None => {
                                self.error(t.pos(), format!("malformed string"));
                                return;
                            }
                        };
                        let si = self.ensure_string(&s, t.pos());
                        self.asm().string(si);
                        self.asm().mode(inst::MODE_STRING);
                    }
                    _ => unreachable!(),
                }
                self.asm().nanbox();
            }
            Expr::Var {
                name,
                var_use: vuid,
                ..
            } => {
                self.compile_var_use(name, &self.scope_set.var_uses[vuid.0]);
            }
            Expr::Unary(op, expr) => {
                self.compile_expr(expr);
                self.asm().mode(inst::MODE_LUA);
                match op.kind {
                    token::Kind::Not => self.asm().not(),
                    token::Kind::Minus => self.asm().neg(),
                    token::Kind::Tilde => self.asm().notb(),
                    token::Kind::Hash => unimplemented!(),
                    _ => panic!("unexpected operator: {:?}", op.kind),
                }
            }
            Expr::Binary(left, op, right) => {
                self.compile_expr(left);
                self.compile_expr(right);
                self.asm().mode(inst::MODE_LUA);
                match op.kind {
                    token::Kind::Lt => self.asm().lt(),
                    token::Kind::LtEq => self.asm().le(),
                    token::Kind::Gt => self.asm().gt(),
                    token::Kind::GtEq => self.asm().ge(),
                    token::Kind::EqEq => self.asm().eq(),
                    token::Kind::TildeEq => self.asm().ne(),
                    token::Kind::Pipe => self.asm().or(),
                    token::Kind::Tilde => self.asm().xor(),
                    token::Kind::Amp => self.asm().and(),
                    token::Kind::LtLt => self.asm().shl(),
                    token::Kind::GtGt => self.asm().shr(),
                    token::Kind::DotDot => self.asm().strcat(),
                    token::Kind::Plus => self.asm().add(),
                    token::Kind::Minus => self.asm().sub(),
                    token::Kind::Star => self.asm().mul(),
                    token::Kind::Slash => self.asm().div(),
                    token::Kind::SlashSlash => self.asm().floordiv(),
                    token::Kind::Percent => self.asm().mod_(),
                    token::Kind::Caret => self.asm().exp(),
                    _ => panic!("unexpected operator: {:?}", op.kind),
                }
            }
            Expr::Group { expr, .. } => {
                self.compile_expr(expr);
            }
        }
    }

    fn compile_lvalue(&mut self, lval: &LValue<'src>) {
        self.line(lval.pos());
        // TODO: evaluate expressions that produce tables into which we're
        // storing fields. For now, no expression does that.
    }

    fn compile_define_prepare(&mut self, _: &Var) {
        // TODO: for captured variables, allocate a cell.
    }

    fn compile_define(&mut self, var: &Var) {
        match var.kind {
            VarKind::Global | VarKind::Parameter => unreachable!(),
            VarKind::Local => {
                // When a local variable is defined, it's always assigned
                // to the top of the stack. Since the value being assigned
                // is already there, we don't need to emit an instruction.
            }
            VarKind::Capture => unimplemented!(),
        }
    }

    fn compile_assign(&mut self, lval: &LValue<'src>) {
        self.line(lval.pos());
        match lval {
            LValue::Var {
                name,
                var_use: vuid,
                ..
            } => {
                let var_use = &self.scope_set.var_uses[vuid.0];
                match var_use.var {
                    Some(vid) => {
                        self.compile_store_var(&self.scope_set.vars[vid.0]);
                    }
                    None => {
                        self.asm().loadglobal(0); // _ENV
                        self.asm().swap();
                        let si = self.ensure_string(name.text.as_bytes(), name.pos());
                        self.asm().mode(inst::MODE_LUA);
                        self.asm().storenamedprop(si);
                    }
                }
            }
        }
    }

    fn compile_store_var_prepare(&mut self, _: &Var) {
        // TODO: for captured variables, load the cell
    }

    fn compile_store_var(&mut self, var: &Var) {
        match var.kind {
            VarKind::Global => {
                // Assignment to _ENV has no effect.
                self.asm().pop();
            }
            VarKind::Parameter => {
                self.asm().storearg(var.slot.try_into().unwrap());
            }
            VarKind::Local => {
                self.asm().storelocal(var.slot.try_into().unwrap());
            }
            VarKind::Capture => {
                // TODO: implement assign to capture.
                unimplemented!();
            }
        }
    }

    fn compile_var_use(&mut self, name: &Token<'src>, var_use: &VarUse) {
        if let Some(vid) = var_use.var {
            self.compile_load_var(&self.scope_set.vars[vid.0])
        } else {
            self.asm().loadglobal(0); // _ENV
            let si = self.ensure_string(name.text.as_bytes(), name.pos());
            self.asm().mode(inst::MODE_LUA);
            self.asm().loadnamedpropornil(si);
        }
    }

    fn compile_load_var(&mut self, var: &Var) {
        match var.kind {
            VarKind::Global => self.asm().loadglobal(var.slot.try_into().unwrap()),
            VarKind::Parameter => self.asm().loadarg(var.slot.try_into().unwrap()),
            VarKind::Local => self.asm().loadlocal(var.slot.try_into().unwrap()),
            VarKind::Capture => {
                // TODO: implement load from capture.
                unimplemented!();
            }
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

    fn ensure_label(&mut self, lid: LabelID) -> &mut Label {
        if self.named_labels.len() <= lid.0 {
            self.named_labels.resize_with(lid.0 + 1, || Label::new());
        }
        &mut self.named_labels[lid.0]
    }

    fn bind_named_label(&mut self, lid: LabelID) {
        self.ensure_label(lid);
        let last_asm_index = self.asm_stack.len() - 1;
        self.asm_stack[last_asm_index].bind(&mut self.named_labels[lid.0]);
    }

    fn b_named_label(&mut self, lid: LabelID) {
        self.ensure_label(lid);
        let last_asm_index = self.asm_stack.len() - 1;
        self.asm_stack[last_asm_index].b(&mut self.named_labels[lid.0]);
    }

    fn pop_block(&mut self, sid: ScopeID) {
        let scope = &self.scope_set.scopes[sid.0];
        for _ in 0..scope.slot_count {
            self.asm().pop();
        }
    }

    fn asm(&mut self) -> &mut Assembler {
        self.asm_stack.last_mut().unwrap()
    }

    fn line(&mut self, pos: Pos) {
        let e = self.lmap.encode_line(pos);
        self.asm().line(e);
    }

    fn error(&mut self, pos: Pos, message: String) {
        self.errors.push(Error {
            position: self.lmap.position(pos),
            message,
        })
    }
}
