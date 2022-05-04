use crate::scope::{self, Attr, CaptureFrom, ScopeSet, Var, VarKind, VarUse};
use crate::syntax::{
    self, Call, Chunk, Expr, LValue, LabelID, Param, ScopeID, Stmt, TableField, VarID,
};
use crate::token::{self, Number, Token};
use codeswitch::inst::{self, Assembler, Label};
use codeswitch::nanbox;
use codeswitch::package::{Function, Global, GlobalImport, Package, PackageImport, Type};
use codeswitch::pos::{Error, ErrorList, LineMap, PackageLineMap, Pos, Position};

use std::collections::HashMap;
use std::fs;
use std::mem;
use std::path::Path;

pub fn compile_file(path: &Path) -> Result<Package, ErrorList> {
    let data = fs::read(path).map_err(|err| {
        let position = Position::from(path);
        let wrapped = Error::wrap(position, &err);
        ErrorList(vec![wrapped])
    })?;
    compile_file_data(path, &data)
}

pub fn compile_file_data(path: &Path, data: &[u8]) -> Result<Package, ErrorList> {
    let mut lmap = LineMap::new();
    let mut errors = Vec::new();
    let tokens = token::lex(path, &data, &mut lmap, &mut errors);
    let chunk = syntax::parse(&tokens, &lmap, &mut errors);
    let scope_set = scope::resolve(&chunk, &lmap, &mut errors);
    if let Some(package) = compile_chunk(
        path.to_string_lossy().into(),
        &chunk,
        &scope_set,
        &lmap,
        &mut errors,
    ) {
        Ok(package)
    } else {
        Err(ErrorList::from(errors))
    }
}

pub fn compile_chunk(
    name: String,
    chunk: &Chunk,
    scope_set: &ScopeSet,
    lmap: &LineMap,
    errors: &mut Vec<Error>,
) -> Option<Package> {
    let mut cmp = Compiler::new(name, scope_set, lmap, errors);
    cmp.compile_chunk(chunk);
    cmp.finish()
}

struct Compiler<'src, 'ss, 'lm, 'err> {
    name: String,
    scope_set: &'ss ScopeSet<'src>,
    lmap: &'lm LineMap,
    globals: Vec<Global>,
    functions: Vec<Function>,
    strings: Vec<Vec<u8>>,
    string_index: HashMap<Vec<u8>, u32>,
    types: Vec<Type>,
    type_index: HashMap<Type, u32>,
    named_labels: Vec<inst::Label>,
    asm: Assembler,
    param_count: u16,
    is_variadic: bool,
    block_stack: Vec<Block>,
    func_stack: Vec<FuncState>,
    in_handler: bool,
    errors: &'err mut Vec<Error>,
}

struct FuncState {
    asm: Assembler,
    param_count: u16,
    is_variadic: bool,
}

impl<'src, 'ss, 'lm, 'err> Compiler<'src, 'ss, 'lm, 'err> {
    fn new(
        name: String,
        scope_set: &'ss ScopeSet<'src>,
        lmap: &'lm LineMap,
        errors: &'err mut Vec<Error>,
    ) -> Compiler<'src, 'ss, 'lm, 'err> {
        Compiler {
            name,
            scope_set,
            lmap,
            globals: Vec::new(),
            functions: Vec::new(),
            strings: Vec::new(),
            string_index: HashMap::new(),
            types: Vec::new(),
            type_index: HashMap::new(),
            named_labels: Vec::new(),
            asm: Assembler::new(),
            param_count: 0,
            is_variadic: false,
            block_stack: Vec::new(),
            func_stack: Vec::new(),
            in_handler: false,
            errors,
        }
    }

    fn finish(mut self) -> Option<Package> {
        self.asm.setvi(0);
        self.asm.mode(inst::MODE_LUA);
        self.asm.retv();
        match self.asm.finish() {
            Ok((insts, line_map)) => {
                self.functions.push(Function {
                    name: String::from(""),
                    insts,
                    param_types: Vec::new(),
                    var_param_type: None,
                    return_types: Vec::new(),
                    var_return_type: Some(Type::NanBox),
                    cell_types: Vec::new(),
                    line_map,
                });
            }
            Err(err) => {
                self.errors.push(Error::wrap(self.lmap.first_file(), &err));
            }
        }

        let init_index: u32 = match (self.functions.len() - 1).try_into() {
            Ok(i) => i,
            _ => {
                self.errors.push(Error {
                    position: self.lmap.first_file(),
                    message: String::from("too many functions"),
                });
                !0
            }
        };
        if !self.errors.is_empty() {
            return None;
        }

        let imports = vec![PackageImport::new(
            String::from("luastd"),
            vec![
                GlobalImport::new(String::from("_ENV"), Type::NanBox),
                GlobalImport::new(String::from("_G"), Type::NanBox),
            ],
            Vec::new(),
        )];
        let package = Package {
            name: self.name,
            globals: self.globals,
            functions: self.functions,
            init_index: Some(init_index),
            strings: self.strings,
            types: self.types,
            line_map: PackageLineMap::from(self.lmap),
            imports,
        };
        Some(package)
    }

    fn compile_chunk(&mut self, chunk: &Chunk<'src>) {
        self.enter_block(chunk.chunk_scope, chunk.pos());
        for stmt in &chunk.stmts {
            self.compile_stmt(stmt);
        }
        self.leave_block();
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

                // Compile the expressions on the right, then adjust the number
                // of values to match the number of expressions on the left.
                let len_known = self.compile_expr_list(right, 0);
                self.compile_adjust(len_known, left.len(), stmt.pos());

                // Perform the actual assignment, right to left.
                // Again, the reference doesn't say what should happen here if
                // the same location is assigned multiple times. This is what
                // the main Lua interpreter does.
                for l in left.iter().rev() {
                    self.compile_assign(l);
                }
            }
            Stmt::Local {
                left, right, pos, ..
            } => {
                let len_known = self.compile_expr_list(right, 0);
                self.compile_adjust(len_known, left.len(), *pos);

                for l in left {
                    let var = &self.scope_set.vars[l.var.0];
                    self.compile_define_from_list(var);
                    if var.attr == Attr::Close {
                        // Check that the variable is nil, false, or has a
                        // non-nil metatable field named "__close".
                        self.compile_load_var(var, None);
                        let error_message = format!(
                            "variable '{}' has close attribute but is not closable",
                            l.name.text
                        );
                        self.compile_check_closable(error_message.as_bytes(), *pos);

                        // Push the address of the handler to ensure the close
                        // method is called later.
                        let mut handler_label = Label::new();
                        self.asm.pushhandler(&mut handler_label);
                        self.add_close(l.var, handler_label);
                    }
                }
            }
            Stmt::Do { stmts, scope, .. } => {
                self.enter_block(*scope, stmt.pos());
                for stmt in stmts {
                    self.compile_stmt(stmt);
                }
                self.leave_block();
            }
            Stmt::If {
                cond_blocks,
                false_block,
                ..
            } => {
                let mut end_label = Label::new();
                let pre_enabled = self.enabled();
                let mut post_enabled = false;
                for block in cond_blocks {
                    let mut next_label = Label::new();
                    self.compile_expr(&block.cond);
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.not();
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.bif(&mut next_label);
                    self.enter_block(block.scope, stmt.pos());
                    for stmt in &block.stmts {
                        self.compile_stmt(stmt);
                    }
                    self.leave_block();
                    self.asm.b(&mut end_label);
                    post_enabled |= self.enabled();
                    if pre_enabled {
                        self.set_enabled(true);
                    }
                    self.asm.bind(&mut next_label);
                }
                if let Some(block) = false_block {
                    self.enter_block(block.scope, stmt.pos());
                    for stmt in &block.stmts {
                        self.compile_stmt(stmt);
                    }
                    post_enabled |= self.enabled();
                    if pre_enabled {
                        self.set_enabled(true);
                    }
                    self.leave_block();
                }
                self.set_enabled(post_enabled);
                self.asm.bind(&mut end_label);
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
                let enabled = self.enabled();
                self.asm.b(&mut cond_label);
                self.asm.bind(&mut body_label);
                self.enter_block(*scope, stmt.pos());
                for stmt in body {
                    self.compile_stmt(stmt);
                }
                self.leave_block();
                if enabled {
                    self.set_enabled(true);
                }
                self.asm.bind(&mut cond_label);
                self.compile_expr(cond);
                self.asm.mode(inst::MODE_LUA);
                self.asm.bif(&mut body_label);
                self.bind_named_label(*break_lid);
            }
            Stmt::Repeat {
                body,
                cond,
                cond_scope,
                body_scope,
                cond_var: cond_vid,
                break_label: break_lid,
                ..
            } => {
                // Reserve a slot for the hidden condition variable.
                // We evaluate the condition in the body scope, but we'll likely
                // need to pop a bunch of stuff from the body before branching,
                // so it's nice to be able to put the condition in a local
                // instead of a temporary.
                let enabled = self.enabled();
                self.enter_block(*cond_scope, stmt.pos());
                let cond_var = &self.scope_set.vars[cond_vid.0];
                self.asm.constzero();
                self.asm.nanbox();

                // Compile the body.
                let mut body_label = Label::new();
                self.asm.bind(&mut body_label);
                self.enter_block(*body_scope, stmt.pos());
                for stmt in body {
                    self.compile_stmt(stmt);
                }

                // Compile the condition in the scope of the body.
                // Store the condtion, leave the body scope, then branch.
                self.compile_expr(cond);
                self.asm.mode(inst::MODE_LUA);
                self.asm.not();
                self.compile_store_var(cond_var, None);
                self.leave_block();
                self.asm.dup();
                self.asm.mode(inst::MODE_LUA);
                self.asm.bif(&mut body_label);
                self.leave_block();
                self.set_enabled(enabled);
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
                let enabled = self.enabled();

                // Evaluate the init, limit, and step expressions.
                // Check that step is a non-negative number.
                // Assign to hidden variables.
                self.enter_block(*ind_scope, stmt.pos());
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
                        self.asm.dup();
                        self.asm.const_(0);
                        self.asm.nanbox();
                        self.asm.ne();
                        self.asm.bif(&mut step_ok_label);
                        let si = self.ensure_string(b"'for' step is zero", step.pos());
                        self.asm.string(si);
                        self.asm.mode(inst::MODE_STRING);
                        self.asm.panic(0);
                        self.asm.bind(&mut step_ok_label);
                    }
                    None => {
                        self.asm.const_(1);
                        self.asm.nanbox();
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
                self.compile_load_var(ind_var, None);
                self.asm.mode(inst::MODE_LUA);
                self.asm.typeof_();
                self.asm.dup();
                self.asm.const_(nanbox::TAG_SMALL_INT);
                self.asm.eq();
                self.asm.bif(&mut ind_is_int_label);
                self.asm.dup();
                self.asm.const_(nanbox::TAG_BIG_INT);
                self.asm.ne();
                self.asm.bif(&mut convert_float_label);

                self.asm.bind(&mut ind_is_int_label);
                if let Some(step) = step {
                    self.line(step.pos());
                    self.asm.pop(); // type of ind
                    self.compile_load_var(step_var, None);
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.typeof_();
                    self.asm.dup();
                    self.asm.const_(nanbox::TAG_SMALL_INT);
                    self.asm.eq();
                    self.asm.bif(&mut ind_and_step_are_int_label);
                    self.asm.dup();
                    self.asm.const_(nanbox::TAG_BIG_INT);
                    self.asm.ne();
                    self.asm.bif(&mut convert_float_label);
                    // TODO: panic on zero step
                }

                self.asm.bind(&mut ind_and_step_are_int_label);
                self.asm.pop(); // type of step or ind
                self.asm.b(&mut check_limit_label);

                self.line(init.pos());
                self.asm.bind(&mut convert_float_label);
                self.asm.pop(); // type of step or ind
                self.compile_store_var_prepare(ind_var);
                self.compile_load_var(ind_var, None);
                self.asm.mode(inst::MODE_LUA);
                self.asm.tofloat();
                self.asm.mode(inst::MODE_F64);
                self.asm.nanbox();
                self.compile_store_var(ind_var, None);
                self.compile_store_var_prepare(step_var);
                self.compile_load_var(step_var, None);
                self.asm.mode(inst::MODE_LUA);
                self.asm.tofloat();
                self.asm.mode(inst::MODE_F64);
                self.asm.nanbox();
                self.compile_store_var(step_var, None);

                // Also check that limit is a number. We don't convert it
                // to a float if init and step were floats though.
                self.asm.bind(&mut check_limit_label);
                self.compile_load_var(limit_var, None);
                self.asm.mode(inst::MODE_LUA);
                self.asm.typeof_();
                self.asm.dup();
                self.asm.const_(nanbox::TAG_SMALL_INT);
                self.asm.eq();
                self.asm.bif(&mut limit_ok_label);
                self.asm.dup();
                self.asm.const_(nanbox::TAG_BIG_INT);
                self.asm.eq();
                self.asm.bif(&mut limit_ok_label);
                self.asm.dup();
                self.asm.const_(nanbox::TAG_FLOAT);
                self.asm.eq();
                self.asm.bif(&mut limit_ok_label);
                let si = self.ensure_string(b"'for' limit is not a number", limit.pos());
                self.asm.string(si);
                self.asm.mode(inst::MODE_STRING);
                self.asm.panic(0);
                self.asm.bind(&mut limit_ok_label);
                self.asm.pop(); // typeof limit
                self.asm.b(&mut cond_label);

                // Compile the loop body. The condition is checked at the
                // bottom, so the body comes first. We copy the hidden induction
                // variable to the visible variable first.
                self.asm.bind(&mut body_label);
                self.enter_block(*body_scope, stmt.pos());
                self.compile_define_prepare(body_var);
                self.compile_load_var(ind_var, None);
                self.compile_define(body_var);
                for stmt in body {
                    self.compile_stmt(stmt);
                }
                self.leave_block();

                // Increment the induction variable by step.
                // If step is an integer, check that the induction variable
                // did not overflow to float. That should terminate the loop.
                let mut step_inc_ok_label = Label::new();
                self.line(init.pos());
                self.compile_store_var_prepare(ind_var);
                self.compile_load_var(ind_var, None);
                self.compile_load_var(step_var, None);
                self.asm.mode(inst::MODE_LUA);
                self.asm.add();
                self.compile_load_var(step_var, None);
                self.asm.mode(inst::MODE_LUA);
                self.asm.typeof_();
                self.asm.const_(nanbox::TAG_FLOAT);
                self.asm.eq();
                self.asm.bif(&mut step_inc_ok_label);
                self.asm.dup();
                self.asm.mode(inst::MODE_LUA);
                self.asm.typeof_();
                self.asm.const_(nanbox::TAG_FLOAT);
                self.asm.ne();
                self.asm.bif(&mut step_inc_ok_label);
                self.asm.pop();
                self.b_named_label(*break_lid);
                self.asm.bind(&mut step_inc_ok_label);
                self.compile_store_var(ind_var, None);

                // Check the condition.
                // If step is positive, we check ind <= limit.
                // Otherwise, we check ind >= limit.
                let mut negative_cond_label = Label::new();
                if enabled {
                    self.set_enabled(true);
                }
                self.line(limit.pos());
                self.asm.bind(&mut cond_label);
                self.compile_load_var(ind_var, None);
                self.compile_load_var(limit_var, None);
                self.compile_load_var(step_var, None);
                self.asm.constzero();
                self.asm.nanbox();
                self.asm.mode(inst::MODE_LUA);
                self.asm.lt();
                self.asm.mode(inst::MODE_LUA);
                self.asm.bif(&mut negative_cond_label);
                self.asm.mode(inst::MODE_LUA);
                self.asm.le();
                self.asm.mode(inst::MODE_LUA);
                self.asm.bif(&mut body_label);
                self.b_named_label(*break_lid);
                self.asm.bind(&mut negative_cond_label);
                self.asm.swap();
                self.asm.mode(inst::MODE_LUA);
                self.asm.le();
                self.asm.mode(inst::MODE_LUA);
                self.asm.bif(&mut body_label);

                // End of the loop.
                self.bind_named_label(*break_lid);
                self.leave_block();
            }
            Stmt::ForIn {
                names,
                exprs,
                body,
                ind_scope,
                named_scope,
                body_scope,
                vars: vids,
                iter_var: iter_vid,
                state_var: state_vid,
                control_var: control_vid,
                close_var: close_vid,
                break_label: break_lid,
                ..
            } => {
                // Evaluate the expressions and assign to the four induction
                // variables. The induction variables must be local (not
                // captured) and must be grouped together in order.
                // This happens once at the beginning.
                let iter_var = &self.scope_set.vars[iter_vid.0];
                let state_var = &self.scope_set.vars[state_vid.0];
                let control_var = &self.scope_set.vars[control_vid.0];
                let close_var = &self.scope_set.vars[close_vid.0];
                assert!(
                    iter_var.kind == VarKind::Local
                        && state_var.kind == VarKind::Local
                        && state_var.slot == iter_var.slot + 1
                        && control_var.kind == VarKind::Local
                        && control_var.slot == iter_var.slot + 2
                        && close_var.kind == VarKind::Local
                        && close_var.slot == iter_var.slot + 3
                );
                let enabled = self.enabled();
                self.enter_block(*ind_scope, stmt.pos());
                let len_known = self.compile_expr_list(exprs, 0);
                let exprs_pos = exprs
                    .first()
                    .unwrap()
                    .pos()
                    .combine(exprs.last().unwrap().pos());
                self.compile_adjust(len_known, 4, exprs_pos);

                // Check that the last induction variable is closable.
                // Push its handler.
                let exprs_pos = exprs
                    .first()
                    .unwrap()
                    .pos()
                    .combine(exprs.last().unwrap().pos());
                self.asm.dup();
                self.compile_check_closable(
                    b"in for-in loop, close value is not closeable",
                    exprs_pos,
                );
                let mut handler_label = Label::new();
                self.asm.pushhandler(&mut handler_label);
                self.add_close(*close_vid, handler_label);

                let mut cond_label = Label::new();
                self.asm.b(&mut cond_label);

                // Loop body.
                let mut body_label = Label::new();
                self.asm.bind(&mut body_label);
                self.enter_block(*named_scope, stmt.pos());
                self.enter_block(*body_scope, stmt.pos());
                for stmt in body {
                    self.compile_stmt(stmt);
                }
                self.leave_block(); // body
                self.leave_block(); // named

                // Loop condition.
                // Call the iterator function with the control and state
                // variables. Assign the results to the named variables, and
                // copy the first result back to control. If control is nil,
                // end the loop.
                if enabled {
                    self.set_enabled(true);
                }
                self.asm.bind(&mut cond_label);
                self.enter_block(*named_scope, stmt.pos());
                self.compile_load_var(iter_var, None);
                self.compile_load_var(state_var, None);
                self.compile_load_var(control_var, None);
                self.asm.mode(inst::MODE_LUA);
                self.asm.callvalue(2);
                let names_pos = names
                    .first()
                    .unwrap()
                    .pos()
                    .combine(names.last().unwrap().pos());
                self.compile_adjust(ExprListLen::Dynamic, names.len(), names_pos);
                for vid in vids {
                    let var = &self.scope_set.vars[vid.0];
                    self.compile_define_from_list(var);
                }
                self.compile_load_var(&self.scope_set.vars[vids[0].0], None);
                self.compile_store_var(control_var, None);
                self.compile_load_var(&self.scope_set.vars[vids[0].0], None);
                self.asm.constzero();
                self.asm.mode(inst::MODE_PTR);
                self.asm.nanbox();
                self.asm.ne();
                self.asm.bif(&mut body_label);

                // End of the loop.
                self.leave_block(); // named
                self.leave_block(); // ind
                self.bind_named_label(*break_lid);
            }
            Stmt::Break {
                label_use: luid, ..
            } => {
                let label_use = &self.scope_set.label_uses[luid.0];
                if let Some(lid) = label_use.label {
                    self.compile_pop_slots_and_handlers(
                        label_use.slot_count,
                        label_use.handler_count,
                    );
                    self.b_named_label(lid);
                }
                self.set_enabled(false);
            }
            Stmt::Label { label: lid, .. } => {
                // We don't know whether the label is referenced by any
                // reachable goto, so we unconditionally enable code generation.
                // We could potentially do a reachability analysis in an earlier
                // phase, but it doesn't seem worthwhile.
                self.set_enabled(true);
                self.bind_named_label(*lid);
            }
            Stmt::Goto {
                label_use: luid, ..
            } => {
                let label_use = &self.scope_set.label_uses[luid.0];
                if let Some(lid) = label_use.label {
                    self.compile_pop_slots_and_handlers(
                        label_use.slot_count,
                        label_use.handler_count,
                    );
                    self.b_named_label(lid);
                }
                self.set_enabled(false);
            }
            Stmt::Function {
                name,
                is_variadic,
                parameters,
                param_scope,
                body_scope,
                body,
                pos,
                ..
            } => {
                // A function statement is essentially an assignment with a
                // complicated L-value that doesn't appear in any context.
                // Prepare to assign the function to a field or capture cell
                // by loading whatever we need to load.
                let is_method_assign = !name.fields.is_empty() || name.method_name.is_some();
                let var_use = &self.scope_set.var_uses[name.var_use.0];
                if let Some(vid) = var_use.var {
                    // First part of name is a known variable.
                    let var = &self.scope_set.vars[vid.0];
                    if is_method_assign {
                        let si = self.check_slot(var.slot, name.name.pos(), "variables");
                        match var.kind {
                            VarKind::Global => (),
                            VarKind::Parameter => self.asm.loadarg(si),
                            VarKind::Local => self.asm.loadlocal(si),
                            VarKind::Capture => {
                                let slot = var_use.cell.unwrap_or(var.cell_slot);
                                let si = self.check_slot(slot, name.name.pos(), "captures");
                                self.asm.capture(si);
                                self.asm.load();
                            }
                        }
                    }
                } else {
                    // First part of name is unknown. May or may not be in _ENV.
                    self.asm.loadimportglobal(0, 0);
                    if is_method_assign {
                        let si = self.ensure_string(name.name.text.as_bytes(), name.name.pos());
                        self.asm.mode(inst::MODE_LUA);
                        self.asm.loadnamedprop(si);
                    }
                }
                let last_field_index = if name.method_name.is_some() || name.fields.is_empty() {
                    name.fields.len()
                } else {
                    name.fields.len() - 1
                };
                for i in 0..last_field_index {
                    let f = name.fields[i];
                    let si = self.ensure_string(f.text.as_bytes(), f.pos());
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.loadnamedprop(si);
                }

                // Compile the function and create a closure.
                let receiver_vid = name.method_name.map(|m| m.receiver_var);
                let fn_index = self.compile_function(
                    name.to_string(),
                    receiver_vid,
                    parameters,
                    *is_variadic,
                    body,
                    *param_scope,
                    *body_scope,
                    *pos,
                );
                self.compile_closure(fn_index, *param_scope, *pos);

                // Assign the closure value wherever it needs to go.
                if is_method_assign {
                    let last_name = name
                        .method_name
                        .map(|m| m.name)
                        .unwrap_or_else(|| *name.fields.last().unwrap());
                    let si = self.ensure_string(last_name.text.as_bytes(), last_name.pos());
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.storenamedprop(si);
                } else if let Some(vid) = var_use.var {
                    // Assignment to known variable, possibly captured.
                    let var = &self.scope_set.vars[vid.0];
                    self.compile_store_var(var, var_use.cell);
                } else {
                    // Assignment to property in _ENV.
                    let si = self.ensure_string(name.name.text.as_bytes(), name.name.pos());
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.storenamedprop(si);
                }
            }
            Stmt::LocalFunction {
                name: name_tok,
                parameters,
                param_scope,
                body_scope,
                is_variadic,
                body,
                var: vid,
                pos,
                ..
            } => {
                let var = &self.scope_set.vars[vid.0];
                self.compile_define_prepare(var);
                let name = String::from(name_tok.text);
                let fn_index = self.compile_function(
                    name,
                    None,
                    parameters,
                    *is_variadic,
                    body,
                    *param_scope,
                    *body_scope,
                    *pos,
                );
                self.compile_closure(fn_index, *param_scope, *pos);
                self.compile_define(var);
            }
            Stmt::Call(call) => {
                self.compile_call(call, ResultMode::Drop);
            }
            Stmt::Return {
                exprs, ret: rid, ..
            } => {
                // TODO: support tail calls.
                // TODO: disable code generation after return.
                // Compile the expressions to return. If the last expression is
                // a call or '...', we don't statically know the number of
                // values being returned, but compile_expr_list will set the
                // vc register for us. If we do statically know, we'll need to
                // use setv explicitly. In either case, vc is set to the number
                // of returned values, so the caller knows what to do with them.
                let len_known = self.compile_expr_list(exprs, 0);

                // If there are error handlers introduced by "close" variables,
                // run them now. Save vc if needed.
                let ret = &self.scope_set.returns[rid.0];
                if ret.handler_count > 0 {
                    if len_known == ExprListLen::Dynamic {
                        self.asm.getv();
                    }
                    for _ in 0..ret.handler_count {
                        self.asm.callhandler();
                    }
                    if len_known == ExprListLen::Dynamic {
                        self.asm.setv();
                    }
                }
                if let ExprListLen::Static(n) = len_known {
                    self.asm.setvi(n);
                }
                self.asm.mode(inst::MODE_LUA);
                self.asm.retv();
                self.set_enabled(false);
            }
        }
    }

    fn compile_expr(&mut self, expr: &Expr<'src>) {
        self.line(expr.pos());
        match expr {
            Expr::Literal(t) => {
                match t.kind {
                    token::Kind::Nil => {
                        self.asm.constzero();
                        self.asm.mode(inst::MODE_PTR);
                    }
                    token::Kind::True => {
                        self.asm.const_(1);
                        self.asm.mode(inst::MODE_BOOL);
                    }
                    token::Kind::False => {
                        self.asm.constzero();
                        self.asm.mode(inst::MODE_BOOL);
                    }
                    token::Kind::Number => match token::convert_number(t.text) {
                        Number::Int(n) if n == 0 => {
                            self.asm.constzero();
                        }
                        Number::Int(n) => {
                            self.asm.const_(n as u64);
                        }
                        Number::Float(n) => {
                            self.asm.const_(n.to_bits());
                            self.asm.mode(inst::MODE_F64);
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
                        self.asm.string(si);
                        self.asm.mode(inst::MODE_STRING);
                    }
                    _ => unreachable!(),
                }
                self.asm.nanbox();
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
                self.asm.mode(inst::MODE_LUA);
                match op.kind {
                    token::Kind::Not => self.asm.not(),
                    token::Kind::Minus => self.asm.neg(),
                    token::Kind::Tilde => self.asm.notb(),
                    token::Kind::Hash => self.asm.len(),
                    _ => panic!("unexpected operator: {:?}", op.kind),
                }
            }
            Expr::Binary(left, op, right) => {
                self.compile_expr(left);
                if op.kind == token::Kind::And {
                    let mut after_label = Label::new();
                    self.asm.dup();
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.not();
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.bif(&mut after_label);
                    self.asm.pop();
                    self.compile_expr(right);
                    self.asm.bind(&mut after_label);
                } else if op.kind == token::Kind::Or {
                    let mut after_label = Label::new();
                    self.asm.dup();
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.bif(&mut after_label);
                    self.asm.pop();
                    self.compile_expr(right);
                    self.asm.bind(&mut after_label);
                } else {
                    self.compile_expr(right);
                    match op.kind {
                        token::Kind::Lt => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.lt();
                        }
                        token::Kind::LtEq => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.le();
                        }
                        token::Kind::Gt => {
                            // Lua translates a > b to b < a.
                            // The __lt metamethod may be implemented to
                            // override <, but there is no __gt metamethod.
                            self.asm.swap();
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.lt();
                        }
                        token::Kind::GtEq => {
                            // Lua translates a >= b to b <= a.
                            // See above.
                            self.asm.swap();
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.le();
                        }
                        token::Kind::EqEq => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.eq();
                        }
                        token::Kind::TildeEq => {
                            // ~= is defined as the negation of ==. == may call
                            // the __eq metamethod (there is no __ne metamethod)
                            // and we need an instruction after to negate it.
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.eq();
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.not();
                        }
                        token::Kind::Pipe => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.or();
                        }
                        token::Kind::Tilde => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.xor();
                        }
                        token::Kind::Amp => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.and();
                        }
                        token::Kind::LtLt => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.shl();
                        }
                        token::Kind::GtGt => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.shr();
                        }
                        token::Kind::DotDot => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.strcat();
                        }
                        token::Kind::Plus => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.add();
                        }
                        token::Kind::Minus => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.sub();
                        }
                        token::Kind::Star => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.mul();
                        }
                        token::Kind::Slash => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.div();
                        }
                        token::Kind::SlashSlash => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.floordiv();
                        }
                        token::Kind::Percent => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.mod_();
                        }
                        token::Kind::Caret => {
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.exp();
                        }
                        _ => panic!("unexpected operator: {:?}", op.kind),
                    }
                }
            }
            Expr::Group { expr, .. } => {
                self.compile_expr(expr);
            }
            Expr::Function {
                parameters,
                param_scope,
                body_scope,
                is_variadic,
                body,
                pos,
                ..
            } => {
                let name = String::from("·anonymous");
                let fn_index = self.compile_function(
                    name,
                    None,
                    parameters,
                    *is_variadic,
                    body,
                    *param_scope,
                    *body_scope,
                    *pos,
                );
                self.compile_closure(fn_index, *param_scope, *pos);
            }
            Expr::Call(call) => {
                self.compile_call(call, ResultMode::Truncate);
            }
            Expr::VarArgs(t) => {
                if !self.is_variadic {
                    self.error(
                        t.pos(),
                        String::from("cannot use '...' outside a variadic function"),
                    );
                }
                self.asm.mode(inst::MODE_LUA);
                self.asm.loadvarargs();
                self.asm.mode(inst::MODE_LUA);
                self.asm.adjustv(1);
            }
            Expr::Table { fields, .. } => {
                let ti = self.ensure_type(Type::Object);
                self.asm.alloc(ti);
                self.asm.mode(inst::MODE_OBJECT);
                self.asm.nanbox();
                let mut count: i64 = 1;
                for field in fields {
                    self.asm.dup();
                    match field {
                        TableField::NameField(key, value) => {
                            self.compile_expr(value);
                            let si = self.ensure_string(key.text.as_bytes(), key.pos());
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.storenamedprop(si);
                        }
                        TableField::ExprField(key, value) => {
                            self.compile_expr(key);
                            self.compile_expr(value);
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.storeindexprop();
                        }
                        TableField::CountField(value) => {
                            self.asm.const_(count as u64);
                            self.asm.nanbox();
                            self.compile_expr(value);
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.storeindexprop();
                            count += 1;
                        }
                    }
                }
            }
            Expr::Dot { expr, name, .. } => {
                self.compile_expr(expr);
                let si = self.ensure_string(name.text.as_bytes(), name.pos());
                self.asm.mode(inst::MODE_LUA);
                self.asm.loadnamedpropornil(si);
            }
            Expr::Index { expr, index, .. } => {
                self.compile_expr(expr);
                self.compile_expr(index);
                self.asm.mode(inst::MODE_LUA);
                self.asm.loadindexpropornil();
            }
        }
    }

    /// Compiles a list of expressions, as in an assignment, local definition,
    /// argument list, or return list.
    ///
    /// The "extra" parameter indicates the number of implicit expressions at
    /// the beginning of the list. This is only used for method receivers.
    ///
    /// Every expression except the last pushes exactly one value. If an
    /// expression dynamically produces 0 values, nil is pushed. If an
    /// expression produces multiple values, all but the first are dropped.
    /// Function calls and '...' are expressions like this.
    ///
    /// If the last expression produces a dynamic number of values, they're
    /// all pushed and ExprListLen::Dynamic is returned. In this case, the
    /// vc (value count) register will be set to the total number of values
    /// pushed by all expressions plus extra (which may be 1 to account for an
    /// implicit receiver). If the last expression statically produces
    /// one value, or if there are no expressions, ExprListLen::Static is
    /// returned. The caller may choose to run setv to set vc, if needed.
    fn compile_expr_list(&mut self, exprs: &[Expr<'src>], extra: usize) -> ExprListLen {
        if exprs.len() >= 2 {
            for expr in exprs.iter().take(exprs.len() - 1) {
                self.compile_expr(expr);
            }
        }
        let static_expr_count: u16 = match (exprs.len() + extra).try_into() {
            Ok(n) => n,
            Err(_) => {
                self.error(
                    exprs.last().unwrap().pos(),
                    String::from("too many expressions"),
                );
                !0
            }
        };
        match exprs.last() {
            Some(Expr::Call(call)) => {
                self.compile_call(call, ResultMode::Append);
                if static_expr_count > 1 {
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.appendv(static_expr_count - 1);
                }
                ExprListLen::Dynamic
            }
            Some(Expr::VarArgs(t)) => {
                if !self.is_variadic {
                    self.error(
                        t.pos(),
                        String::from("cannot use '...' outside a variadic function"),
                    );
                }
                self.asm.mode(inst::MODE_LUA);
                self.asm.loadvarargs();
                if static_expr_count > 1 {
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.appendv(static_expr_count - 1);
                }
                ExprListLen::Dynamic
            }
            Some(expr) => {
                self.compile_expr(expr);
                ExprListLen::Static(static_expr_count)
            }
            None => ExprListLen::Static(static_expr_count),
        }
    }

    /// Adjusts a compiled list of values (produced by compile_expr_list) to
    /// the given length by popping extra values or pushing nil.
    ///
    /// If the number of values is known statically, compile_adjust emits
    /// the correct number of pop or constzero/nanbox/dup instructions.
    ///
    /// If the number of values is not known statically, for example, because
    /// the last expression is a function call, compile_adjust emits adjustv,
    /// which pushes or pops based on the vc register, which compile_expr_list
    /// should have set.
    fn compile_adjust(&mut self, len_known: ExprListLen, want: usize, pos: Pos) {
        let want_narrow: u16 = match want.try_into() {
            Ok(n) => n,
            _ => {
                self.error(pos, String::from("too many expressions"));
                !0
            }
        };
        match len_known {
            ExprListLen::Static(expr_count) => {
                if want_narrow > expr_count {
                    self.asm.constzero();
                    self.asm.mode(inst::MODE_PTR);
                    self.asm.nanbox();
                    for _ in 0..(want_narrow - expr_count - 1) {
                        self.asm.dup();
                    }
                } else {
                    for _ in 0..(expr_count - want_narrow) {
                        self.asm.pop();
                    }
                }
            }
            ExprListLen::Dynamic => {
                self.asm.mode(inst::MODE_LUA);
                self.asm.adjustv(want_narrow);
            }
        }
    }

    fn compile_lvalue(&mut self, lval: &LValue<'src>) {
        self.line(lval.pos());
        match lval {
            LValue::Var { .. } => (),
            LValue::Dot { expr, .. } => self.compile_expr(expr),
            LValue::Index { expr, index, .. } => {
                self.compile_expr(expr);
                self.compile_expr(index);
            }
        }
    }

    fn compile_function(
        &mut self,
        name: String,
        receiver: Option<VarID>,
        parameters: &[Param<'src>],
        is_variadic: bool,
        body: &[Stmt<'src>],
        param_sid: ScopeID,
        body_sid: ScopeID,
        pos: Pos,
    ) -> u32 {
        // Start compiling the function.
        self.push_func(parameters.len().try_into().unwrap(), is_variadic);
        self.line(pos);
        self.enter_block(param_sid, pos);

        // Move captured parameters into cells.
        let mut cell_slot = 0;
        let mut move_captured_param = |vid: VarID| {
            let var = &self.scope_set.vars[vid.0];
            if var.kind == VarKind::Capture {
                let ti = self.ensure_type(Type::NanBox);
                self.asm.alloc(ti);
                self.asm.dup();
                let param_slot = match var.slot.try_into() {
                    Ok(n) => n,
                    Err(_) => {
                        self.error(pos, String::from("too many parameters"));
                        !0
                    }
                };
                self.asm.loadarg(param_slot);
                self.asm.mode(inst::MODE_LUA);
                self.asm.store();
                assert_eq!(var.cell_slot, cell_slot);
                cell_slot += 1;
            }
        };
        if let Some(vid) = receiver {
            move_captured_param(vid);
        }
        for p in parameters {
            move_captured_param(p.var);
        }

        // Compile the function body.
        self.enter_block(body_sid, pos);
        for stmt in body {
            self.compile_stmt(stmt);
        }

        // If the function didn't end with a return statement,
        // return nothing.
        self.leave_block();
        self.leave_block();
        self.asm.setvi(0);
        self.asm.mode(inst::MODE_LUA);
        self.asm.retv();

        // Finish building the function and add it to the package.
        let (insts, line_map) = match self.pop_func().finish() {
            Ok(res) => res,
            Err(err) => {
                self.errors.push(Error::wrap(self.lmap.position(pos), &err));
                return !0;
            }
        };
        let param_count = if receiver.is_some() {
            parameters.len() + 1
        } else {
            parameters.len()
        };
        let param_types = vec![Type::NanBox; param_count];
        let var_param_type = if is_variadic {
            Some(Type::NanBox)
        } else {
            None
        };
        let fn_index = match self.functions.len().try_into() {
            Ok(i) => i,
            Err(_) => {
                self.error(pos, String::from("too many functions"));
                return !0;
            }
        };
        self.functions.push(Function {
            name: String::from(name),
            insts,
            param_types,
            var_param_type,
            return_types: Vec::new(),
            var_return_type: Some(Type::NanBox),
            cell_types: Vec::new(),
            line_map,
        });
        fn_index
    }

    fn compile_closure(&mut self, fn_index: u32, param_sid: ScopeID, pos: Pos) {
        // Load variables captured by the function or one of its nested
        // functions.
        let param_scope = &self.scope_set.scopes[param_sid.0];
        for capture in &param_scope.captures {
            match capture.from {
                CaptureFrom::Local => {
                    let slot = self.scope_set.vars[capture.var.0]
                        .cell_slot
                        .try_into()
                        .unwrap();
                    self.asm.loadlocal(slot);
                }
                CaptureFrom::Closure(slot) => {
                    self.asm.capture(slot.try_into().unwrap());
                }
            }
        }

        // Construct and box the closure.
        let capture_count = match param_scope.captures.len().try_into() {
            Ok(n) => n,
            Err(_) => {
                self.error(pos, String::from("too many captures"));
                !0
            }
        };
        let bound_arg_count = 0;
        self.asm
            .newclosure(fn_index, capture_count, bound_arg_count);
        self.asm.mode(inst::MODE_CLOSURE);
        self.asm.nanbox();
    }

    fn compile_call(&mut self, call: &Call<'src>, rmode: ResultMode) {
        self.compile_expr(&call.callee);
        let extra = if call.method_name.is_some() {
            // Lua doesn't have methods. A call like a:b(c) just copies the
            // receiver on the stack.
            self.asm.dup();
            1
        } else {
            0
        };
        let arg_len = self.compile_expr_list(&call.arguments, extra);
        self.asm.mode(inst::MODE_LUA);
        if let Some(name) = call.method_name {
            let si = self.ensure_string(name.text.as_bytes(), name.pos());
            match arg_len {
                ExprListLen::Static(n) => self.asm.callnamedprop(si, n),
                ExprListLen::Dynamic => self.asm.callnamedpropv(si),
            }
        } else {
            match arg_len {
                ExprListLen::Static(n) => self.asm.callvalue(n),
                ExprListLen::Dynamic => self.asm.callvaluev(),
            }
        }

        match rmode {
            ResultMode::Drop => {
                self.asm.mode(inst::MODE_LUA);
                self.asm.adjustv(0);
            }
            ResultMode::Truncate => {
                self.asm.mode(inst::MODE_LUA);
                self.asm.adjustv(1);
            }
            ResultMode::Append => (),
        }
    }

    /// Emits instructions needed before a (possibly captured) local variable
    /// definition. This should be called before compiling the value to be
    /// assigned. compile_define should be called after. Both should be called
    /// before the next variable definition. These function can't be used with
    /// a normal assignment or "local" statement which has multiple expressions
    /// on the left or right.
    fn compile_define_prepare(&mut self, var: &Var) {
        if var.kind == VarKind::Capture {
            let ti = self.ensure_type(Type::NanBox);
            self.asm.alloc(ti);
            self.asm.dup();
        }
    }

    /// Emits instructions needed for a local variable definition. This should
    /// be called after compile_define_prepare and after compiling the value
    /// to be assigned.
    fn compile_define(&mut self, var: &Var) {
        match var.kind {
            VarKind::Global | VarKind::Parameter => unreachable!(),
            VarKind::Local => {
                // When a local variable is defined, it's always assigned
                // to the top of the stack. Since the value being assigned
                // is already there, we don't need to emit an instruction.
            }
            VarKind::Capture => {
                // When a captured variable is defined, a cell should have
                // been allocated earlier with compile_define_prepare.
                self.asm.mode(inst::MODE_LUA);
                self.asm.store();
            }
        }
    }

    /// Like compile_define, but intended to be called as part of a definition
    /// of multiple local variables, as in a local or for-in statement.
    /// compile_define_prepare should not be called first in this case.
    fn compile_define_from_list(&mut self, var: &Var) {
        match var.kind {
            VarKind::Global | VarKind::Parameter => unreachable!(),
            VarKind::Local => {
                // We've arranged for the adjusted list of values to
                // be evaluated into place, so there's no need for
                // a storelocal instruction.
            }
            VarKind::Capture => {
                // The value is in the slot where the cell should
                // go. Allocate a cell, store the value, and put
                // the cell in that slot.
                assert_eq!(var.slot, var.cell_slot);
                let ti = self.ensure_type(Type::NanBox);
                self.asm.alloc(ti);
                self.asm.dup();
                self.asm.loadlocal(var.slot as u16);
                self.asm.mode(inst::MODE_LUA);
                self.asm.store();
                self.asm.storelocal(var.slot as u16);
            }
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
                        let var = &self.scope_set.vars[vid.0];
                        self.compile_store_var(var, var_use.cell);
                    }
                    None => {
                        self.asm.loadimportglobal(0, 0); // _ENV
                        self.asm.swap();
                        let si = self.ensure_string(name.text.as_bytes(), name.pos());
                        self.asm.mode(inst::MODE_LUA);
                        self.asm.storenamedprop(si);
                    }
                }
            }
            LValue::Dot { name, .. } => {
                let si = self.ensure_string(name.text.as_bytes(), name.pos());
                self.asm.mode(inst::MODE_LUA);
                self.asm.storenamedprop(si);
            }
            LValue::Index { .. } => {
                self.asm.mode(inst::MODE_LUA);
                self.asm.storeindexprop();
            }
        }
    }

    fn compile_store_var_prepare(&mut self, _: &Var) {
        // TODO: for captured variables, load the cell
    }

    fn compile_store_var(&mut self, var: &Var, var_use_cell: Option<usize>) {
        debug_assert!(!self.in_handler); // Close handlers don't store variables.
        match var.kind {
            VarKind::Global => {
                if var.slot == 0 {
                    // Assignment to _ENV has no effect.
                    self.asm.pop();
                } else {
                    // Assignment to _G.
                    assert_eq!(var.slot, 1);
                    self.asm.storeimportglobal(0, 1);
                }
            }
            VarKind::Parameter => {
                self.asm.storearg(var.slot.try_into().unwrap());
            }
            VarKind::Local => {
                self.asm.storelocal(var.slot.try_into().unwrap());
            }
            VarKind::Capture => {
                if let Some(cell) = var_use_cell {
                    self.asm.capture(cell.try_into().unwrap());
                } else {
                    self.asm.loadlocal(var.cell_slot.try_into().unwrap());
                }
                self.asm.swap();
                self.asm.mode(inst::MODE_LUA);
                self.asm.store();
            }
        }
    }

    fn compile_var_use(&mut self, name: &Token<'src>, var_use: &VarUse) {
        if let Some(vid) = var_use.var {
            let var = &self.scope_set.vars[vid.0];
            self.compile_load_var(var, var_use.cell);
        } else {
            self.asm.loadimportglobal(0, 0); // _ENV
            let si = self.ensure_string(name.text.as_bytes(), name.pos());
            self.asm.mode(inst::MODE_LUA);
            self.asm.loadnamedpropornil(si);
        }
    }

    fn compile_load_var(&mut self, var: &Var, var_use_cell: Option<usize>) {
        match var.kind {
            VarKind::Global => self.asm.loadimportglobal(0, var.slot.try_into().unwrap()),
            VarKind::Parameter if self.in_handler => {
                self.asm.loadargparent(var.slot.try_into().unwrap())
            }
            VarKind::Parameter => self.asm.loadarg(var.slot.try_into().unwrap()),
            VarKind::Local if self.in_handler => {
                self.asm.loadlocalparent(var.slot.try_into().unwrap())
            }
            VarKind::Local => self.asm.loadlocal(var.slot.try_into().unwrap()),
            VarKind::Capture => {
                if let Some(cell) = var_use_cell {
                    self.asm.capture(cell.try_into().unwrap());
                } else if self.in_handler {
                    self.asm.loadlocalparent(var.cell_slot.try_into().unwrap());
                } else {
                    self.asm.loadlocal(var.cell_slot.try_into().unwrap());
                }
                self.asm.load();
            }
        }
    }

    /// Emits code to check that the value on the top of the stack is closable.
    /// The value on top of the stack is consumed. It must be nil, false, or
    /// have a metatable with a non-nil __close property. The __close property
    /// need not be callable at this point.
    fn compile_check_closable(&mut self, message: &[u8], pos: Pos) {
        self.asm.dup();
        self.asm.mode(inst::MODE_LUA);
        self.asm.not();
        let mut is_nil_label = Label::new();
        self.asm.mode(inst::MODE_LUA);
        self.asm.bif(&mut is_nil_label);
        self.asm.mode(inst::MODE_LUA);
        self.asm.loadprototype();
        self.asm.dup();
        self.asm.constzero();
        self.asm.mode(inst::MODE_PTR);
        self.asm.nanbox();
        self.asm.eq();
        let mut close_missing_label = Label::new();
        self.asm.bif(&mut close_missing_label);
        let close_si = self.ensure_string(b"__close", pos);
        self.asm.mode(inst::MODE_LUA);
        self.asm.loadnamedpropornil(close_si);
        self.asm.constzero();
        self.asm.mode(inst::MODE_PTR);
        self.asm.nanbox();
        self.asm.ne();
        let mut close_ok_label = Label::new();
        self.asm.bif(&mut close_ok_label);
        self.asm.bind(&mut close_missing_label);
        let error_si = self.ensure_string(message, pos);
        self.asm.string(error_si);
        self.asm.mode(inst::MODE_STRING);
        self.asm.panic(0);
        self.asm.bind(&mut is_nil_label);
        self.asm.pop();
        self.asm.bind(&mut close_ok_label);
    }

    fn ensure_string(&mut self, s: &[u8], pos: Pos) -> u32 {
        if !self.enabled() {
            return !0;
        }
        match self.string_index.get(s) {
            Some(&i) => i,
            None => {
                let i: u32 = match self.strings.len().try_into() {
                    Ok(i) => i,
                    _ => {
                        self.error(pos, String::from("too many strings"));
                        !0
                    }
                };
                self.strings.push(Vec::from(s));
                self.string_index.insert(Vec::from(s), i);
                i
            }
        }
    }

    fn ensure_type(&mut self, t: Type) -> u32 {
        if !self.enabled() {
            return !0;
        }
        match self.type_index.get(&t) {
            Some(&i) => i,
            None => {
                let i: u32 = match self.types.len().try_into() {
                    Ok(i) => i,
                    _ => {
                        self.error(Pos::default(), String::from("too many types"));
                        !0
                    }
                };
                self.type_index.insert(t.clone(), i);
                self.types.push(t);
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

    fn check_slot(&mut self, index: usize, pos: Pos, kinds: &str) -> u16 {
        index.try_into().unwrap_or_else(|_| {
            self.error(pos, format!("too many {}", kinds));
            !0
        })
    }

    fn bind_named_label(&mut self, lid: LabelID) {
        self.ensure_label(lid);
        self.asm.bind(&mut self.named_labels[lid.0]);
    }

    fn b_named_label(&mut self, lid: LabelID) {
        self.ensure_label(lid);
        self.asm.b(&mut self.named_labels[lid.0]);
    }

    fn enter_block(&mut self, sid: ScopeID, pos: Pos) {
        self.block_stack.push(Block {
            sid,
            enabled: self.enabled(),
            closes: Vec::new(),
            pos,
        })
    }

    /// Emits code for leaving a local block. In most cases, this just pops
    /// slots for local variables, but for "close" variables, it also calls and
    /// pops error handlers that call their __close metamethods. goto, return,
    /// and break statements do some of this, too, but the actual handlers
    /// are only emitted once, here.
    fn leave_block(&mut self) {
        let mut block = self.block_stack.pop().unwrap();
        let scope = &self.scope_set.scopes[block.sid.0];
        self.compile_pop_slots_and_handlers(scope.slot_count(), scope.handler_count());
        if !block.closes.is_empty() {
            let mut after_handlers_label = Label::new();
            self.asm.b(&mut after_handlers_label);
            self.in_handler = true;
            let was_enabled = self.enabled();
            if block.enabled {
                // If the block contains closes and is reachable but contains a
                // break, goto, or return statement that disables code
                // generation, re-enable code generation to emit code to call
                // the close functions.
                self.set_enabled(true);
            }
            for close in block.closes.iter_mut().rev() {
                self.asm.bind(&mut close.label);
                let var = &self.scope_set.vars[close.vid.0];
                self.compile_load_var(var, None);
                self.asm.mode(inst::MODE_LUA);
                self.asm.not();
                let mut after_close_label = Label::new();
                self.asm.mode(inst::MODE_LUA);
                self.asm.bif(&mut after_close_label);
                self.compile_load_var(var, None);
                self.asm.dup();
                self.asm.mode(inst::MODE_LUA);
                self.asm.loadprototype();
                let close_si = self.ensure_string(b"__close", block.pos);
                self.asm.mode(inst::MODE_LUA);
                self.asm.loadnamedprop(close_si);
                self.asm.swap();
                self.asm.mode(inst::MODE_LUA);
                self.asm.loaderror();
                self.asm.mode(inst::MODE_LUA);
                self.asm.callvalue(2);
                self.asm.mode(inst::MODE_LUA);
                self.asm.adjustv(0);
                self.asm.bind(&mut after_close_label);
                self.asm.nexthandler();
            }
            self.set_enabled(was_enabled);
            self.in_handler = false;
            self.asm.bind(&mut after_handlers_label);
        }
    }

    fn add_close(&mut self, close_vid: VarID, handler_label: Label) {
        if !self.enabled() {
            return;
        }
        let block = self.block_stack.last_mut().unwrap();
        block.closes.push(Close {
            vid: close_vid,
            label: handler_label,
        });
    }

    /// Returns true if the code being compiled may be reachable, and
    /// instructions are being emitted.
    fn enabled(&self) -> bool {
        self.asm.enabled()
    }

    /// Allows or prevents the assembler from emitting instructions, depending
    /// on whether the code being compiled is reachable or unreachabe.
    /// set_enabled(false) should be called after return, break, and goto
    /// statements. set_enabled(true) should be called at any point where
    /// control flows merge and at least one predecessor block is reachable.
    fn set_enabled(&mut self, enabled: bool) {
        self.asm.set_enabled(enabled);
    }

    fn compile_pop_slots_and_handlers(&mut self, slot_count: usize, handler_count: usize) {
        for _ in 0..handler_count {
            self.asm.callhandler();
        }
        for _ in 0..slot_count {
            self.asm.pop();
        }
    }

    fn push_func(&mut self, mut param_count: u16, mut is_variadic: bool) {
        let mut asm = Assembler::new();
        mem::swap(&mut self.asm, &mut asm);
        mem::swap(&mut self.param_count, &mut param_count);
        mem::swap(&mut self.is_variadic, &mut is_variadic);
        if !asm.enabled() {
            let si = self.ensure_string(b"unreachable", Pos::default());
            self.asm.string(si);
            self.asm.mode(inst::MODE_STRING);
            self.asm.panic(0);
            self.asm.set_enabled(false);
        }
        self.func_stack.push(FuncState {
            asm,
            param_count,
            is_variadic,
        });
    }

    fn pop_func(&mut self) -> Assembler {
        let mut state = self.func_stack.pop().unwrap();
        mem::swap(&mut self.asm, &mut state.asm);
        mem::swap(&mut self.param_count, &mut state.param_count);
        mem::swap(&mut self.is_variadic, &mut state.is_variadic);
        state.asm
    }

    fn line(&mut self, pos: Pos) {
        let e = self.lmap.encode_line(pos);
        self.asm.line(e);
    }

    fn error(&mut self, pos: Pos, message: String) {
        self.errors.push(Error {
            position: self.lmap.position(pos),
            message,
        })
    }
}

/// Indicates what to do with the results of an expression.
enum ResultMode {
    /// The results should be popped from the stack and ignored.
    /// Used by call statements.
    Drop,

    /// All results but the first should be popped. If the expression
    /// dynamically produces no results, nil is pushed. Used for call
    /// expressions and '...' that are not at the end of an expression list.
    Truncate,

    /// All results should be kept on the stack and vc should be set to the
    /// total number of values in the expression list. Used for call expressions
    /// and '...' at the end of an expression list.
    Append,
}

/// Indicates whether an expression list produces a statically-known number
/// of values.
#[derive(Eq, PartialEq)]
enum ExprListLen {
    Static(u16),
    Dynamic,
}

struct Block {
    sid: ScopeID,
    enabled: bool,
    closes: Vec<Close>,
    pos: Pos,
}

struct Close {
    vid: VarID,
    label: Label,
}
