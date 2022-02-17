use crate::data::{self, List, SetValue, Slice};
use crate::heap::Handle;
use crate::inst::{self, Assembler, Label};
use crate::lua::scope::{self, CaptureFrom, ScopeSet, Var, VarKind, VarUse};
use crate::lua::syntax::{
    self, Call, Chunk, Expr, LValue, LabelID, Param, ScopeID, Stmt, TableField, VarID,
};
use crate::lua::token::{self, Number, Token};
use crate::nanbox;
use crate::package::{Function, Global, ImportGlobal, ImportPackage, Object, Package, Type};
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
) -> Option<Box<Package>> {
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
    strings: Handle<List<data::String>>,
    string_index: Handle<data::HashMap<data::String, SetValue<u32>>>,
    named_labels: Vec<inst::Label>,
    asm: Assembler,
    param_count: u16,
    is_variadic: bool,
    func_stack: Vec<FuncState>,
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
            strings: Handle::new(List::alloc()),
            string_index: Handle::new(data::HashMap::alloc()),
            named_labels: Vec::new(),
            asm: Assembler::new(),
            param_count: 0,
            is_variadic: false,
            func_stack: Vec::new(),
            errors,
        }
    }

    fn finish(mut self) -> Option<Box<Package>> {
        self.asm.mode(inst::MODE_LUA);
        self.asm.setv(0);
        self.asm.mode(inst::MODE_LUA);
        self.asm.retv();
        match self.asm.finish() {
            Ok((insts, line_map)) => {
                self.functions.push(Function {
                    name: String::from("·init"),
                    insts,
                    package: 0 as *mut Package,
                    param_types: Vec::new(),
                    var_param_type: None,
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

        let imports = vec![ImportPackage::new(
            String::from("luastd"),
            vec![
                ImportGlobal::new(String::from("_ENV")),
                ImportGlobal::new(String::from("_G")),
            ],
            Vec::new(),
        )];
        let mut package = Box::new(Package {
            name: self.name,
            globals: self.globals,
            functions: self.functions,
            strings: Handle::empty(),
            line_map: PackageLineMap::from(self.lmap),
            imports,
        });
        package.strings = Handle::new(Slice::alloc());
        package.strings.init_from_list(&self.strings);
        Some(package)
    }

    fn compile_chunk(&mut self, chunk: &Chunk<'src>) {
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

                // Compile the expressions on the right, then adjust the number
                // of values to match the number of expressions on the left.
                let len_known = self.compile_expr_list(right, 0);
                self.compile_adjust(right.len(), len_known, left.len(), stmt.pos());

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
                self.compile_adjust(right.len(), len_known, left.len(), *pos);

                for l in left {
                    let var = &self.scope_set.vars[l.var.0];
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
                            self.asm.alloc(mem::size_of::<usize>() as u32);
                            self.asm.dup();
                            self.asm.loadlocal(var.slot as u16);
                            self.asm.mode(inst::MODE_LUA);
                            self.asm.store();
                            self.asm.storelocal(var.slot as u16);
                        }
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
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.not();
                    self.asm.mode(inst::MODE_LUA);
                    self.asm.bif(&mut next_label);
                    self.compile_stmt(stmt);
                    self.asm.b(&mut end_label);
                    self.asm.bind(&mut next_label);
                }
                if let Some(false_stmt) = false_stmt {
                    self.compile_stmt(false_stmt);
                }
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
                self.asm.b(&mut cond_label);
                self.asm.bind(&mut body_label);
                for stmt in body {
                    self.compile_stmt(stmt);
                }
                self.pop_block(*scope);
                self.asm.bind(&mut cond_label);
                self.compile_expr(cond);
                self.asm.mode(inst::MODE_LUA);
                self.asm.bif(&mut body_label);
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
                self.asm.bind(&mut body_label);
                for stmt in body {
                    self.compile_stmt(stmt);
                }
                self.compile_expr(cond);
                self.asm.mode(inst::MODE_LUA);
                self.asm.not();
                let slot_count = self.scope_set.scopes[scope.0].slot_count;
                for _ in 0..slot_count {
                    self.asm.swap();
                    self.asm.pop();
                }
                self.asm.mode(inst::MODE_LUA);
                self.asm.bif(&mut body_label);
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
                self.compile_define_prepare(body_var);
                self.compile_load_var(ind_var, None);
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
                self.asm.mode(inst::MODE_LUA);
                self.asm.ge();
                self.asm.mode(inst::MODE_LUA);
                self.asm.bif(&mut body_label);

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
                        self.asm.pop();
                    }
                    self.ensure_label(lid);
                    self.asm.b(&mut self.named_labels[lid.0]);
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
                            self.asm.pop();
                        }
                    }
                    self.ensure_label(lid);
                    self.asm.b(&mut self.named_labels[lid.0]);
                }
            }
            Stmt::Function {
                name,
                is_variadic,
                parameters,
                param_scope,
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
                is_variadic,
                body,
                var: vid,
                pos,
                ..
            } => {
                let var = &self.scope_set.vars[vid.0];
                self.compile_define_prepare(var);
                let name = String::from(name_tok.text);
                let fn_index =
                    self.compile_function(name, None, parameters, *is_variadic, body, *pos);
                self.compile_closure(fn_index, *param_scope, *pos);
                self.compile_define(var);
            }
            Stmt::Call(call) => {
                self.compile_call(call, ResultMode::Drop);
            }
            Stmt::Return { exprs, pos, .. } => {
                // TODO: support tail calls.
                // TODO: disable code generation after return.
                // Compile the expressions to return. If the last expression is
                // a call or '...', we don't statically know the number of
                // values being returned, but compile_expr_list will set the
                // vc register for us. If we do statically know, we need to
                // use setv explicitly. In either case, vc is set to the number
                // of returned values, so the caller knows what to do with them.
                match self.compile_expr_list(exprs, 0) {
                    ExprListLen::Static => {
                        let n = match exprs.len().try_into() {
                            Ok(n) => n,
                            Err(_) => {
                                self.error(*pos, String::from("too many return values"));
                                !0
                            }
                        };
                        self.asm.mode(inst::MODE_LUA);
                        self.asm.setv(n);
                    }
                    ExprListLen::Dynamic => (),
                }
                self.asm.mode(inst::MODE_LUA);
                self.asm.retv();
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
                    self.asm.mode(inst::MODE_LUA);
                    match op.kind {
                        token::Kind::Lt => self.asm.lt(),
                        token::Kind::LtEq => self.asm.le(),
                        token::Kind::Gt => self.asm.gt(),
                        token::Kind::GtEq => self.asm.ge(),
                        token::Kind::EqEq => self.asm.eq(),
                        token::Kind::TildeEq => self.asm.ne(),
                        token::Kind::Pipe => self.asm.or(),
                        token::Kind::Tilde => self.asm.xor(),
                        token::Kind::Amp => self.asm.and(),
                        token::Kind::LtLt => self.asm.shl(),
                        token::Kind::GtGt => self.asm.shr(),
                        token::Kind::DotDot => self.asm.strcat(),
                        token::Kind::Plus => self.asm.add(),
                        token::Kind::Minus => self.asm.sub(),
                        token::Kind::Star => self.asm.mul(),
                        token::Kind::Slash => self.asm.div(),
                        token::Kind::SlashSlash => self.asm.floordiv(),
                        token::Kind::Percent => self.asm.mod_(),
                        token::Kind::Caret => self.asm.exp(),
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
                is_variadic,
                body,
                pos,
                ..
            } => {
                let name = String::from("·anonymous");
                let fn_index =
                    self.compile_function(name, None, parameters, *is_variadic, body, *pos);
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
                self.asm.alloc(mem::size_of::<Object>() as u32);
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
        let static_expr_count = match (exprs.len() + extra).try_into() {
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
                ExprListLen::Dynamic
            }
            Some(expr) => {
                self.compile_expr(expr);
                ExprListLen::Static
            }
            None => ExprListLen::Static,
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
    fn compile_adjust(&mut self, expr_count: usize, len_known: ExprListLen, want: usize, pos: Pos) {
        match len_known {
            ExprListLen::Static => {
                if want > expr_count {
                    self.asm.constzero();
                    self.asm.mode(inst::MODE_PTR);
                    self.asm.nanbox();
                    for _ in 0..(want - expr_count - 1) {
                        self.asm.dup();
                    }
                } else {
                    for _ in 0..(expr_count - want) {
                        self.asm.pop();
                    }
                }
            }
            ExprListLen::Dynamic => {
                let want_narrow = match want.try_into() {
                    Ok(n) => n,
                    Err(_) => {
                        self.error(pos, String::from("too many expressions"));
                        !0
                    }
                };
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
        pos: Pos,
    ) -> u32 {
        // Start compiling the function.
        self.push_func(parameters.len().try_into().unwrap(), is_variadic);
        self.line(pos);

        // Move captured parameters into cells.
        let mut cell_slot = 0;
        let mut move_captured_param = |vid: VarID| {
            let var = &self.scope_set.vars[vid.0];
            if var.kind == VarKind::Capture {
                self.asm.alloc(mem::size_of::<usize>() as u32); // pointer to nanbox
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
        for stmt in body {
            self.compile_stmt(stmt);
        }

        // If the function didn't end with a return statement,
        // return nothing.
        self.asm.mode(inst::MODE_LUA);
        self.asm.setv(0);
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
            package: 0 as *mut Package,
            param_types,
            var_param_type,
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
        let static_arg_count = match call.arguments.len().try_into() {
            Ok(i) if call.method_name.is_some() => i + 1,
            Ok(i) => i,
            Err(_) => {
                self.error(call.pos, String::from("too many arguments"));
                !0
            }
        };
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
                ExprListLen::Static => self.asm.callnamedprop(si, static_arg_count),
                ExprListLen::Dynamic => self.asm.callnamedpropv(si),
            }
        } else {
            match arg_len {
                ExprListLen::Static => self.asm.callvalue(static_arg_count),
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
            self.asm.alloc(mem::size_of::<usize>() as u32);
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
            VarKind::Parameter => self.asm.loadarg(var.slot.try_into().unwrap()),
            VarKind::Local => self.asm.loadlocal(var.slot.try_into().unwrap()),
            VarKind::Capture => {
                if let Some(cell) = var_use_cell {
                    self.asm.capture(cell.try_into().unwrap());
                } else {
                    self.asm.loadlocal(var.cell_slot.try_into().unwrap());
                }
                self.asm.load();
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

    fn pop_block(&mut self, sid: ScopeID) {
        let scope = &self.scope_set.scopes[sid.0];
        for _ in 0..scope.slot_count {
            self.asm.pop();
        }
    }

    fn push_func(&mut self, mut param_count: u16, mut is_variadic: bool) {
        let mut asm = Assembler::new();
        mem::swap(&mut self.asm, &mut asm);
        mem::swap(&mut self.param_count, &mut param_count);
        mem::swap(&mut self.is_variadic, &mut is_variadic);
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
enum ExprListLen {
    Static,
    Dynamic,
}
