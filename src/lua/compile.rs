use crate::data::{self, List, SetValue, Slice};
use crate::heap::Handle;
use crate::inst::{self, Assembler};
use crate::lua::scope::{self, ScopeSet, VarKind, VarUse};
use crate::lua::syntax::{self, Chunk, Expr, LValue, Stmt};
use crate::lua::token::{self, Number, Token};
use crate::package::{Function, Global, Package, Type};
use crate::pos::{Error, ErrorList, LineMap, PackageLineMap, Pos, Position};

use std::fs;
use std::path::Path;

pub fn compile_file(path: &Path) -> Result<Box<Package>, ErrorList> {
    let data = fs::read(path).map_err(|err| {
        let position = Position::from(path);
        let wrapped = Error::wrap(position, &err);
        ErrorList(vec![wrapped])
    })?;
    let mut lmap = LineMap::new();
    let tokens = token::lex(path, &data, &mut lmap)?;
    let chunk = syntax::parse(&tokens, &lmap)?;
    let scope_set = scope::resolve(&chunk, &lmap)?;
    compile_chunk(&chunk, &scope_set, &lmap)
}

pub fn compile_chunk(
    chunk: &Chunk,
    scope_set: &ScopeSet,
    lmap: &LineMap,
) -> Result<Box<Package>, ErrorList> {
    let mut cmp = Compiler::new(scope_set, lmap);
    cmp.compile_chunk(chunk);
    cmp.finish()
}

struct Compiler<'src, 'ss, 'lm> {
    scope_set: &'ss ScopeSet<'src>,
    lmap: &'lm LineMap,
    globals: Vec<Global>,
    functions: Vec<Function>,
    strings: Handle<List<data::String>>,
    string_index: Handle<data::HashMap<data::String, SetValue<u32>>>,
    types: Vec<Type>,
    asm_stack: Vec<Assembler>,
    errors: Vec<Error>,
}

impl<'src, 'ss, 'lm> Compiler<'src, 'ss, 'lm> {
    fn new(scope_set: &'ss ScopeSet<'src>, lmap: &'lm LineMap) -> Compiler<'src, 'ss, 'lm> {
        Compiler {
            scope_set,
            lmap,
            globals: Vec::new(),
            functions: Vec::new(),
            strings: Handle::new(List::alloc()),
            string_index: Handle::new(data::HashMap::alloc()),
            types: Vec::new(),
            asm_stack: vec![Assembler::new()],
            errors: Vec::new(),
        }
    }

    fn finish(mut self) -> Result<Box<Package>, ErrorList> {
        self.asm().nil();
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
            return Err(ErrorList(self.errors));
        }

        let mut package = Box::new(Package {
            globals: self.globals,
            functions: Vec::new(),
            strings: Handle::empty(),
            types: self.types,
            line_map: PackageLineMap::from(self.lmap),
        });
        for f in &mut self.functions {
            f.package = &*package;
        }
        package.functions = self.functions;
        package.strings = Handle::new(Slice::alloc());
        package.strings.init_from_list(&self.strings);
        Ok(package)
    }

    fn compile_chunk(&mut self, chunk: &Chunk<'src>) {
        // Create the global object.
        let env_var = &self.scope_set.vars[chunk.env_var.0];
        assert_eq!(env_var.slot, 0);
        self.globals.push(Global {
            name: String::from("_ENV"),
        });
        let ti = self.ensure_type(Type::Object, chunk.pos());
        self.asm().alloc(ti);
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
                        self.asm().nil();
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
            Stmt::Print { expr, .. } => {
                self.compile_expr(expr);
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
                        self.asm().nil();
                    }
                    token::Kind::True => {
                        self.asm().true_();
                    }
                    token::Kind::False => {
                        self.asm().false_();
                    }
                    token::Kind::Number => {
                        self.compile_number(t);
                    }
                    token::Kind::String => {
                        self.compile_string(t);
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
        }
    }

    fn compile_lvalue(&mut self, lval: &LValue<'src>) {
        self.line(lval.pos());
        // TODO: evaluate expressions that produce tables into which we're
        // storing fields. For now, no expression does that.
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
                                // TODO: implemnt assign to capture.
                                unimplemented!();
                            }
                        }
                    }
                    None => {
                        self.asm().loadglobal(0); // _ENV
                        self.asm().swap();
                        let si = self.ensure_string(name.text.as_bytes(), name.pos());
                        self.asm().storenamedprop(si);
                    }
                }
            }
        }
    }

    fn compile_var_use(&mut self, name: &Token<'src>, var_use: &VarUse) {
        if let Some(vid) = var_use.var {
            let var = &self.scope_set.vars[vid.0];
            match var.kind {
                VarKind::Global => self.asm().loadglobal(var.slot.try_into().unwrap()),
                VarKind::Parameter => self.asm().loadarg(var.slot.try_into().unwrap()),
                VarKind::Local => self.asm().loadlocal(var.slot.try_into().unwrap()),
                VarKind::Capture => {
                    // TODO: implement load from capture.
                    unimplemented!();
                }
            }
        } else {
            self.asm().loadglobal(0); // _ENV
            let si = self.ensure_string(name.text.as_bytes(), name.pos());
            self.asm().loadnamedpropornil(si);
        }
    }

    fn compile_number(&mut self, t: &Token<'src>) {
        match token::convert_number(t.text) {
            Number::Int(n) => {
                self.asm().int64(n);
                self.asm().nanbox();
            }
            Number::Float(n) => {
                self.asm().float64(n);
                self.asm().nanbox();
            }
            Number::Malformed => {
                self.error(t.pos(), format!("malformed number"));
            }
        }
    }

    fn compile_string(&mut self, t: &Token<'src>) {
        let s = match token::unquote_string(t.text) {
            Some(s) => s,
            None => {
                self.error(t.pos(), format!("malformed string"));
                return;
            }
        };
        let si = self.ensure_string(&s, t.pos());
        self.asm().string(si);
        self.asm().nanbox();
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

    fn ensure_type(&mut self, type_: Type, pos: Pos) -> u32 {
        // TODO: deduplicate types.
        let i: u32 = match self.types.len().try_into() {
            Ok(i) => i,
            _ => {
                self.error(pos, String::from("too many types"));
                return !0;
            }
        };
        self.types.push(type_);
        i
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
