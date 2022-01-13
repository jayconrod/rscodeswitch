use crate::data;
use crate::heap::HEAP;
use crate::inst;
use crate::nanbox;
use crate::package::{Closure, Function, Object, Type};

use std::error;
use std::fmt;
use std::io::Write;
use std::mem;

// Each stack frame consists of (with descending stack address):
//
//   - Caller: *const Function
//   - Caller's cells: *[*mut u64; ?]
//   - Return address: *const u8
//   - Caller's fp
const FRAME_SIZE: usize = 32;

pub struct Interpreter<'a> {
    w: &'a mut dyn Write,
    global_slots: Vec<u64>,
}

impl<'a> Interpreter<'a> {
    pub fn new(w: &'a mut dyn Write) -> Interpreter<'a> {
        Interpreter {
            w,
            global_slots: Vec::new(),
        }
    }

    pub fn interpret(&mut self, mut func: &Function) -> Result<(), Error> {
        unsafe {
            assert!(func.param_types.is_empty());
            let mut pp = func.package.as_ref().unwrap();
            if self.global_slots.is_empty() {
                self.global_slots.resize(pp.globals.len(), 0);
            }
            let mut cp = 0 as *mut *mut u64;

            let mut stack = Stack::new();
            let mut sp = stack.end() - FRAME_SIZE;
            let mut fp = sp;
            let mut ip = &func.insts[0] as *const u8;
            let mut types = Vec::new();

            *((fp + 24) as *mut u64) = 0; // caller
            *((fp + 16) as *mut u64) = 0; // caller's cells
            *((fp + 8) as *mut u64) = 0; // return address
            *(fp as *mut u64) = 0; // caller's fp

            macro_rules! return_errorf {
                ($($x:expr),*) => {
                    return Err(Error{message: format!($($x,)*)})
                };
            }

            macro_rules! pop {
                () => {{
                    let v = *(sp as *mut u64);
                    sp += 8;
                    (v, types.pop().unwrap())
                }};
                ($t:expr) => {{
                    let top = types.pop().unwrap();
                    if top != $t {
                        return_errorf!("unexpected type {}", top);
                    }
                    let v = *(sp as *mut u64);
                    sp += 8;
                    v
                }};
            }

            macro_rules! pop_cond {
                () => {{
                    let (v, ty) = pop!();
                    match ty {
                        Type::Bool => v != 0,
                        Type::Nanbox => {
                            if let Some(b) = nanbox::to_bool(v) {
                                b
                            } else {
                                return_errorf!(
                                    "condition must be bool value (got {})",
                                    nanbox::debug_type(v)
                                );
                            }
                        }
                        _ => unreachable!(),
                    }
                }};
            }

            macro_rules! push {
                ($x:expr, $t:expr) => {{
                    sp -= 8;
                    *(sp as *mut u64) = $x;
                    types.push($t);
                }};
            }

            macro_rules! binop_eq {
                ($op:tt) => {{
                    let (r, ty) = pop!();
                    let l = pop!(ty);
                    match ty {
                        Type::Nil => {
                            return_errorf!("binary operator used with nil operand");
                        }
                        Type::Bool | Type::Function | Type::Closure | Type::Object | Type::Pointer(_) => {
                            push!((l $op r) as u64, Type::Bool);
                        }
                        Type::Float64 => {
                            // Float comparison can't use raw bit comparison
                            // because NaN != NaN.
                            let l = f64::from_bits(l);
                            let r = f64::from_bits(r);
                            push!((l $op r) as u64, Type::Bool);
                        }
                        Type::String => {
                            let l = (l as *const data::String).as_ref().unwrap();
                            let r = (r as *const data::String).as_ref().unwrap();
                            push!((l $op r) as u64, Type::Bool);
                        }
                        Type::Nanbox => {
                            let v = if nanbox::is_nil(l) && nanbox::is_nil(r) {
                                true $op true
                            } else if let (Some(lb), Some(rb)) = (nanbox::to_bool(l), nanbox::to_bool(r)) {
                                lb $op rb
                            } else if let (Some(ln), Some(rn)) = (nanbox::to_f64(l), nanbox::to_f64(r)) {
                                ln $op rn
                            } else if let (Some(ls), Some(rs)) = (nanbox::to_string(l), nanbox::to_string(r)) {
                                ls $op rs
                            } else if let (Some(lf), Some(rf)) = (nanbox::to_closure(l), nanbox::to_closure(r)) {
                                lf $op rf
                            } else if let (Some(lo), Some(ro)) = (nanbox::to_object(l), nanbox::to_object(r)) {
                                lo $op ro
                            } else {
                                true $op false
                            };
                            push!(v as u64, Type::Bool);
                        }
                    }
                }};
            }

            macro_rules! binop_cmp {
                ($op:tt) => {{
                    let (r, ty) = pop!();
                    let l = pop!(ty);
                    match ty {
                        Type::Float64 => {
                            let l = f64::from_bits(l);
                            let r = f64::from_bits(r);
                            push!((l $op r) as u64, Type::Bool);
                        }
                        Type::String => {
                            let l = (l as *const data::String).as_ref().unwrap();
                            let r = (r as *const data::String).as_ref().unwrap();
                            push!((l $op r) as u64, Type::Bool);
                        }
                        Type::Nanbox => {
                            let v = if let (Some(ln), Some(rn)) = (nanbox::to_f64(l), nanbox::to_f64(r)) {
                                ln $op rn
                            } else if let (Some(ls), Some(rs)) = (nanbox::to_string(l), nanbox::to_string(r)) {
                                ls $op rs
                            } else {
                                return_errorf!("comparison operands must both be strings or numbers (got {}, {})", nanbox::debug_type(l), nanbox::debug_type(l))
                            };
                            push!(v as u64, Type::Bool);
                        }
                        _ => unreachable!(),
                    }
                }}
            }

            macro_rules! binop_num {
                ($op:tt) => {{
                    let (r, ty) = pop!();
                    let l = pop!(ty);
                    match ty {
                        Type::Float64 => {
                            let l = f64::from_bits(l);
                            let r = f64::from_bits(r);
                            push!((l $op r) as u64, Type::Float64);
                        }
                        Type::Nanbox => {
                            let v = if let (Some(ln), Some(rn)) = (nanbox::to_f64(l), nanbox::to_f64(r)) {
                                nanbox::from_f64(ln $op rn)
                            } else {
                                return_errorf!("arithmetic operands must both be numbers (got {}, {})", nanbox::debug_type(l), nanbox::debug_type(r));
                            };
                            push!(v, Type::Nanbox)
                        }
                        _ => unreachable!(),
                    }
                }};
            }

            loop {
                match *ip {
                    inst::ADD => {
                        let (r, ty) = pop!();
                        let l = pop!(ty);
                        match ty {
                            Type::Float64 => {
                                let l = f64::from_bits(l);
                                let r = f64::from_bits(r);
                                push!((l + r) as u64, Type::Float64);
                            }
                            Type::String => {
                                let l = (l as *const data::String).as_ref().unwrap();
                                let r = (r as *const data::String).as_ref().unwrap();
                                push!((l + r) as u64, Type::String);
                            }
                            Type::Nanbox => {
                                let v = if let (Some(ln), Some(rn)) =
                                    (nanbox::to_f64(l), nanbox::to_f64(r))
                                {
                                    nanbox::from_f64(ln + rn)
                                } else if let (Some(ls), Some(rs)) =
                                    (nanbox::to_string(l), nanbox::to_string(r))
                                {
                                    let ls = ls.as_ref().unwrap();
                                    let rs = rs.as_ref().unwrap();
                                    nanbox::from_string(ls + rs)
                                } else {
                                    return_errorf!(
                                        "arithmetic operands must both be numbers (got {}, {})",
                                        nanbox::debug_type(l),
                                        nanbox::debug_type(r)
                                    );
                                };
                                push!(v, Type::Nanbox)
                            }
                            _ => unreachable!(),
                        }
                    }
                    inst::ALLOC => {
                        let i = u32::from_le_bytes(*((ip as usize + 1) as *const [u8; 4]));
                        let ty = pp.types[i as usize].clone();
                        let p = HEAP.allocate(ty.size()) as u64;
                        push!(p, ty);
                    }
                    inst::B => {
                        let delta = i32::from_le_bytes(*((ip as usize + 1) as *const [u8; 4]));
                        ip = ((ip as isize) + 1 + delta as isize) as *const u8;
                        continue;
                    }
                    inst::BIF => {
                        if pop_cond!() {
                            let delta = i32::from_le_bytes(*((ip as usize + 1) as *const [u8; 4]));
                            ip = ((ip as isize) + 1 + delta as isize) as *const u8;
                            continue;
                        }
                    }
                    inst::CALLVALUE => {
                        let arg_count = i16::from_le_bytes(*((ip as usize + 1) as *const [u8; 2]));
                        let raw_callee = *((sp as usize + arg_count as usize * 8) as *const u64);
                        let (callee, cells) = match types[types.len() - arg_count as usize - 1] {
                            Type::Function => {
                                let f = (raw_callee as *const Function).as_ref().unwrap();
                                (f, 0 as *mut *mut u64)
                            }
                            Type::Closure => {
                                let c = (raw_callee as *const Closure).as_ref().unwrap();
                                (&*c.function, c.cell_addr(0))
                            }
                            Type::Nanbox => {
                                if let Some(c) = nanbox::to_closure(raw_callee) {
                                    let c = c.as_ref().unwrap();
                                    (&*c.function, c.cell_addr(0))
                                } else {
                                    return_errorf!(
                                        "call of non-function ({})",
                                        nanbox::debug_type(raw_callee)
                                    )
                                }
                            }
                            _ => unreachable!(),
                        };
                        sp -= FRAME_SIZE;
                        *((sp as usize + 24) as *mut u64) = func as *const Function as u64;
                        func = callee;
                        *((sp as usize + 16) as *mut u64) = cp as u64;
                        cp = cells;
                        *((sp as usize + 8) as *mut u64) = (ip as u64) + 3;
                        ip = &func.insts[0] as *const u8;
                        *(sp as *mut u64) = fp as u64;
                        fp = sp;
                        pp = callee.package.as_ref().unwrap();
                        continue;
                    }
                    inst::CELL => {
                        let i = i16::from_le_bytes(*((ip as usize + 1) as *const [u8; 2])) as usize;
                        let cell = *((cp as usize + i * mem::size_of::<usize>()) as *const u64);
                        let ty = func.cell_types[i].clone();
                        push!(cell, ty);
                    }
                    inst::DIV => {
                        binop_num!(/);
                    }
                    inst::DUP => {
                        let v = *(sp as *mut u64);
                        sp -= 8;
                        *(sp as *mut u64) = v;
                        types.push(types[types.len() - 1].clone());
                    }
                    inst::EQ => {
                        binop_eq!(==)
                    }
                    inst::FUNCTION => {
                        let i = u32::from_le_bytes(*((ip as usize + 1) as *const [u8; 4])) as usize;
                        let f = &pp.functions[i] as *const Function as u64;
                        push!(f, Type::Function);
                    }
                    inst::GE => {
                        binop_cmp!(>=)
                    }
                    inst::GT => {
                        binop_cmp!(>)
                    }
                    inst::LE => {
                        binop_cmp!(<=)
                    }
                    inst::FALSE => {
                        push!(0, Type::Bool);
                    }
                    inst::FLOAT64 => {
                        let n = f64::from_le_bytes(*((ip as usize + 1) as *const [u8; 8]));
                        push!(n.to_bits(), Type::Float64);
                    }
                    inst::LOAD => {
                        let (p, pty) = pop!();
                        let ty = match pty {
                            Type::Pointer(ty) => ty,
                            _ => unreachable!(),
                        };
                        let v = *(p as *const u64);
                        push!(v, *ty);
                    }
                    inst::LOADARG => {
                        let ai =
                            u16::from_le_bytes(*((ip as usize + 1) as *const [u8; 2])) as usize;
                        let si = func.param_types.len() - ai - 1;
                        let v = *((fp + FRAME_SIZE + si * 8) as *const u64);
                        push!(v, func.param_types[ai].clone());
                    }
                    inst::LOADGLOBAL => {
                        let i = *((ip as usize + 1) as *const u32) as usize;
                        let v = self.global_slots[i];
                        push!(v, Type::Nanbox);
                    }
                    inst::LT => {
                        binop_cmp!(<)
                    }
                    inst::LOADLOCAL => {
                        let i = *((ip as usize + 1) as *const u16) as usize;
                        let v = *((fp as usize - (i + 1) * 8) as *const u64);
                        let stack_depth = (fp - sp) / 8;
                        let ty = types[types.len() - stack_depth + i].clone();
                        push!(v, ty);
                    }
                    inst::LOADNAMEDPROP => {
                        let i = *((ip as usize + 1) as *const u32) as usize;
                        let name = &pp.strings[i];
                        let (r, ty) = pop!();
                        match ty {
                            Type::Object => {
                                // TODO: figure out where the property is based
                                // on its static type. We need to know the
                                // type of the property itself, too.
                                unimplemented!();
                            }
                            Type::Nanbox => {
                                let o = if let Some(o) = nanbox::to_object(r) {
                                    o.as_ref().unwrap()
                                } else {
                                    return_errorf!(
                                        "value is not an object: {}",
                                        nanbox::debug_type(r)
                                    );
                                };
                                let prop = if let Some(prop) = o.property(name) {
                                    prop
                                } else {
                                    return_errorf!("object does not have property '{}'", &name);
                                };
                                push!(prop, Type::Nanbox);
                            }
                            _ => {
                                return_errorf!("value is not an object: {}", ty);
                            }
                        }
                    }
                    inst::LOADPROTOTYPE => {
                        let (v, ty) = pop!();
                        let p = match ty {
                            Type::Object => {
                                let o = (v as *const Object).as_ref().unwrap();
                                o.prototype.unwrap()
                            }
                            Type::Nanbox => {
                                if let Some(o) = nanbox::to_object(v) {
                                    let o = o.as_ref().unwrap();
                                    o.prototype.unwrap()
                                } else {
                                    return_errorf!(
                                        "value is not an object: {}",
                                        nanbox::debug_type(v)
                                    )
                                }
                            }
                            _ => {
                                return_errorf!("value is not an object: {}", ty);
                            }
                        };
                        push!(p as *const Object as u64, Type::Object);
                    }
                    inst::MUL => {
                        binop_num!(*)
                    }
                    inst::NANBOX => {
                        let (v, ty) = pop!();
                        let b = match ty {
                            Type::Nil => nanbox::from_nil(),
                            Type::Bool => nanbox::from_bool(v != 0),
                            Type::String => {
                                let s = v as *const data::String;
                                nanbox::from_string(s)
                            }
                            Type::Closure => {
                                let f = v as *const Closure;
                                nanbox::from_closure(f)
                            }
                            Type::Object => {
                                let o = v as *const Object;
                                nanbox::from_object(o)
                            }
                            Type::Float64 | Type::Nanbox => v,
                            _ => unreachable!(),
                        };
                        push!(b, Type::Nanbox);
                    }
                    inst::NE => {
                        binop_eq!(!=)
                    }
                    inst::NEG => {
                        let (v, ty) = pop!();
                        match ty {
                            Type::Float64 => {
                                let vn = f64::from_bits(v);
                                push!((-vn).to_bits(), Type::Float64);
                            }
                            Type::Nanbox => {
                                if let Some(vn) = nanbox::to_f64(v) {
                                    push!(nanbox::from_f64(-vn), Type::Nanbox);
                                } else {
                                    return_errorf!(
                                        "invalid value in numeric operation: {}",
                                        nanbox::debug_type(v)
                                    )
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    inst::NEWCLOSURE => {
                        let fn_index =
                            u32::from_le_bytes(*((ip as usize + 1) as *const [u8; 4])) as usize;
                        let cell_count = u16::from_le_bytes(*((ip as usize + 5) as *const [u8; 2]));
                        let f =
                            &pp.functions[fn_index] as *const Function as usize as *mut Function;
                        let c = Closure::alloc(cell_count).as_mut().unwrap();
                        c.function.set_ptr(f);
                        for i in 0..cell_count {
                            let cell = *((sp + (cell_count - i - 1) as usize * 8) as *mut *mut u64);
                            c.set_cell(i, cell);
                        }
                        sp += cell_count as usize * 8;
                        types.truncate(types.len() - cell_count as usize);
                        push!(c as *const Closure as u64, Type::Closure);
                    }
                    inst::NIL => {
                        push!(0, Type::Nil);
                    }
                    inst::NOP => (),
                    inst::NOT => {
                        let (v, ty) = pop!();
                        match ty {
                            Type::Bool => {
                                let vb = v != 0;
                                push!((!vb) as u64, Type::Bool);
                            }
                            Type::Nanbox => {
                                if let Some(vb) = nanbox::to_bool(v) {
                                    push!(nanbox::from_bool(!vb), Type::Nanbox);
                                } else {
                                    return_errorf!(
                                        "invalid value in logic negation: {}",
                                        nanbox::debug_str(v)
                                    )
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    inst::POP => {
                        sp += 8;
                        types.pop();
                    }
                    inst::RET => {
                        let ret_sp = sp;
                        let stack_depth = (fp - sp) / 8;
                        let ret_ty = types.last().unwrap().clone();
                        types.truncate(types.len() - stack_depth - func.param_types.len());
                        types.push(ret_ty);
                        sp = fp + FRAME_SIZE + func.param_types.len() * 8 - 8;
                        func = match (*((fp + 24) as *const *const Function)).as_ref() {
                            Some(f) => f,
                            None => {
                                return Ok(());
                            }
                        };
                        pp = func.package.as_ref().unwrap();
                        cp = *((fp + 16) as *const *mut *mut u64);
                        ip = *((fp + 8) as *const *const u8);
                        fp = *(fp as *const usize);
                        let v = *(ret_sp as *const u64);
                        *(sp as *mut u64) = v;
                        continue;
                    }
                    inst::STORE => {
                        let (v, vty) = pop!();
                        let (p, pty) = pop!();
                        match pty {
                            Type::Pointer(ty) => assert_eq!(*ty, vty),
                            _ => unreachable!(),
                        };
                        *(p as *mut u64) = v;
                        if vty.is_pointer() {
                            HEAP.write_barrier(p as usize, v as usize);
                        }
                    }
                    inst::STOREARG => {
                        let ai =
                            u16::from_le_bytes(*((ip as usize + 1) as *const [u8; 2])) as usize;
                        let si = func.param_types.len() - ai - 1;
                        let (v, ty) = pop!();
                        assert!(ty == func.param_types[ai]);
                        *((fp + FRAME_SIZE + si * 8) as *mut u64) = v;
                    }
                    inst::STOREGLOBAL => {
                        let i = *((ip as usize + 1) as *const u32) as usize;
                        let (v, ty) = pop!();
                        self.global_slots[i] = v;
                        if ty.is_pointer() {
                            HEAP.write_barrier(
                                &self.global_slots[i] as *const u64 as usize,
                                v as usize,
                            );
                        }
                    }
                    inst::STORELOCAL => {
                        let i = *((ip as usize + 1) as *const u16) as usize;
                        let stack_depth = (fp - sp) / 8;
                        let tyi = types.len() - stack_depth + i;
                        let (v, ty) = pop!();
                        *((fp as usize - (i + 1) * 8) as *mut u64) = v;
                        types[tyi] = ty;
                    }
                    inst::STORENAMEDPROP => {
                        let i = *((ip as usize + 1) as *const u32) as usize;
                        let name = &pp.strings[i];
                        let (v, vty) = pop!();
                        let (r, rty) = pop!();
                        match rty {
                            Type::Object => {
                                // TODO: figure out where the property is based
                                // on its static type. We need to know the
                                // type of the property itself, too.
                                unimplemented!();
                            }
                            Type::Nanbox => {
                                if vty != Type::Nanbox {
                                    // TODO: store statically typed values
                                    // in objects.
                                    unimplemented!();
                                }
                                let o = if let Some(o) = nanbox::to_object(r) {
                                    (o as usize as *mut Object).as_mut().unwrap()
                                } else {
                                    return_errorf!(
                                        "value is not an object: {}",
                                        nanbox::debug_type(r)
                                    )
                                };
                                o.set_property(name, v);
                            }
                            _ => {
                                return_errorf!("value is not an object: {}", rty);
                            }
                        }
                    }
                    inst::STRING => {
                        let i = *((ip as usize + 1) as *const u32) as usize;
                        let s = &pp.strings[i] as *const data::String as u64;
                        push!(s, Type::String);
                    }
                    inst::SUB => {
                        binop_num!(-)
                    }
                    inst::SWAP => {
                        let (v1, ty1) = pop!();
                        let (v2, ty2) = pop!();
                        push!(v1, ty1);
                        push!(v2, ty2);
                    }
                    inst::SYS => {
                        let sys = *((ip as usize + 1) as *const u8);
                        match sys {
                            inst::SYS_PRINT => {
                                let (v, ty) = pop!();
                                self.sys_print(v, &ty)?;
                            }
                            _ => panic!("unknown sys"),
                        }
                    }
                    inst::TRUE => {
                        push!(1, Type::Bool);
                    }
                    _ => panic!("unknown opcode"),
                }
                ip = ((ip as usize) + inst::size(*ip)) as *const u8;
            }
        }
    }

    fn sys_print(&mut self, v: u64, type_: &Type) -> Result<(), Error> {
        let r = match type_ {
            Type::Nil => {
                write!(self.w, "nil\n")
            }
            Type::Bool => {
                write!(self.w, "{}\n", v != 0)
            }
            Type::Float64 => {
                write!(self.w, "{}\n", f64::from_bits(v))
            }
            Type::String => unsafe {
                write!(self.w, "{}\n", (v as *const data::String).as_ref().unwrap())
            },
            Type::Function | Type::Closure => {
                write!(self.w, "<function>\n")
            }
            Type::Object => {
                write!(self.w, "<object>\n")
            }
            Type::Nanbox => {
                write!(self.w, "{}\n", nanbox::debug_str(v))
            }
            Type::Pointer(_) => {
                write!(self.w, "<pointer>\n")
            }
        };
        r.map_err(|_| Error {
            message: String::from("error printing value"),
        })
    }
}

struct Stack {
    data: Vec<u8>,
}

impl Stack {
    fn new() -> Stack {
        let mut data = Vec::new();
        data.resize(1024, 0);
        Stack { data }
    }

    fn end(&mut self) -> usize {
        &mut self.data[0] as *mut u8 as usize + self.data.len()
    }
}

#[derive(Debug)]
pub struct Error {
    message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.message.fmt(f)
    }
}

impl error::Error for Error {}
