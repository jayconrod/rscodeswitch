use crate::data;
use crate::heap::{Set, HEAP};
use crate::inst;
use crate::nanbox;
use crate::package::{Closure, Function, Object, PropertyKind, Type};

use std::error;
use std::fmt;
use std::io::Write;
use std::mem;

// Each stack frame consists of (with descending stack address):
//
//   - Caller: *const Function
//   - Caller's closure: *const Closure
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

            // pp points to the current function's package.
            let mut pp = func.package.as_ref().unwrap();
            if self.global_slots.is_empty() {
                self.global_slots.resize(pp.globals.len(), 0);
            }

            // cp points to the current function's closure. cp is null if
            // the function was called directly without a closure.
            let mut cp = 0 as *const Closure;

            let mut stack = Stack::new();
            // sp is the top of the stack. sp points to the last temporary
            // stack slot. The stack grows down.
            let mut sp = stack.end() - FRAME_SIZE;

            // fp is the frame pointer. fp points to the caller's saved fp
            // in the stack frame. The addresses of local variables and
            // arguments are based on fp.
            let mut fp = sp;

            // ip is the instruction pointer. ip points to the next instruction
            // to execute.
            let mut ip = &func.insts[0] as *const u8;

            // types is a stack containing types of values on the stack,
            // including from calling functions. types should contain mostly
            // static information, but some types may be more specific than
            // can be statically inferred.
            let mut types = Vec::new();

            // Construct the stack frame.
            *((fp + 24) as *mut u64) = 0; // caller
            *((fp + 16) as *mut u64) = 0; // caller's cells
            *((fp + 8) as *mut u64) = 0; // return address
            *(fp as *mut u64) = 0; // caller's fp

            // return_errorf! stops execution, formats an error, and returns it.
            macro_rules! return_errorf {
                ($($x:expr),*) => {
                    return Err(Error{message: format!($($x,)*)})
                };
            }

            // pop! removes and returns the value on top of the stack.
            // If pop! is called with a type, it checks that the type on
            // top of the type stack is the same.
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

            // pop_cond! removes and returns the value on top of the stack
            // as a bool, to be used as a condition.
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

            // push! adds a given value and type to the top of the stack.
            macro_rules! push {
                ($x:expr, $t:expr) => {{
                    sp -= 8;
                    *(sp as *mut u64) = $x;
                    types.push($t);
                }};
            }

            // shift_args! shifts a number of values on top of the stack
            // back by a given number of slots, deleting values earlier
            // in the stack.
            // TODO: this is used in function calls and is inefficient.
            // Is there a better way?
            macro_rules! shift_args {
                ($arg_count:ident, $by:expr) => {{
                    let arg_count = $arg_count as usize;
                    let by = $by;
                    let mut from = sp + arg_count * 8 - 8;
                    let mut to = from + by * 8;
                    while from >= sp {
                        *(to as *mut u64) = *(from as *mut u64);
                        from -= 8;
                        to -= 8;
                    }
                    sp += by * 8;
                    types.drain(types.len() - arg_count - by..types.len() - arg_count);
                }};
            }

            // call_closure! sets up a call to the given closure, with a number
            // of arguments on the stack. If the callee has bound arguments,
            // they're inserted on the stack before the arguments that are
            // already there. After call_closure!, ip points to the first
            // instruction of the callee, so 'continue' should run to avoid
            // incrementing ip.
            macro_rules! call_closure {
                ($callee:expr, $arg_count:expr) => {{
                    let callee = $callee;
                    let arg_count = $arg_count;
                    let callee_func = callee.function.unwrap_ref();
                    if callee.bound_arg_count as usize + arg_count != callee_func.param_types.len()
                    {
                        return_errorf!(
                            "call to function with {} parameters, but got {} arguments",
                            callee_func.param_types.len(),
                            arg_count
                        );
                    }

                    // If the callee has bound arguments, insert them on the
                    // stack before the regular arguments.
                    if callee.bound_arg_count > 0 {
                        let bound_arg_begin = sp + arg_count * 8 - 8;
                        let delta = callee.bound_arg_count as usize * 8;
                        let mut from = sp;
                        sp -= delta;
                        let mut to = sp;
                        while from <= bound_arg_begin {
                            *(to as *mut u64) = *(from as *mut u64);
                            to += 8;
                            from += 8;
                        }
                        for i in 0..callee.bound_arg_count {
                            let to = (bound_arg_begin - i as usize * 8) as *mut u64;
                            *to = callee.bound_arg(i);
                        }
                        types.resize(types.len() + callee.bound_arg_count as usize, Type::Nil);
                        for i in 0..arg_count {
                            let to = types.len() - i as usize - 1;
                            let from = to - arg_count;
                            let mut tmp = Type::Nil;
                            mem::swap(&mut tmp, &mut types[from]);
                            mem::swap(&mut types[to], &mut tmp);
                        }
                        for i in 0..(callee.bound_arg_count as usize) {
                            let to = types.len() - callee_func.param_types.len() + i;
                            types[to] = callee_func.param_types[i].clone();
                        }
                    }

                    // Construct a stack frame for the callee, and set the
                    // "registers" so the function's instructions, cells,
                    // and package will be used.
                    sp -= FRAME_SIZE;
                    *((sp as usize + 24) as *mut u64) = func as *const Function as u64;
                    func = callee_func;
                    *((sp as usize + 16) as *mut u64) = cp as u64;
                    cp = callee;
                    *((sp as usize + 8) as *mut u64) = ip as u64 + inst::size(*ip) as u64;
                    ip = &func.insts[0] as *const u8;
                    *(sp as *mut u64) = fp as u64;
                    fp = sp;
                    pp = callee_func.package.as_ref().unwrap();
                }};
            }

            // binop_eq! implements the == and != operators.
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

            // binop_cmp! implements the <, <=, >, and >= operators.
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

            // binop_num! implements other numeric operators.
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
                    inst::CALLNAMEDPROP => {
                        let name_index = *((ip as usize + 1) as *const u32) as usize;
                        let name = &pp.strings[name_index];
                        let arg_count = *((ip as usize + 5) as *const u16) as usize;
                        let receiver_addr = sp + arg_count * 8;
                        let receiver = match types[types.len() - arg_count - 1] {
                            Type::Object => {
                                (*(receiver_addr as *const *const Object)).as_ref().unwrap()
                            }
                            Type::Nanbox => {
                                let r = *(receiver_addr as *const u64);
                                if let Some(o) = nanbox::to_object(r) {
                                    o.as_ref().unwrap()
                                } else {
                                    return_errorf!(
                                        "receiver is not an object: {}",
                                        nanbox::debug_type(r)
                                    );
                                }
                            }
                            _ => unreachable!(),
                        };
                        let prop = if let Some(prop) = receiver.property(name) {
                            prop
                        } else {
                            return_errorf!("property {} is not defined", name);
                        };
                        let callee = if let Some(c) = nanbox::to_closure(prop.value) {
                            c.as_ref().unwrap()
                        } else {
                            return_errorf!("property {} is not a function", name);
                        };
                        let arg_count_including_receiver = if prop.kind != PropertyKind::Method {
                            // If this is not a method but a regular field that
                            // happens to contain a function, shift the
                            // arguments back to remove the receiver from the
                            // stack. A method will pop the receiver (and so it
                            // remains on the stack in that case), but a
                            // function won't.
                            // TODO: this is horrendously inefficient. Come up
                            // with something better.
                            shift_args!(arg_count, 1);
                            arg_count
                        } else {
                            arg_count + 1
                        };
                        call_closure!(callee, arg_count_including_receiver);
                        continue;
                    }
                    inst::CALLNAMEDPROPWITHPROTOTYPE => {
                        let name_index = *((ip as usize + 1) as *const u32) as usize;
                        let name = &pp.strings[name_index];
                        let arg_count = *((ip as usize + 5) as *const u16) as usize;
                        let prototype_addr = sp + arg_count * 8;
                        let prototype = match types[types.len() - arg_count - 1] {
                            Type::Object => (*(prototype_addr as *const *const Object))
                                .as_ref()
                                .unwrap(),
                            Type::Nanbox => {
                                let r = *(prototype_addr as *const u64);
                                if let Some(o) = nanbox::to_object(r) {
                                    o.as_ref().unwrap()
                                } else {
                                    return_errorf!(
                                        "prototype is not an object: {}",
                                        nanbox::debug_type(r)
                                    );
                                }
                            }
                            _ => unreachable!(),
                        };
                        let prop = if let Some(prop) = prototype.property(name) {
                            prop
                        } else {
                            return_errorf!("property {} is not defined", name);
                        };
                        let callee = if let Some(c) = nanbox::to_closure(prop.value) {
                            c.as_ref().unwrap()
                        } else {
                            return_errorf!("property {} is not a function", name);
                        };
                        let arg_count_including_receiver = if prop.kind != PropertyKind::Method {
                            // Not a method but a regular field that happens to
                            // contain a function. See comment in CALLNAMEDPROP.
                            shift_args!(arg_count, 2);
                            arg_count
                        } else {
                            // Regular method call. We still need to remove the
                            // prototype from the stack though.
                            shift_args!(arg_count, 1);
                            arg_count + 1
                        };
                        call_closure!(callee, arg_count_including_receiver);
                        continue;
                    }
                    inst::CALLVALUE => {
                        let arg_count =
                            i16::from_le_bytes(*((ip as usize + 1) as *const [u8; 2])) as usize;
                        let callee_addr = sp + arg_count * 8;
                        let raw_callee = *(callee_addr as *const u64);
                        let callee = match types[types.len() - arg_count as usize - 1] {
                            Type::Closure => (raw_callee as *const Closure).as_ref().unwrap(),
                            Type::Nanbox => {
                                if let Some(c) = nanbox::to_closure(raw_callee) {
                                    c.as_ref().unwrap()
                                } else {
                                    return_errorf!(
                                        "call of non-function ({})",
                                        nanbox::debug_type(raw_callee)
                                    )
                                }
                            }
                            _ => unreachable!(),
                        };
                        // Remove the callee from the stack before the call.
                        // CALLNAMEDPROP does this too when the called property
                        // is a field instead of a method. See comment there.
                        // TODO: this is a terrible, inefficient solution.
                        shift_args!(arg_count, 1);
                        call_closure!(callee, arg_count);
                        continue;
                    }
                    inst::CAPTURE => {
                        let i = u16::from_le_bytes(*((ip as usize + 1) as *const [u8; 2]));
                        let c = cp.as_ref().unwrap();
                        let cell = c.capture(i) as u64;
                        let ty = c.function.cell_types[i as usize].clone();
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
                                let value = if prop.kind == PropertyKind::Method {
                                    // Method loaded as value without call.
                                    // Allocate a new closure to bind the
                                    // receiver, and return the bound method.
                                    let method =
                                        nanbox::to_closure(prop.value).unwrap().as_ref().unwrap();
                                    let raw = Closure::alloc(
                                        method.capture_count,
                                        method.bound_arg_count + 1,
                                    );
                                    let bm = raw.as_mut().unwrap();
                                    bm.function.set(&method.function);
                                    for i in 0..method.capture_count {
                                        bm.set_capture(i, method.capture(i));
                                    }
                                    for i in 0..method.bound_arg_count {
                                        bm.set_bound_arg(i, method.bound_arg(i));
                                    }
                                    bm.set_bound_arg(method.bound_arg_count, r);
                                    nanbox::from_closure(bm)
                                } else {
                                    prop.value
                                };
                                push!(value, Type::Nanbox);
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
                            Type::Closure => {
                                let c = (v as *const Closure).as_ref().unwrap();
                                c.prototype.unwrap()
                            }
                            Type::Nanbox => {
                                if let Some(o) = nanbox::to_object(v) {
                                    o.as_ref().unwrap().prototype.unwrap()
                                } else if let Some(c) = nanbox::to_closure(v) {
                                    c.as_ref().unwrap().prototype.unwrap()
                                } else {
                                    return_errorf!(
                                        "value is not an object: {}",
                                        nanbox::debug_type(v)
                                    );
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
                        let capture_count =
                            u16::from_le_bytes(*((ip as usize + 5) as *const [u8; 2]));
                        let bound_arg_count =
                            u16::from_le_bytes(*((ip as usize + 7) as *const [u8; 2]));
                        let f =
                            &pp.functions[fn_index] as *const Function as usize as *mut Function;
                        let c = Closure::alloc(capture_count, bound_arg_count)
                            .as_mut()
                            .unwrap();
                        c.function.set_ptr(f);
                        let cell_count = capture_count as usize + bound_arg_count as usize;
                        let mut from = sp + cell_count * 8 - 8;
                        for i in 0..capture_count {
                            let v = *(from as *mut *mut u64);
                            c.set_capture(i, v);
                            from -= 8;
                        }
                        for i in 0..bound_arg_count {
                            let v = *(from as *mut u64);
                            c.set_bound_arg(i, v);
                            from -= 8;
                        }
                        sp += cell_count * 8;
                        types.truncate(types.len() - cell_count);
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
                    inst::PROTOTYPE => {
                        let c = cp.as_ref().unwrap();
                        let p = c.prototype.unwrap();
                        assert!(!p.is_null());
                        push!(p as u64, Type::Object);
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
                        cp = *((fp + 16) as *const *const Closure);
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
                    inst::STOREMETHOD => {
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
                                o.set_own_property(name, PropertyKind::Method, v);
                            }
                            _ => {
                                return_errorf!("value is not an object: {}", rty);
                            }
                        }
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
                                o.set_property(name, PropertyKind::Field, v);
                            }
                            _ => {
                                return_errorf!("value is not an object: {}", rty);
                            }
                        }
                    }
                    inst::STOREPROTOTYPE => {
                        let p = pop!(Type::Object) as *mut Object;
                        let (o, oty) = pop!();
                        match oty {
                            Type::Object => {
                                let o = (o as *mut Object).as_mut().unwrap();
                                o.prototype.set_ptr(p);
                            }
                            Type::Closure => {
                                let c = (o as *mut Closure).as_mut().unwrap();
                                c.prototype.set_ptr(p);
                            }
                            _ => unreachable!(),
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
                    inst::SWAPN => {
                        let n = *((ip as usize + 1) as *const u8);
                        let top = sp as *mut u64;
                        let slot = (sp + (n as usize + 1) * 8) as *mut u64;
                        let v = *top;
                        *top = *slot;
                        *slot = v;
                        let stack_depth = types.len();
                        types.swap(stack_depth - 1, stack_depth - n as usize - 1);
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
    // TODO: include source locations in error messages. This requires some
    // mechanism to map instruction addresses to source locations.
    message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.message.fmt(f)
    }
}

impl error::Error for Error {}
