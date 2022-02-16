use crate::data;
use crate::heap::HEAP;
use crate::inst;
use crate::nanbox::{self, NanBox};
use crate::package::{Closure, Function, Object, Property, PropertyKind};
use crate::pos::Error;

use std::io::Write;
use std::mem;

// Each stack frame consists of (with descending stack address):
//
//   - Caller: *const Function
//   - Caller's closure: *const Closure
//   - Return address: *const u8
//   - Caller's fp
const FRAME_SIZE: usize = 32;

pub struct Interpreter<'w> {
    w: &'w mut dyn Write,
}

impl<'w> Interpreter<'w> {
    pub fn new(w: &'w mut dyn Write) -> Interpreter<'w> {
        Interpreter { w }
    }

    pub fn interpret(&mut self, func: &Function) -> Result<(), Error> {
        unsafe { self.interpret_unsafe(func) }
    }

    pub unsafe fn interpret_unsafe(&mut self, mut func: &Function) -> Result<(), Error> {
        assert!(func.param_types.is_empty());

        // vc is value count. In Lua, this is the number of dynamic values in
        // an expression list.
        let mut vc = 0;

        // pp points to the current function's package.
        let mut pp = func.package.as_mut().unwrap();

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

        // Construct the stack frame.
        *((fp + 24) as *mut u64) = 0; // caller
        *((fp + 16) as *mut u64) = 0; // caller's cells
        *((fp + 8) as *mut u64) = 0; // return address
        *(fp as *mut u64) = 0; // caller's fp

        // return_errorf constructs and returns an error immediately.
        macro_rules! return_errorf {
            ($($x:expr),*) => {{
                let message = format!($($x,)*);
                return Err(Interpreter::error(func, ip, message))
            }};
        }

        // read_imm reads an immediate value out of the instruction stream.
        macro_rules! read_imm {
            ($ty:ident, $offset:literal) => {
                $ty::from_le_bytes(*((ip as usize + $offset) as *const [u8; mem::size_of::<$ty>()]))
            };
        }

        // pop! removes and returns the value on top of the stack.
        macro_rules! pop {
            () => {{
                let v = *(sp as *mut u64);
                sp += 8;
                v
            }};
        }

        // pop_float! is like pop! but works with f64 and f32.
        macro_rules! pop_float {
            (f32) => {{
                let bits = *(sp as *mut u64) as u32;
                sp += 8;
                f32::from_bits(bits)
            }};
            (f64) => {{
                let bits = *(sp as *mut u64);
                sp += 8;
                f64::from_bits(bits)
            }};
        }

        // push! adds a given value to the top of the stack.
        macro_rules! push {
            ($e:expr) => {{
                let v: u64 = $e;
                sp -= 8;
                *(sp as *mut u64) = v;
            }};
        }

        // push_float! is like pop! but works with f64 and f32.
        macro_rules! push_float {
            ($e:expr, f32) => {
                push!(($e).to_bits() as u64)
            };
            ($e:expr, f64) => {
                push!(($e).to_bits())
            };
        }

        // load! implements instructions that load values using pointers.
        macro_rules! load {
            ($ty:ty, $p:expr, $index:expr, $offset:expr) => {{
                let addr = ($p) as usize + ($index) * mem::size_of::<$ty>() + $offset;
                *(addr as *const $ty)
            }};
        }

        // store! implements instructions that store values using pointers.
        macro_rules! store {
            (ptr, $p:expr, $index:expr, $offset:expr, $value:expr) => {{
                let addr = ($p) as usize + ($index) * mem::size_of::<usize>() + $offset;
                let value = $value;
                *(addr as *mut usize) = value;
                HEAP.write_barrier(addr, value);
            }};
            (lua, $p:expr, $index:expr, $offset:expr, $value:expr) => {{
                let addr = ($p) as usize + ($index) * mem::size_of::<u64>() + $offset;
                let value = $value;
                *(addr as *mut u64) = value;
                HEAP.write_barrier_nanbox(addr, value);
            }};
            ($ty:ty, $p:expr, $index:expr, $offset:expr, $value:expr) => {{
                let addr = ($p) as usize + ($index) * mem::size_of::<$ty>() + $offset;
                *(addr as *mut $ty) = $value;
            }};
        }

        // binop_eq! implements the == and != operators.
        macro_rules! binop_eq {
            ($op:tt, f32) => {{
                let r = pop_float!(f32);
                let l = pop_float!(f32);
                let v = (l $op r) as u64;
                push!(v);
            }};
            ($op:tt, f64) => {{
                let r = pop_float!(f64);
                let l = pop_float!(f64);
                let v = (l $op r) as u64;
                push!(v);
            }};
            ($op:tt, lua) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                let v = NanBox::from(l $op r);
                push!(v.0);
            }};
            ($op:tt, $ty:ty) => {{
                let r = pop!() as $ty;
                let l = pop!() as $ty;
                let v = (l $op r) as u64;
                push!(v);
            }};
        }

        // binop_cmp! implements the <, <=, >, >= operators.
        macro_rules! binop_cmp {
            ($op:tt, f32) => {{
                let r = pop_float!(f32);
                let l = pop_float!(f32);
                let v = (l $op r) as u64;
                push!(v);
            }};
            ($op:tt, f64) => {{
                let r = pop_float!(f64);
                let l = pop_float!(f64);
                let v = (l $op r) as u64;
                push!(v);
            }};
            ($ordmethod:ident, lua) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                let v = if let Some(c) = l.partial_cmp(&r) {
                    NanBox::from(c.$ordmethod())
                } else {
                    return_errorf!("can't compare values: {:?} and {:?}", l, r);
                };
                push!(v.0)
            }};
            ($op:tt, $ty:ty) => {{
                let r = pop!() as $ty;
                let l = pop!() as $ty;
                let v = (l $op r) as u64;
                push!(v);
            }};
        }

        // binop_num! implements numeric operators that produce a value of
        // the same type.
        macro_rules! binop_num {
            ($op:tt, f32) => {{
                let r = pop_float!(f32);
                let l = pop_float!(f32);
                let v = l $op r;
                push_float!(v, f32);
            }};
            ($op:tt, f64) => {{
                let r = pop_float!(f64);
                let l = pop_float!(f64);
                let v = l $op r;
                push_float!(v, f64);
            }};
            ($op:tt, $checked:ident, lua) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                let v = if let (Ok(li), Ok(ri)) = (<NanBox as TryInto<i64>>::try_into(l), <NanBox as TryInto<i64>>::try_into(r)) {
                    match li.$checked(ri) {
                        Some(vi) => maybe_box_int!(vi),
                        None => NanBox::from((li as f64) $op (ri as f64))
                    }
                } else if let (Ok(lf), Ok(rf)) = (l.as_f64(), r.as_f64()) {
                    NanBox::from(lf $op rf)
                } else {
                    return_errorf!("arithmetic operands must both be numbers: {:?} and {:?}", l, r)
                };
                push!(v.0);
            }};
            ($wrapping:ident, $ty:ty) => {{
                let r = pop!() as $ty;
                let l = pop!() as $ty;
                let v = l.$wrapping(r) as u64;
                push!(v);
            }};
        }

        // unop_num! implements unary numeric operators that produce a value
        // of the same type.
        macro_rules! unop_num {
            ($op:tt, f32) => {{
                let v = pop_float!(f32);
                let r = $op v;
                push_float!(r, f32);
            }};
            ($op:tt, f64) => {{
                let v = pop_float!(f64);
                let r = $op v;
                push_float!(r, f64);
            }};
            ($op:tt, lua) => {{
                let o = NanBox(pop!());
                let v = if let Ok(i) = <NanBox as TryInto<i64>>::try_into(o) {
                    maybe_box_int!($op i)
                } else if let Ok(f) = o.as_f64() {
                    NanBox::from($op f)
                } else {
                    return_errorf!("arithmetic operand must be number: {:?}", o)
                };
                push!(v.0);
            }};
            ($op:tt, $ty:ty) => {{
                let o = pop!() as $ty;
                let v = $op o;
                push!(v as u64);
            }};
        }

        // shift_args! shifts a number of values on top of the stack
        // back by a given number of slots, deleting values earlier
        // in the stack.
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
            }};
        }

        // arg_addr returns the stack address of an argument to the current
        // function.
        macro_rules! arg_addr {
            ($index:expr) => {{
                let index = $index;
                if func.var_param_type.is_some() {
                    let argc = *((fp + FRAME_SIZE) as *const u64) as usize;
                    fp + FRAME_SIZE + argc * 8 - index * 8
                } else {
                    let argc = func.param_types.len();
                    fp + FRAME_SIZE + argc * 8 - index * 8 - 8
                }
            }};
        }

        // maybe_box_int converts an unboxed integer to a small or big boxed
        // integer. If the integer doesn't fit in a small box, a big box is
        // allocated.
        macro_rules! maybe_box_int {
            ($i:expr) => {{
                let i: i64 = $i;
                NanBox::try_from(i).unwrap_or_else(|_| {
                    let bi = HEAP.allocate(mem::size_of::<i64>()) as *mut i64;
                    *bi = i;
                    NanBox::from(bi)
                })
            }};
        }

        // lua_value_as_bool converts a nanboxed value to true or false
        // (unboxed) according to Lua semantics. false and nil are false;
        // all other values are true.
        macro_rules! lua_value_as_bool {
            ($v:expr) => {{
                let v: NanBox = $v;
                !v.is_nil() && <NanBox as TryInto<bool>>::try_into(v).unwrap_or(true)
            }};
        }

        // lua_value_as_int converts a nanboxed value to an integer according
        // to Lua semantics. Integers are converted to themselves; floats
        // are converted if the conversion is exact. An error is reported for
        // any other value.
        macro_rules! lua_value_as_int {
            ($v:expr) => {{
                let v: NanBox = $v;
                if let Ok(i) = v.as_i64() {
                    i
                } else if v.is_number() {
                    return_errorf!("number has no integer representation")
                } else {
                    return_errorf!("cannot perform numeric operation on {:?} value", v)
                }
            }};
        }

        // lua_concat_op_as_string converts a nanboxed value to a string
        // for concatenation. Strings and numbers are allowed. All other
        // values cause errors.
        macro_rules! lua_concat_op_as_string {
            ($v:expr) => {{
                let v: NanBox = $v;
                if let Ok(s) = <NanBox as TryInto<&data::String>>::try_into(v) {
                    s
                } else if let Ok(i) = <NanBox as TryInto<i64>>::try_into(v) {
                    let s = i.to_string();
                    data::String::from_bytes(s.as_bytes()).as_ref().unwrap()
                } else if let Ok(f) = <NanBox as TryInto<f64>>::try_into(v) {
                    let s = f.to_string();
                    data::String::from_bytes(s.as_bytes()).as_ref().unwrap()
                } else {
                    return_errorf!("can't convert concatenation operand to string: {:?}", v)
                }
            }};
        }

        // lua_binop_bit implements the &, |, and ~ binary operators for Lua.
        // It unboxes its operands and converts them to integers, reporting an
        // error if either is not a number. It then performs the operation,
        // boxes, and pushes the result.
        macro_rules! lua_binop_bit {
            ($op:tt) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                let li = lua_value_as_int!(l);
                let ri = lua_value_as_int!(r);
                let v = li $op ri;
                push!(maybe_box_int!(v).0);
            }};
        }

        macro_rules! lua_call_closure {
            ($callee:expr, $arg_count:expr) => {{
                // TODO: support metatable calls
                let callee: &Closure = $callee;
                let arg_count = ($arg_count) as usize;
                let callee_func = callee.function.unwrap_ref();

                // If the callee has bound arguments, insert them on the stack
                // before the regular arguments.
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
                }

                // If there are fewer arguments than parameters, push nils. If
                // the callee is variadic, push the number of arguments,
                // including pushed nils. If the callee is not variadic and
                // there are more arguments than parameters, pop the extra
                // arguments.
                let mut total_arg_count = arg_count + callee.bound_arg_count as usize;
                if total_arg_count > u16::MAX as usize {
                    return_errorf!("too many arguments");
                }
                let param_count = callee_func.param_types.len();
                if total_arg_count < param_count {
                    for _ in 0..(param_count - total_arg_count) {
                        push!(NanBox::from_nil().0);
                    }
                    total_arg_count = param_count;
                }
                if callee_func.var_param_type.is_some() {
                    push!(total_arg_count as u64);
                } else if total_arg_count > param_count {
                    sp += (total_arg_count - param_count) * 8;
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
                pp = callee_func.package.as_mut().unwrap();
            }};
        }

        // Main loop
        loop {
            let mut op = *ip;
            let mode = if op < inst::MODE_MIN {
                inst::MODE_I64
            } else {
                let m = op;
                ip = (ip as usize + 1) as *const u8;
                op = *ip;
                m
            };

            let inst_size = match (op, mode) {
                (inst::ADD, inst::MODE_I64) => {
                    binop_num!(wrapping_add, i64);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_I32) => {
                    binop_num!(wrapping_add, i32);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_I16) => {
                    binop_num!(wrapping_add, i16);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_I8) => {
                    binop_num!(wrapping_add, i8);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_U64) => {
                    binop_num!(wrapping_add, u64);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_U32) => {
                    binop_num!(wrapping_add, u32);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_U16) => {
                    binop_num!(wrapping_add, u16);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_U8) => {
                    binop_num!(wrapping_add, u8);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_F64) => {
                    binop_num!(+, f64);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_F32) => {
                    binop_num!(+, f32);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    let v = if let (Ok(li), Ok(ri)) = (
                        <NanBox as TryInto<i64>>::try_into(l),
                        <NanBox as TryInto<i64>>::try_into(r),
                    ) {
                        match li.checked_add(ri) {
                            Some(vi) => maybe_box_int!(vi),
                            None => NanBox::from((li as f64) + (ri as f64)),
                        }
                    } else if let (Ok(lf), Ok(rf)) = (l.as_f64(), r.as_f64()) {
                        NanBox::from(lf + rf)
                    } else if let (Ok(ls), Ok(rs)) = (
                        <NanBox as TryInto<&data::String>>::try_into(l),
                        <NanBox as TryInto<&data::String>>::try_into(r),
                    ) {
                        NanBox::from(ls + rs)
                    } else {
                        return_errorf!(
                            "arithmetic operands must both be numbers: {:?} and {:?}",
                            l,
                            r
                        )
                    };
                    push!(v.0);
                    inst::size(inst::ADD)
                }
                (inst::ADJUSTV, inst::MODE_LUA) => {
                    let value_count = read_imm!(u16, 1) as usize;
                    if vc < value_count {
                        for _ in 0..(value_count - vc) {
                            push!(NanBox::from_nil().0);
                        }
                    } else {
                        sp += (vc - value_count) as usize * 8;
                    }
                    vc = value_count;
                    inst::size(inst::ADJUSTV)
                }
                (inst::ALLOC, inst::MODE_I64) => {
                    let size = read_imm!(u32, 1) as usize;
                    push!(HEAP.allocate(size) as u64);
                    inst::size(inst::ALLOC)
                }
                (inst::AND, inst::MODE_LUA) => {
                    lua_binop_bit!(&);
                    inst::size(inst::AND)
                }
                (inst::APPENDV, inst::MODE_LUA) => {
                    let value_count = read_imm!(u16, 1) as usize;
                    vc += value_count;
                    inst::size(inst::APPENDV)
                }
                (inst::B, inst::MODE_I64) => {
                    let delta = read_imm!(i32, 1) as usize;
                    ip = ((ip as isize) + (delta as isize) + 1) as *const u8;
                    continue;
                }
                (inst::BIF, inst::MODE_I64) => {
                    let delta = read_imm!(i32, 1) as usize;
                    let v = pop!();
                    if v != 0 {
                        ip = ((ip as isize) + (delta as isize) + 1) as *const u8;
                        continue;
                    }
                    inst::size(inst::BIF)
                }
                (inst::BIF, inst::MODE_LUA) => {
                    let delta = read_imm!(i32, 1) as usize;
                    if lua_value_as_bool!(NanBox(pop!())) {
                        ip = ((ip as isize) + (delta as isize) + 1) as *const u8;
                        continue;
                    }
                    // fall through
                    inst::size(inst::BIF)
                }
                (inst::CALLNAMEDPROP, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let arg_count = read_imm!(u16, 5) as usize;
                    let receiver_addr = sp + arg_count * 8;
                    let raw_receiver = NanBox(*(receiver_addr as *const u64));
                    let receiver: &Object = match raw_receiver.try_into() {
                        Ok(o) => o,
                        _ => return_errorf!("receiver is not an object: {:?}", raw_receiver),
                    };
                    let prop = match receiver.property(key) {
                        Some(p) => p,
                        _ => return_errorf!("property {} is not defined", name),
                    };
                    let callee: &Closure = match prop.value.try_into() {
                        Ok(c) => c,
                        _ => return_errorf!("property {} is not a function", name),
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
                    lua_call_closure!(callee, arg_count_including_receiver);
                    continue;
                }
                (inst::CALLNAMEDPROPV, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let receiver_addr = sp + vc * 8;
                    let raw_receiver = NanBox(*(receiver_addr as *const u64));
                    let receiver: &Object = match raw_receiver.try_into() {
                        Ok(o) => o,
                        _ => return_errorf!("receiver is not an object: {:?}", raw_receiver),
                    };
                    let prop = match receiver.property(key) {
                        Some(p) => p,
                        _ => return_errorf!("property {} is not defined", name),
                    };
                    let callee: &Closure = match prop.value.try_into() {
                        Ok(c) => c,
                        _ => return_errorf!("property {} is not a function", name),
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
                        shift_args!(vc, 1);
                        vc
                    } else {
                        vc + 1
                    };
                    lua_call_closure!(callee, arg_count_including_receiver);
                    continue;
                }
                (inst::CALLNAMEDPROPWITHPROTOTYPE, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let arg_count = read_imm!(u16, 5) as usize;
                    let prototype_addr = sp + arg_count * 8;
                    let prototype = NanBox(*(prototype_addr as *const u64));
                    let prototype_obj: &Object = match prototype.try_into() {
                        Ok(p) => p,
                        _ => return_errorf!("prototype is not an object: {:?}", prototype),
                    };
                    let prop = match prototype_obj.property(key) {
                        Some(p) => p,
                        _ => return_errorf!("property {} is not defined", key),
                    };
                    let callee: &Closure = match prop.value.try_into() {
                        Ok(c) => c,
                        _ => return_errorf!("property {} is not a function", name),
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
                    lua_call_closure!(callee, arg_count_including_receiver);
                    continue;
                }
                (inst::CALLVALUE, inst::MODE_LUA) => {
                    let arg_count = read_imm!(u16, 1) as usize;
                    let callee_addr = sp + arg_count * 8;
                    let raw_callee = NanBox(*(callee_addr as *const u64));
                    let callee = match raw_callee.try_into() {
                        Ok(c) => c,
                        _ => return_errorf!("called value is not a function: {:?}", raw_callee),
                    };
                    // Remove the callee from the stack before the call.
                    // CALLNAMEDPROP does this too when the called property
                    // is a field instead of a method. See comment there.
                    // TODO: this is a terrible, inefficient solution.
                    shift_args!(arg_count, 1);
                    lua_call_closure!(callee, arg_count);
                    continue;
                }
                (inst::CALLVALUEV, inst::MODE_LUA) => {
                    let callee_addr = sp + vc * 8;
                    let raw_callee = NanBox(*(callee_addr as *const u64));
                    let callee = match raw_callee.try_into() {
                        Ok(c) => c,
                        _ => return_errorf!("called value is not a function: {:?}", raw_callee),
                    };
                    shift_args!(vc, 1);
                    lua_call_closure!(callee, vc);
                    continue;
                }
                (inst::CAPTURE, inst::MODE_I64) => {
                    let i = read_imm!(u16, 1);
                    let c = cp.as_ref().unwrap();
                    let cell = c.capture(i) as u64;
                    push!(cell);
                    inst::size(inst::CAPTURE)
                }
                (inst::CONST, _) => {
                    let v = read_imm!(u64, 1);
                    push!(v);
                    inst::size(inst::CONST)
                }
                (inst::CONSTZERO, _) => {
                    push!(0);
                    inst::size(inst::CONSTZERO)
                }
                (inst::DIV, inst::MODE_I64) => {
                    binop_num!(wrapping_div, i64);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_I32) => {
                    binop_num!(wrapping_div, i32);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_I16) => {
                    binop_num!(wrapping_div, i16);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_I8) => {
                    binop_num!(wrapping_div, i8);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_U64) => {
                    binop_num!(wrapping_div, u64);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_U32) => {
                    binop_num!(wrapping_div, u32);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_U16) => {
                    binop_num!(wrapping_div, u16);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_U8) => {
                    binop_num!(wrapping_div, u8);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_F64) => {
                    binop_num!(/, f64);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_F32) => {
                    binop_num!(/, f32);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    let v = if let (Ok(lf), Ok(rf)) = (l.as_f64_imprecise(), r.as_f64_imprecise()) {
                        NanBox::from(lf / rf)
                    } else {
                        return_errorf!(
                            "arithmetic operands must both be numbers: {:?} and {:?}",
                            l,
                            r
                        )
                    };
                    push!(v.0);
                    inst::size(inst::DIV)
                }
                (inst::DUP, inst::MODE_I64) => {
                    let v = *(sp as *const u64);
                    push!(v);
                    inst::size(inst::DUP)
                }
                (inst::EQ, inst::MODE_I64) => {
                    binop_eq!(==, i64);
                    inst::size(inst::EQ)
                }
                (inst::EQ, inst::MODE_F64) => {
                    binop_eq!(==, f64);
                    inst::size(inst::EQ)
                }
                (inst::EQ, inst::MODE_F32) => {
                    binop_eq!(==, f32);
                    inst::size(inst::EQ)
                }
                (inst::EQ, inst::MODE_LUA) => {
                    binop_eq!(==, lua);
                    inst::size(inst::EQ)
                }
                (inst::EXP, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    let v = if let (Ok(lf), Ok(rf)) = (l.as_f64_imprecise(), r.as_f64_imprecise()) {
                        NanBox::from(f64::powf(lf, rf))
                    } else {
                        return_errorf!(
                            "arithmetic operands must both be numbers: {:?} and {:?}",
                            l,
                            r
                        )
                    };
                    push!(v.0);
                    inst::size(inst::EXP)
                }
                (inst::FLOORDIV, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    let v = if let (Ok(li), Ok(ri)) = (l.as_i64(), r.as_i64()) {
                        maybe_box_int!(li / ri)
                    } else if let (Ok(lf), Ok(rf)) = (l.as_f64_imprecise(), r.as_f64_imprecise()) {
                        NanBox::from(lf.floor() / rf.floor())
                    } else {
                        return_errorf!(
                            "arithmetic operands must both be numbers: {:?} and {:?}",
                            l,
                            r
                        )
                    };
                    push!(v.0);
                    inst::size(inst::FLOORDIV)
                }
                (inst::FUNCTION, inst::MODE_I64) => {
                    let i = read_imm!(u32, 1) as usize;
                    let f = &pp.functions[i] as *const Function as u64;
                    push!(f);
                    inst::size(inst::FUNCTION)
                }
                (inst::GE, inst::MODE_I64) => {
                    binop_cmp!(>=, i64);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_I32) => {
                    binop_cmp!(>=, i32);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_I16) => {
                    binop_cmp!(>=, i16);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_I8) => {
                    binop_cmp!(>=, i8);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_U64) => {
                    binop_cmp!(>=, u64);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_U32) => {
                    binop_cmp!(>=, u32);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_U16) => {
                    binop_cmp!(>=, u16);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_U8) => {
                    binop_cmp!(>=, u8);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_F64) => {
                    binop_cmp!(>=, f64);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_F32) => {
                    binop_cmp!(>=, f32);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_LUA) => {
                    binop_cmp!(is_ge, lua);
                    inst::size(inst::GE)
                }
                (inst::GT, inst::MODE_I64) => {
                    binop_cmp!(>, i64);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_I32) => {
                    binop_cmp!(>, i32);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_I16) => {
                    binop_cmp!(>, i16);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_I8) => {
                    binop_cmp!(>, i8);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_U64) => {
                    binop_cmp!(>, u64);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_U32) => {
                    binop_cmp!(>, u32);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_U16) => {
                    binop_cmp!(>, u16);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_U8) => {
                    binop_cmp!(>, u8);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_F64) => {
                    binop_cmp!(>, f64);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_F32) => {
                    binop_cmp!(>, f32);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_LUA) => {
                    binop_cmp!(is_gt, lua);
                    inst::size(inst::GT)
                }
                (inst::LE, inst::MODE_I64) => {
                    binop_cmp!(<=, i64);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_I32) => {
                    binop_cmp!(<=, i32);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_I16) => {
                    binop_cmp!(<=, i16);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_I8) => {
                    binop_cmp!(<=, i8);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_U64) => {
                    binop_cmp!(<=, u64);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_U32) => {
                    binop_cmp!(<=, u32);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_U16) => {
                    binop_cmp!(<=, u16);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_U8) => {
                    binop_cmp!(<=, u8);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_F64) => {
                    binop_cmp!(<=, f64);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_F32) => {
                    binop_cmp!(<=, f32);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_LUA) => {
                    binop_cmp!(is_le, lua);
                    inst::size(inst::LE)
                }
                (inst::LEN, inst::MODE_LUA) => {
                    let o = NanBox(pop!());
                    let v = if let Ok(s) = <NanBox as TryInto<&data::String>>::try_into(o) {
                        s.len() as i64
                    } else if let Ok(o) = <NanBox as TryInto<&Object>>::try_into(o) {
                        // We want to return the index of the last non-nil
                        // property with a positive integer key in the table.
                        // Object::len is not quite that: it's one plus the
                        // index of the property with the highest non-negative
                        // integer key. If that property is nil, we walk back
                        // until we find a non-nil value.
                        // TODO: find a faster solution. The spec requires
                        // O(log n) time, but this is O(n).
                        let mut n = o.len;
                        if n > 0 {
                            n -= 1;
                        }
                        while n > 0 {
                            match o.own_array_property(n) {
                                Some(Property { value, .. }) if !value.is_nil() => break,
                                _ => (),
                            }
                            n -= 1;
                        }
                        n
                    } else {
                        return_errorf!("value is not an object: {:?}", o);
                    };
                    push!(maybe_box_int!(v).0);
                    inst::size(inst::LEN)
                }
                (inst::LOAD, inst::MODE_I64) => {
                    push!(load!(i64, pop!(), 0, 0) as u64);
                    inst::size(inst::LOAD)
                }
                (inst::LOAD, inst::MODE_I32) => {
                    push!(load!(i32, pop!(), 0, 0) as u64);
                    inst::size(inst::LOAD)
                }
                (inst::LOAD, inst::MODE_I16) => {
                    push!(load!(i16, pop!(), 0, 0) as u64);
                    inst::size(inst::LOAD)
                }
                (inst::LOAD, inst::MODE_I8) => {
                    push!(load!(i8, pop!(), 0, 0) as u64);
                    inst::size(inst::LOAD)
                }
                (inst::LOAD, inst::MODE_U32) => {
                    push!(load!(u32, pop!(), 0, 0) as u64);
                    inst::size(inst::LOAD)
                }
                (inst::LOAD, inst::MODE_U16) => {
                    push!(load!(u16, pop!(), 0, 0) as u64);
                    inst::size(inst::LOAD)
                }
                (inst::LOAD, inst::MODE_U8) => {
                    push!(load!(u8, pop!(), 0, 0) as u64);
                    inst::size(inst::LOAD)
                }
                (inst::LOAD, inst::MODE_F32) => {
                    push!(load!(f32, pop!(), 0, 0).to_bits() as u64);
                    inst::size(inst::LOAD)
                }
                (inst::LOADARG, inst::MODE_I64) => {
                    let i = read_imm!(u16, 1) as usize;
                    let slot = arg_addr!(i);
                    let v = *(slot as *const u64);
                    push!(v);
                    inst::size(inst::LOADARG)
                }
                (inst::LOADGLOBAL, inst::MODE_I64) => {
                    let i = read_imm!(u32, 1) as usize;
                    let v = pp.globals[i].value;
                    push!(v);
                    inst::size(inst::LOADGLOBAL)
                }
                (inst::LOADIMPORTGLOBAL, inst::MODE_I64) => {
                    let imp_index = read_imm!(u16, 1) as usize;
                    let index = read_imm!(u32, 1) as usize;
                    let v = pp.imports[imp_index].globals[index]
                        .link
                        .as_ref()
                        .unwrap()
                        .value;
                    push!(v);
                    inst::size(inst::LOADIMPORTGLOBAL)
                }
                (inst::LOADINDEXPROPORNIL, inst::MODE_LUA) => {
                    let index = NanBox(pop!());
                    let raw_receiver = NanBox(pop!());
                    let receiver: &Object = match raw_receiver.try_into() {
                        Ok(o) => o,
                        _ => return_errorf!("value is not an object: {:?}", raw_receiver),
                    };
                    let v = match index.try_into() {
                        Err(_) => NanBox::from_nil(),
                        Ok(key) => match receiver.property(key) {
                            None => NanBox::from_nil(),
                            Some(p) => receiver.property_value(p),
                        },
                    };
                    push!(v.0);
                    inst::size(inst::LOADINDEXPROPORNIL)
                }
                (inst::LOADLOCAL, inst::MODE_I64) => {
                    let i = read_imm!(u16, 1) as usize;
                    let v = *((fp as usize - (i + 1) * 8) as *const u64);
                    push!(v);
                    inst::size(inst::LOADLOCAL)
                }
                (inst::LOADNAMEDPROP, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let raw_receiver = NanBox(pop!());
                    let receiver: &Object = match raw_receiver.try_into() {
                        Ok(o) => o,
                        _ => return_errorf!("value is not an object: {:?}", raw_receiver),
                    };
                    let prop = match receiver.property(key) {
                        Some(p) => p,
                        None => return_errorf!("object does not have property {}", key),
                    };
                    let value = receiver.property_value(prop);
                    push!(value.0);
                    inst::size(inst::LOADNAMEDPROP)
                }
                (inst::LOADNAMEDPROPORNIL, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let receiver = NanBox(pop!());
                    let receiver_obj: &Object = match receiver.try_into() {
                        Ok(o) => o,
                        _ => return_errorf!("value is not an object: {:?}", receiver),
                    };
                    let value = match receiver_obj.property(key) {
                        Some(p) => receiver_obj.property_value(p),
                        None => NanBox::from_nil(),
                    };
                    push!(value.0);
                    inst::size(inst::LOADNAMEDPROPORNIL)
                }
                (inst::LOADPROTOTYPE, inst::MODE_OBJECT) => {
                    let v = pop!();
                    let o = (v as *const Object).as_ref().unwrap();
                    let p = o.prototype.unwrap();
                    push!(p as *const Object as u64);
                    inst::size(inst::LOADPROTOTYPE)
                }
                (inst::LOADPROTOTYPE, inst::MODE_LUA) => {
                    let v = NanBox(pop!());
                    let p = if let Ok(o) = <NanBox as TryInto<&Object>>::try_into(v) {
                        o.prototype.unwrap()
                    } else if let Ok(c) = <NanBox as TryInto<&Closure>>::try_into(v) {
                        c.prototype.unwrap()
                    } else {
                        return_errorf!("value is not an object: {:?}", v)
                    };
                    push!(p as *const Object as u64);
                    inst::size(inst::LOADPROTOTYPE)
                }
                (inst::LOADVARARGS, inst::MODE_LUA) => {
                    debug_assert!(func.var_param_type.is_some());
                    let argc = *((fp + FRAME_SIZE) as *const u64) as usize;
                    vc = argc - func.param_types.len();
                    let mut argp = fp + FRAME_SIZE + vc * 8;
                    let end = fp + FRAME_SIZE;
                    while argp != end {
                        let v = *(argp as *const u64);
                        argp -= 8;
                        push!(v);
                    }
                    inst::size(inst::LOADVARARGS)
                }
                (inst::LT, inst::MODE_I64) => {
                    binop_cmp!(<, i64);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_I32) => {
                    binop_cmp!(<, i32);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_I16) => {
                    binop_cmp!(<, i16);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_I8) => {
                    binop_cmp!(<, i8);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_U64) => {
                    binop_cmp!(<, u64);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_U32) => {
                    binop_cmp!(<, u32);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_U16) => {
                    binop_cmp!(<, u16);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_U8) => {
                    binop_cmp!(<, u8);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_F64) => {
                    binop_cmp!(<, f64);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_F32) => {
                    binop_cmp!(<, f32);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_LUA) => {
                    binop_cmp!(is_lt, lua);
                    inst::size(inst::LT)
                }
                (inst::MOD, inst::MODE_I64) => {
                    binop_num!(wrapping_rem, i64);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_I32) => {
                    binop_num!(wrapping_rem, i32);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_I16) => {
                    binop_num!(wrapping_rem, i16);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_I8) => {
                    binop_num!(wrapping_rem, i8);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_U64) => {
                    binop_num!(wrapping_rem, u64);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_U32) => {
                    binop_num!(wrapping_rem, u32);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_U16) => {
                    binop_num!(wrapping_rem, u16);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_U8) => {
                    binop_num!(wrapping_rem, u8);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_F64) => {
                    binop_num!(%, f64);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_F32) => {
                    binop_num!(%, f32);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    let v = if let (Ok(li), Ok(ri)) = (l.as_i64(), r.as_i64()) {
                        if ri == 0 {
                            return_errorf!("attempt to perform n%0");
                        }
                        let vi = li.wrapping_rem(ri);
                        maybe_box_int!(vi)
                    } else if let (Ok(lf), Ok(rf)) = (l.as_f64_imprecise(), r.as_f64_imprecise()) {
                        NanBox::from(lf.floor() % rf.floor())
                    } else {
                        return_errorf!(
                            "arithmetic operands must both be numbers: {:?} and {:?}",
                            l,
                            r
                        )
                    };
                    push!(v.0);
                    inst::size(inst::MOD)
                }
                (inst::MUL, inst::MODE_I64) => {
                    binop_num!(wrapping_mul, i64);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_I32) => {
                    binop_num!(wrapping_mul, i32);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_I16) => {
                    binop_num!(wrapping_mul, i16);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_I8) => {
                    binop_num!(wrapping_mul, i8);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_U64) => {
                    binop_num!(wrapping_mul, u64);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_U32) => {
                    binop_num!(wrapping_mul, u32);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_U16) => {
                    binop_num!(wrapping_mul, u16);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_U8) => {
                    binop_num!(wrapping_mul, u8);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_F64) => {
                    binop_num!(*, f64);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_F32) => {
                    binop_num!(*, f32);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_LUA) => {
                    binop_num!(*, checked_mul, lua);
                    inst::size(inst::MUL)
                }
                (inst::NANBOX, inst::MODE_I64) | (inst::NANBOX, inst::MODE_U64) => {
                    let i = pop!() as i64;
                    let v = maybe_box_int!(i);
                    push!(v.0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_I32) => {
                    push!(NanBox::try_from(pop!() as i32 as i64).unwrap().0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_I16) => {
                    push!(NanBox::try_from(pop!() as i16 as i64).unwrap().0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_I8) => {
                    push!(NanBox::try_from(pop!() as i8 as i64).unwrap().0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_U32) => {
                    push!(NanBox::try_from(pop!() as u32 as i64).unwrap().0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_U16) => {
                    push!(NanBox::try_from(pop!() as u16 as i64).unwrap().0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_U8) => {
                    push!(NanBox::try_from(pop!() as u8 as i64).unwrap().0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_F64) => {
                    push!(NanBox::from(f64::from_bits(pop!())).0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_F32) => {
                    push!(NanBox::from(f32::from_bits(pop!() as u32) as f64).0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_BOOL) => {
                    let v = pop!();
                    push!(NanBox::from(v != 0).0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_PTR) => {
                    if pop!() != 0 {
                        return_errorf!("can't box non-zero value as nil");
                    }
                    push!(NanBox::from_nil().0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_STRING) => {
                    push!(NanBox::from(pop!() as usize as *const data::String).0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_CLOSURE) => {
                    push!(NanBox::from(pop!() as usize as *const Closure).0);
                    inst::size(inst::NANBOX)
                }
                (inst::NANBOX, inst::MODE_OBJECT) => {
                    push!(NanBox::from(pop!() as usize as *const Object).0);
                    inst::size(inst::NANBOX)
                }
                (inst::NE, inst::MODE_I64) => {
                    binop_eq!(!=, i64);
                    inst::size(inst::NE)
                }
                (inst::NE, inst::MODE_F64) => {
                    binop_eq!(!=, f64);
                    inst::size(inst::NE)
                }
                (inst::NE, inst::MODE_F32) => {
                    binop_eq!(!=, f32);
                    inst::size(inst::NE)
                }
                (inst::NE, inst::MODE_LUA) => {
                    binop_eq!(!=, lua);
                    inst::size(inst::NE)
                }
                (inst::NEG, inst::MODE_I64) => {
                    unop_num!(-, i64);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_I32) => {
                    unop_num!(-, i32);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_I16) => {
                    unop_num!(-, i16);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_I8) => {
                    unop_num!(-, i8);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_F64) => {
                    unop_num!(-, f64);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_F32) => {
                    unop_num!(-, f32);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_LUA) => {
                    unop_num!(-, lua);
                    inst::size(inst::NEG)
                }
                (inst::NEWCLOSURE, inst::MODE_I64) => {
                    let fn_index = read_imm!(u32, 1) as usize;
                    let capture_count = read_imm!(u16, 5);
                    let bound_arg_count = read_imm!(u16, 7);
                    let f = &pp.functions[fn_index] as *const Function as usize as *mut Function;
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
                    push!(c as *const Closure as u64);
                    inst::size(inst::NEWCLOSURE)
                }
                (inst::NOP, inst::MODE_I64) => inst::size(inst::NOP),
                (inst::NOT, inst::MODE_BOOL) => {
                    let o = pop!() as u64;
                    let v = (o != 0) as u64;
                    push!(v);
                    inst::size(inst::NOT)
                }
                (inst::NOT, inst::MODE_LUA) => {
                    let o = NanBox(pop!());
                    let b = lua_value_as_bool!(o);
                    let n = NanBox::from(!b);
                    push!(n.0);
                    inst::size(inst::NOT)
                }
                (inst::NOTB, inst::MODE_I64) => {
                    unop_num!(!, i64);
                    inst::size(inst::NOTB)
                }
                (inst::NOTB, inst::MODE_I32) => {
                    unop_num!(!, i32);
                    inst::size(inst::NOTB)
                }
                (inst::NOTB, inst::MODE_I16) => {
                    unop_num!(!, i16);
                    inst::size(inst::NOTB)
                }
                (inst::NOTB, inst::MODE_I8) => {
                    unop_num!(!, i8);
                    inst::size(inst::NOTB)
                }
                (inst::NOTB, inst::MODE_LUA) => {
                    let v = NanBox(pop!());
                    let vi = lua_value_as_int!(v);
                    let b = !vi;
                    push!(maybe_box_int!(b).0);
                    inst::size(inst::NOTB)
                }
                (inst::OR, inst::MODE_LUA) => {
                    lua_binop_bit!(|);
                    inst::size(inst::OR)
                }
                (inst::PANIC, inst::MODE_STRING) => {
                    let s = (*(sp as *const *const data::String)).as_ref().unwrap();
                    return_errorf!("{}", s)
                }
                (inst::PANIC, inst::MODE_LUA) => {
                    let v = NanBox(*(sp as *const u64));
                    let s = v.to_string();
                    return_errorf!("{}", s)
                }
                (inst::POP, inst::MODE_I64) => {
                    sp += 8;
                    inst::size(inst::POP)
                }
                (inst::PROTOTYPE, inst::MODE_I64) => {
                    let c = cp.as_ref().unwrap();
                    let p = c.prototype.unwrap();
                    assert!(!p.is_null());
                    push!(p as u64);
                    inst::size(inst::PROTOTYPE)
                }
                (inst::RET, inst::MODE_I64) => {
                    let ret_sp = sp;
                    sp = arg_addr!(0);
                    func = match (*((fp + 24) as *const *const Function)).as_ref() {
                        Some(f) => f,
                        None => {
                            return Ok(());
                        }
                    };
                    pp = func.package.as_mut().unwrap();
                    cp = *((fp + 16) as *const *const Closure);
                    ip = *((fp + 8) as *const *const u8);
                    fp = *(fp as *const usize);
                    let v = *(ret_sp as *const u64);
                    *(sp as *mut u64) = v;
                    continue;
                }
                (inst::RETV, inst::MODE_LUA) => {
                    let mut retp = sp + vc * 8;
                    sp = arg_addr!(0) + 8;
                    func = match (*((fp + 24) as *const *const Function)).as_ref() {
                        Some(f) => f,
                        None => {
                            return Ok(());
                        }
                    };
                    pp = func.package.as_mut().unwrap();
                    cp = *((fp + 16) as *const *const Closure);
                    ip = *((fp + 8) as *const *const u8);
                    fp = *(fp as *const usize);
                    for _ in 0..vc {
                        sp -= 8;
                        retp -= 8;
                        *(sp as *mut u64) = *(retp as *const u64);
                    }
                    continue;
                }
                (inst::SHL, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    let li = lua_value_as_int!(l) as u64;
                    let ri = lua_value_as_int!(r);
                    let vi = if ri >= 64 {
                        0
                    } else if ri >= 0 {
                        li << ri
                    } else if ri >= -63 {
                        li >> -ri
                    } else {
                        0
                    };
                    push!(maybe_box_int!(vi as i64).0);
                    inst::size(inst::SHL)
                }
                (inst::SHR, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    let li = lua_value_as_int!(l) as u64;
                    let ri = lua_value_as_int!(r);
                    let vi = if ri >= 64 {
                        0
                    } else if ri >= 0 {
                        li >> ri
                    } else if ri >= -63 {
                        li << -ri
                    } else {
                        0
                    };
                    push!(maybe_box_int!(vi as i64).0);
                    inst::size(inst::SHR)
                }
                (inst::SETV, inst::MODE_LUA) => {
                    vc = read_imm!(u16, 1) as usize;
                    inst::size(inst::SETV)
                }
                (inst::STORE, inst::MODE_I64) => {
                    let v = pop!() as i64;
                    let p = pop!() as usize;
                    store!(i64, p, 0, 0, v);
                    inst::size(inst::STORE)
                }
                (inst::STORE, inst::MODE_I32) => {
                    let v = pop!() as i32;
                    let p = pop!() as usize;
                    store!(i32, p, 0, 0, v);
                    inst::size(inst::STORE)
                }
                (inst::STORE, inst::MODE_I16) => {
                    let v = pop!() as i16;
                    let p = pop!() as usize;
                    store!(i16, p, 0, 0, v);
                    inst::size(inst::STORE)
                }
                (inst::STORE, inst::MODE_I8) => {
                    let v = pop!() as i8;
                    let p = pop!() as usize;
                    store!(i8, p, 0, 0, v);
                    inst::size(inst::STORE)
                }
                (inst::STORE, inst::MODE_PTR) => {
                    let v = pop!() as usize;
                    let p = pop!() as usize;
                    store!(ptr, p, 0, 0, v);
                    inst::size(inst::STORE)
                }
                (inst::STORE, inst::MODE_LUA) => {
                    let v = pop!();
                    let p = pop!() as usize;
                    store!(lua, p, 0, 0, v);
                    inst::size(inst::STORE)
                }
                (inst::STOREARG, inst::MODE_I64) => {
                    let i = read_imm!(u16, 1) as usize;
                    let slot = arg_addr!(i);
                    let v = pop!();
                    *(slot as *mut u64) = v;
                    inst::size(inst::STOREARG)
                }
                (inst::STOREGLOBAL, inst::MODE_I64) => {
                    let i = read_imm!(u32, 1) as usize;
                    let v = pop!();
                    pp.globals[i].value = v;
                    inst::size(inst::STOREGLOBAL)
                }
                (inst::STOREINDEXPROP, inst::MODE_LUA) => {
                    let v = NanBox(pop!());
                    let i = NanBox(pop!());
                    let raw_receiver = NanBox(pop!());
                    let receiver: &mut Object = match raw_receiver.try_into() {
                        Ok(o) => o,
                        _ => return_errorf!("value is not an object: {:?}", raw_receiver),
                    };
                    let key = match i.try_into() {
                        Ok(key) => key,
                        Err(_) => return_errorf!("cannot use NaN as table key"),
                    };
                    receiver.set_property(key, PropertyKind::Field, v);
                    inst::size(inst::STOREINDEXPROP)
                }
                (inst::STORELOCAL, inst::MODE_I64) => {
                    let i = read_imm!(u16, 1) as usize;
                    let v = pop!();
                    *((fp as usize - (i + 1) * 8) as *mut u64) = v;
                    inst::size(inst::STORELOCAL)
                }
                (inst::STOREMETHOD, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let raw_method = NanBox(pop!());
                    if raw_method.type_tag() != nanbox::TAG_CLOSURE {
                        return_errorf!("method value is not a function: {:?}", raw_method);
                    }
                    let raw_receiver = NanBox(pop!());
                    let receiver: &mut Object = match raw_receiver.try_into() {
                        Ok(o) => o,
                        _ => return_errorf!("value is not an object: {:?}", raw_receiver),
                    };
                    receiver.set_own_property(key, PropertyKind::Method, raw_method);
                    inst::size(inst::STOREMETHOD)
                }
                (inst::STORENAMEDPROP, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let v = NanBox(pop!());
                    let raw_receiver = NanBox(pop!());
                    let receiver: &mut Object = match raw_receiver.try_into() {
                        Ok(o) => o,
                        _ => return_errorf!("value is not an object: {:?}", raw_receiver),
                    };
                    receiver.set_property(key, PropertyKind::Field, v);
                    inst::size(inst::STORENAMEDPROP)
                }
                (inst::STOREPROTOTYPE, inst::MODE_I64) => {
                    let prototype = pop!() as *mut Object;
                    let receiver = (pop!() as *mut Object).as_mut().unwrap();
                    receiver.prototype.set_ptr(prototype);
                    inst::size(inst::STOREPROTOTYPE)
                }
                (inst::STOREPROTOTYPE, inst::MODE_CLOSURE) => {
                    let prototype = pop!() as *mut Object;
                    let receiver = (pop!() as *mut Closure).as_mut().unwrap();
                    receiver.prototype.set_ptr(prototype);
                    inst::size(inst::STOREPROTOTYPE)
                }
                (inst::STRCAT, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    let ls = lua_concat_op_as_string!(l);
                    let rs = lua_concat_op_as_string!(r);
                    let cs = ls + rs;
                    push!(NanBox::from(cs).0);
                    inst::size(inst::STRCAT)
                }
                (inst::STRING, inst::MODE_I64) => {
                    let si = read_imm!(u32, 1) as usize;
                    let s = &pp.strings[si] as *const data::String as u64;
                    push!(s);
                    inst::size(inst::STRING)
                }
                (inst::SUB, inst::MODE_I64) => {
                    binop_num!(wrapping_sub, i64);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_I32) => {
                    binop_num!(wrapping_sub, i32);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_I16) => {
                    binop_num!(wrapping_sub, i16);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_I8) => {
                    binop_num!(wrapping_sub, i8);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_U64) => {
                    binop_num!(wrapping_sub, u64);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_U32) => {
                    binop_num!(wrapping_sub, u32);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_U16) => {
                    binop_num!(wrapping_sub, u16);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_U8) => {
                    binop_num!(wrapping_sub, u8);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_F64) => {
                    binop_num!(-, f64);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_F32) => {
                    binop_num!(-, f32);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_LUA) => {
                    binop_num!(-, checked_sub, lua);
                    inst::size(inst::SUB)
                }
                (inst::SWAP, inst::MODE_I64) => {
                    let a = pop!();
                    let b = pop!();
                    push!(a);
                    push!(b);
                    inst::size(inst::SWAP)
                }
                (inst::SWAPN, inst::MODE_I64) => {
                    let n = read_imm!(u8, 1) as usize;
                    let top = sp as *mut u64;
                    let slot = (sp + (n + 1) * 8) as *mut u64;
                    let v = *top;
                    *top = *slot;
                    *slot = v;
                    inst::size(inst::SWAPN)
                }
                (inst::SYS, inst::MODE_LUA) => {
                    let sys = read_imm!(u8, 1);
                    let mut args = vec![0; vc];
                    for i in 0..vc {
                        let argp = sp + (vc - i - 1) * 8;
                        args[i] = *(argp as *const u64);
                    }
                    match sys {
                        inst::SYS_PRINT => {
                            self.sys_print(&args)?;
                        }
                        _ => panic!("unknown sys {}", sys),
                    }
                    sp += vc * 8;
                    inst::size(inst::SYS)
                }
                (inst::TOFLOAT, inst::MODE_LUA) => {
                    let i = NanBox(pop!());
                    match i.as_f64_imprecise() {
                        Ok(o) => push!(o.to_bits()),
                        _ => return_errorf!("could not convert value of type {:?} to float", i),
                    }
                    inst::size(inst::TOFLOAT)
                }
                (inst::TYPEOF, inst::MODE_LUA) => {
                    let i = NanBox(pop!());
                    let o = i.type_tag();
                    push!(o);
                    inst::size(inst::TYPEOF)
                }
                (inst::XOR, inst::MODE_LUA) => {
                    lua_binop_bit!(^);
                    inst::size(inst::XOR)
                }
                (_, inst::MODE_I64) => {
                    panic!(
                        "{}",
                        Interpreter::error(
                            func,
                            ip,
                            format!("unknown opcode {} code {}", inst::mnemonic(op), op)
                        )
                    )
                }
                _ => panic!(
                    "{}",
                    Interpreter::error(
                        func,
                        ip,
                        format!(
                            "unknown opcode {}{} code {} {}",
                            inst::mnemonic(op),
                            inst::mode_mnemonic(mode),
                            mode,
                            op
                        )
                    )
                ),
            };
            ip = (ip as usize + inst_size) as *const u8;
        }
    }

    fn sys_print(&mut self, vs: &[u64]) -> Result<(), Error> {
        let mut sep = "";
        for v in vs {
            let _ = write!(self.w, "{}{}", sep, NanBox(*v));
            sep = " ";
        }
        let _ = write!(self.w, "\n");
        Ok(())
    }

    unsafe fn error(func: &Function, ip: *const u8, message: String) -> Error {
        let inst_offset = (ip as usize - &func.insts[0] as *const u8 as usize)
            .try_into()
            .unwrap();
        let position = func
            .package
            .as_ref()
            .unwrap()
            .line_map
            .position(inst_offset, &func.line_map);
        Error { position, message }
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
