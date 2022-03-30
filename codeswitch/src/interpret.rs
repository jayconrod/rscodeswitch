use crate::data;
use crate::heap::HEAP;
use crate::inst;
use crate::nanbox::{self, NanBox, NanBoxKey};
use crate::pos::{Error, Position};
use crate::runtime::{
    Closure, Function, LuaConvertedNumber, LuaRuntime, Object, PackageLoader, Property,
    PropertyKind,
};

use std::cell::RefCell;
use std::fmt::Display;
use std::fs;
use std::io::{Read, Write};
use std::mem;
use std::path::PathBuf;
use std::sync::Arc;

// Each stack frame consists of (with descending stack address):
//
//   - Caller: *const Function
//   - Caller's closure: *const Closure
//   - Return address: *const u8
//   - Caller's fp
const FRAME_SIZE: usize = 32;
const FRAME_FP_OFFSET: usize = 0;
const FRAME_IP_OFFSET: usize = 8;
const FRAME_CP_OFFSET: usize = 16;
const FRAME_FUNC_OFFSET: usize = 24;

// Error handlers may be pushed on the stack. Each error handler comprises:
//
// - Pointer to error handling code within the same function.
// - Pointer to next error handler on the stack or null.
const HANDLER_SIZE: usize = 16;
const HANDLER_HP_OFFSET: usize = 0;
const HANDLER_IP_OFFSET: usize = 8;

pub struct Env<'a> {
    pub r: &'a mut dyn Read,
    pub w: &'a mut dyn Write,
}

pub struct Interpreter<'a> {
    env: &'a RefCell<Env<'a>>,
    loader: Arc<PackageLoader>,
    lua_runtime: &'a dyn LuaRuntime,

    /// Holds the memory for the interpreter's stack.
    // TODO: remove this annotation. Check stack limits.
    #[allow(dead_code)]
    stack: Stack,

    // Below this point are "registers" used by the interpreter. The main loop
    // uses local variables, but they're saved here when calling a native
    // function.
    /// The function at the top of the stack being executed.
    func: *const Function,

    /// Value count. In Lua, this is the number of dynamic values in
    /// an expression list. Set before calling or returning from a function and
    /// when expanding "...".
    vc: usize,

    /// Closure pointer. Points to the current function's closure so that its
    /// cells may be accessed. cp is null if the function was called directly
    /// without a closure.
    cp: *const Closure,

    /// Stack pointer. Points to the value at the "top" of the stack, but like
    /// most architectures, the stack grows down.
    sp: usize,

    /// Frame pointer. Points to the current function's stack frame,
    /// specifically at the saved fp from the caller's stack frame.
    fp: usize,

    /// Instruction pointer. Points to the instruction being executed.
    ip: *const u8,

    /// Handler pointer. Acts as the head of a linked list of error handlers on
    /// the stack. Each error handler comprises a pointer to the next handler,
    /// and a pointer to code that should be executed.
    hp: usize,

    /// Error value. When an error occurs, this value is set, and error handlers
    /// (if any) are executed.
    error: Option<Error>,
}

impl<'a> Interpreter<'a> {
    pub fn new(
        env: &'a RefCell<Env<'a>>,
        loader: Arc<PackageLoader>,
        lua_runtime: &'a dyn LuaRuntime,
    ) -> Interpreter<'a> {
        let stack = Stack::new();
        let sp = stack.end() - FRAME_SIZE;
        let fp = sp;
        Interpreter {
            env,
            loader,
            lua_runtime,
            stack,
            func: 0 as *const Function,
            vc: 0,
            cp: 0 as *const Closure,
            sp,
            fp,
            ip: 0 as *const u8,
            hp: 0,
            error: None,
        }
    }

    pub fn interpret_closure(
        &mut self,
        closure: &Closure,
        args: &[u64],
    ) -> Result<Vec<u64>, Error> {
        unsafe {
            self.interpret_loop(
                closure.function.unwrap_ref(),
                closure as *const Closure,
                args,
            )
        }
    }

    pub unsafe fn interpret_function(
        &mut self,
        func: &Function,
        args: &[u64],
    ) -> Result<Vec<u64>, Error> {
        self.interpret_loop(func, 0 as *const Closure, args)
    }

    unsafe fn interpret_loop(
        &mut self,
        mut func: &Function,
        mut cp: *const Closure,
        args: &[u64],
    ) -> Result<Vec<u64>, Error> {
        // Load interpreter state into registers.
        let mut vc = self.vc;
        let mut pp = func.package.as_mut().unwrap();
        let mut sp = self.sp;
        let mut fp;
        let mut ip = &func.insts[0] as *const u8;
        let mut ret_sp; // used to return at the end
        let mut hp = 0;

        // Construct the stack frame.
        for i in 0..args.len() {
            sp -= 8;
            *(sp as *mut u64) = args[i];
        }
        sp -= FRAME_SIZE;
        *((sp + FRAME_FUNC_OFFSET) as *mut *const Function) = self.func;
        *((sp + FRAME_CP_OFFSET) as *mut *const Closure) = self.cp;
        *((sp + FRAME_IP_OFFSET) as *mut *const u8) = self.ip;
        *((sp + FRAME_FP_OFFSET) as *mut usize) = self.fp;
        fp = sp;

        // save_regs writes the local values of ip and other registers into the
        // Interpreter object.
        macro_rules! save_regs {
            () => {{
                self.func = func;
                self.vc = vc;
                self.cp = cp;
                self.sp = sp;
                self.fp = fp;
                self.ip = ip;
                self.hp = hp;
            }};
        }

        // load_regs reads the the local values of ip and other registers from
        // the Interpreter object.
        macro_rules! load_regs {
            () => {
                #[allow(unused_assignments)] // for vc
                {
                    func = self.func.as_ref().unwrap();
                    pp = func.package.as_mut().unwrap();
                    vc = self.vc;
                    cp = self.cp;
                    sp = self.sp;
                    fp = self.fp;
                    ip = self.ip;
                    hp = self.hp;
                }
            };
        }

        // unwindw_errorf constructs an error and begins unwinding the stack.
        // If there's an error handler (pushhandler), the stack will be unwound
        // to that point, and it will be executed next. Otherwise, the
        // interpreter's state is cleared, and the error is returned
        // immediately.
        macro_rules! unwind_errorf {
            ($($x:expr),*) => {{
                save_regs!();
                let message = format!($($x,)*);
                let error = self.error(message);
                match self.unwind_with_error(error) {
                    Ok(()) => {
                        load_regs!();
                        continue;
                    },
                    Err(err) => return Err(err),
                }
            }};
        }

        // return_ok returns normally from a function, popping the stack frame.
        // If the return address is non-zero, return_ok moves results into the
        // caller's stack frame and continues. If the return address is zero,
        // return_ok leaves ret_sp pointing to the last result and breaks.
        macro_rules! return_ok {
            ($retc:expr) => {{
                let retc = $retc;
                ret_sp = sp;
                sp = arg_addr!(0) + 8;
                let func_ptr = *((fp + FRAME_FUNC_OFFSET) as *const *const Function);
                cp = *((fp + FRAME_CP_OFFSET) as *const *const Closure);
                ip = *((fp + FRAME_IP_OFFSET) as *const *const u8);
                fp = *((fp + FRAME_FP_OFFSET) as *const usize);
                if ip.is_null() {
                    break;
                }
                func = func_ptr.as_ref().unwrap();
                pp = func.package.as_mut().unwrap();
                for i in 0..retc {
                    let retp = ret_sp + (retc - i - 1) * 8;
                    let ret = *(retp as *const u64);
                    push!(ret);
                }
                continue;
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

        // call_function pushes a stack frame and sets registers, beginning a
        // call to the given function. The next instruction executed will be the
        // first in the function. After the function returns, the next
        // instruction will be the one after the current instruction.
        macro_rules! call_function {
            ($callee:expr, $arg_count:expr) => {{
                let callee: *const Function = $callee;
                let callee_func = callee.as_ref().unwrap();
                let arg_count: usize = $arg_count;
                if callee_func.var_param_type.is_some() {
                    push!(arg_count as u64);
                    vc = arg_count - callee_func.param_types.len();
                } else {
                    debug_assert_eq!(callee_func.param_types.len(), arg_count);
                    vc = 0;
                }
                sp -= FRAME_SIZE;
                *((sp + FRAME_FUNC_OFFSET) as *mut u64) = func as *const Function as u64;
                func = callee_func;
                *((sp + FRAME_CP_OFFSET) as *mut u64) = cp as u64;
                cp = 0 as *const Closure;
                *((sp + FRAME_IP_OFFSET) as *mut u64) = ip as u64 + inst::size(*ip) as u64;
                ip = &callee_func.insts[0] as *const u8;
                *((sp + FRAME_FP_OFFSET) as *mut u64) = fp as u64;
                fp = sp;
                pp = func.package.as_mut().unwrap();
            }};
        }

        macro_rules! call_closure {
            ($callee:expr, $arg_count:expr) => {{
                let callee: &Closure = $callee;
                let arg_count: usize = $arg_count;
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

                // If the callee is not variadic and the number of arguments
                // differs from the number of parameters, or if the callee is
                // variadic and there are too few arguments, raise an error.
                // If the callee is variadic, push the number of arguments
                // and set vc to the number of variadic arguments.
                let total_arg_count = arg_count + callee.bound_arg_count as usize;
                if total_arg_count > u16::MAX as usize {
                    unwind_errorf!("too many arguments");
                }
                let param_count = callee_func.param_types.len();
                if total_arg_count < param_count
                    || (callee_func.var_param_type.is_none() && total_arg_count > param_count)
                {
                    unwind_errorf!(
                        "wrong number of arguments: want {}, got {}",
                        param_count,
                        total_arg_count
                    );
                }
                if callee_func.var_param_type.is_some() {
                    push!(total_arg_count as u64);
                    vc = total_arg_count - param_count;
                } else {
                    vc = 0;
                }

                // Constrct a stack frame for the callee and set the registers
                // so the function's instructions, cells, and package will be
                // used.
                sp -= FRAME_SIZE;
                *((sp + FRAME_FUNC_OFFSET) as *mut u64) = func as *const Function as u64;
                func = callee_func;
                *((sp + FRAME_CP_OFFSET) as *mut u64) = cp as u64;
                cp = callee;
                *((sp + FRAME_IP_OFFSET) as *mut u64) = ip as u64 + inst::size(*ip) as u64;
                ip = &callee_func.insts[0] as *const u8;
                *((sp + FRAME_FP_OFFSET) as *mut u64) = fp as u64;
                fp = sp;
                pp = callee_func.package.as_mut().unwrap();
            }};
        }

        // lua_try_meta_unop! checks if the operand is a table with the named
        // metamethod. If so, the method is called. It's an error if the
        // metatable has a non-nil, non-callable property. If the operand does
        // not have the metamethod, control falls through.
        macro_rules! lua_try_meta_unop {
            ($i:expr, $name:literal) => {{
                let i = $i;
                if let Some(mm) = Interpreter::lua_load_meta_value(i, $name) {
                    let c: &Closure = match mm.try_into() {
                        Ok(c) => c,
                        _ => unwind_errorf!("metamethod '{}' is not a function", $name),
                    };
                    push!(NanBox::from(c).0);
                    push!(i.0);
                    let adjust1 = self.lua_load_std_function("_adjust1").unwrap();
                    call_function!(adjust1, 2);
                    continue;
                }
            }};
        }

        // lua_try_meta_binop! checks if the left value is a table with the
        // named metamethod, then checks the same on the right. If one of the
        // values has the metamethod, both values are pushed, and the method
        // is called. It's an error if a metatable has a non-nil, non-callable
        // property. If neither value has the metamethod, control falls through.
        macro_rules! lua_try_meta_binop {
            ($l:expr, $r:expr, $name:literal) => {{
                let l = $l;
                let r = $r;
                let name = $name;
                let mut mm: Option<&Closure> = None;
                if let Some(lmm) = Interpreter::lua_load_meta_value(l, name) {
                    match lmm.try_into() {
                        Ok(c) => {
                            mm = Some(c);
                        }
                        _ => unwind_errorf!("metamethod '{}' is not a function", name),
                    };
                } else if let Some(rmm) = Interpreter::lua_load_meta_value(r, name) {
                    match rmm.try_into() {
                        Ok(c) => {
                            mm = Some(c);
                        }
                        _ => unwind_errorf!("metamethod '{}' is not a function", name),
                    };
                }
                if let Some(c) = mm {
                    push!(NanBox::from(c).0);
                    push!(l.0);
                    push!(r.0);
                    let adjust1 = self.lua_load_std_function("_adjust1").unwrap();
                    call_function!(adjust1, 3);
                    continue;
                }
            }};
        }

        // lua_meta_index implements the table[key] expression. If the
        // receiver is not a table, an error is raised. If the key is in the
        // table, its value is returned. If the table has an __index metavalue
        // that is a function, the function is called. If the table has a
        // non-nil __index metavalue, the index operation is retried with that
        // value as the receiver. If __index is nil or not present, control
        // falls through.
        macro_rules! lua_meta_index {
            ($receiver:expr, $key:expr, $mainloop:tt) => {{
                let mut receiver: NanBox = $receiver;
                let key: NanBoxKey = $key;
                let mut result: Option<NanBox>;
                loop {
                    let receiver_obj: &Object = match receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("value is not an object: {:?}", receiver),
                    };
                    result = receiver_obj.own_property(key);
                    if result.is_some() {
                        break;
                    }
                    let meta_value_opt = receiver_obj.prototype.as_ref()
                        .and_then(|p| p.own_named_property(b"__index"))
                        .filter(|m| !m.is_nil());
                    let meta_value = match meta_value_opt {
                        Some(v) => v,
                        None => {break;}
                    };
                    if let Ok(c) = <NanBox as TryInto<&Closure>>::try_into(meta_value) {
                        push!(NanBox::from(c).0);
                        push!(NanBox::from(receiver).0);
                        push!(NanBox::from(key).0);
                        let adjust1 = self.lua_load_std_function("_adjust1").unwrap();
                        call_function!(adjust1, 3);
                        continue $mainloop;
                    }
                    receiver = meta_value;
                }
                result
            }};
        }

        // lua_meta_newindex implements 'table[key] = value' assignment. If the
        // receiver is not a table, an error is raised. If the key is in the
        // table, its value is replaced with the given value. If the table has
        // a __newindex metavalue that is a function, the function is called.
        // If the table has a non-nil __newindex metavalue, the operation is
        // retried with that value as the receiver. If __newindex is nil or
        // not present, a new property is added to the receiver.
        macro_rules! lua_meta_newindex {
            ($receiver:expr, $key:expr, $value:expr, $mainloop:tt) => {{
                let mut receiver: NanBox = $receiver;
                let key: NanBoxKey = $key;
                let value: NanBox = $value;
                loop {
                    let receiver_obj: &mut Object = match receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("value is not an object: {:?}", receiver),
                    };
                    if receiver_obj.lookup_own_property(key).is_some() {
                        receiver_obj.set_property(key, PropertyKind::Field, value);
                        break;
                    }
                    let meta_value_opt = receiver_obj.prototype.as_ref()
                        .and_then(|p| p.own_named_property(b"__newindex"))
                        .filter(|m| !m.is_nil());
                    let meta_value = match meta_value_opt {
                        Some(v) => v,
                        None => {
                            receiver_obj.set_property(key, PropertyKind::Field, value);
                            break;
                        }
                    };
                    if let Ok(c) = <NanBox as TryInto<&Closure>>::try_into(meta_value) {
                        push!(NanBox::from(c).0);
                        push!(receiver.0);
                        push!(NanBox::from(key).0);
                        push!(value.0);
                        let adjust0 = self.lua_load_std_function("_adjust0").unwrap();
                        call_function!(adjust0, 4);
                        continue $mainloop;
                    }
                    receiver = meta_value;
                }
            }};
        }

        // binop_eq! implements the == and != operators.
        macro_rules! binop_eq {
            (f32, $op:tt) => {{
                let r = pop_float!(f32);
                let l = pop_float!(f32);
                let v = (l $op r) as u64;
                push!(v);
            }};
            (f64, $op:tt) => {{
                let r = pop_float!(f64);
                let l = pop_float!(f64);
                let v = (l $op r) as u64;
                push!(v);
            }};
            (box, $op:tt) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                let v = NanBox::from(l $op r);
                push!(v.0);
            }};
            (lua, $op:tt, $name:literal) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                lua_try_meta_binop!(l, r, $name);
                let v = NanBox::from(l $op r);
                push!(v.0)
            }};
            ($ty:ty, $op:tt) => {{
                let r = pop!() as $ty;
                let l = pop!() as $ty;
                let v = (l $op r) as u64;
                push!(v);
            }};
        }

        // binop_cmp! implements the <, <=, >, >= operators.
        macro_rules! binop_cmp {
            (f32, $op:tt) => {{
                let r = pop_float!(f32);
                let l = pop_float!(f32);
                let v = (l $op r) as u64;
                push!(v);
            }};
            (f64, $op:tt) => {{
                let r = pop_float!(f64);
                let l = pop_float!(f64);
                let v = (l $op r) as u64;
                push!(v);
            }};
            (box, $ordmethod:ident) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                let v = if let Some(c) = l.partial_cmp(&r) {
                    NanBox::from(c.$ordmethod())
                } else {
                    unwind_errorf!("can't compare values: {:?} and {:?}", l, r);
                };
                push!(v.0)
            }};
            (lua, $ordmethod:ident, $name:literal) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                lua_try_meta_binop!(l, r, $name);
                let v = if let Some(c) = l.partial_cmp(&r) {
                    NanBox::from(c.$ordmethod())
                } else {
                    unwind_errorf!("can't compare values: {:?} and {:?}", l, r);
                };
                push!(v.0)
            }};
            ($ty:ty, $op:tt) => {{
                let r = pop!() as $ty;
                let l = pop!() as $ty;
                let v = (l $op r) as u64;
                push!(v);
            }};
        }

        // binop_num! implements numeric operators that produce a value of
        // the same type.
        macro_rules! binop_num {
            (f32, $op:tt) => {{
                let r = pop_float!(f32);
                let l = pop_float!(f32);
                let v = l $op r;
                push_float!(v, f32);
            }};
            (f64, $op:tt) => {{
                let r = pop_float!(f64);
                let l = pop_float!(f64);
                let v = l $op r;
                push_float!(v, f64);
            }};
            (box, $op:tt, $checked:ident) => {{
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
                    unwind_errorf!("arithmetic operands must both be numbers: {:?} and {:?}", l, r)
                };
                push!(v.0);
            }};
            (lua, $op:tt, $checked:ident, $name:literal) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                lua_try_meta_binop!(l, r, $name);
                let v = if let (Ok(li), Ok(ri)) = (<NanBox as TryInto<i64>>::try_into(l), <NanBox as TryInto<i64>>::try_into(r)) {
                    match li.$checked(ri) {
                        Some(vi) => maybe_box_int!(vi),
                        None => NanBox::from((li as f64) $op (ri as f64))
                    }
                } else if let (Ok(lf), Ok(rf)) = (l.as_f64(), r.as_f64()) {
                    NanBox::from(lf $op rf)
                } else {
                    unwind_errorf!("arithmetic operands must both be numbers: {:?} and {:?}", l, r)
                };
                push!(v.0);
            }};
            ($ty:ty, $wrapping:ident) => {{
                let r = pop!() as $ty;
                let l = pop!() as $ty;
                let v = l.$wrapping(r) as u64;
                push!(v);
            }};
        }

        // unop_num! implements unary numeric operators that produce a value
        // of the same type.
        macro_rules! unop_num {
            (f32, $op:tt) => {{
                let v = pop_float!(f32);
                let r = $op v;
                push_float!(r, f32);
            }};
            (f64, $op:tt) => {{
                let v = pop_float!(f64);
                let r = $op v;
                push_float!(r, f64);
            }};
            (box, $op:tt) => {{
                let o = NanBox(pop!());
                let v = if let Ok(i) = <NanBox as TryInto<i64>>::try_into(o) {
                    maybe_box_int!($op i)
                } else if let Ok(f) = o.as_f64() {
                    NanBox::from($op f)
                } else {
                    unwind_errorf!("arithmetic operand must be number: {:?}", o)
                };
                push!(v.0);
            }};
            (lua, $op:tt, $name:literal) => {{
                let o = NanBox(pop!());
                lua_try_meta_unop!(o, $name);
                let v = if let Ok(i) = <NanBox as TryInto<i64>>::try_into(o) {
                    maybe_box_int!($op i)
                } else if let Ok(f) = o.as_f64() {
                    NanBox::from($op f)
                } else {
                    unwind_errorf!("arithmetic operand must be number: {:?}", o)
                };
                push!(v.0);
            }};
            ($ty:ty, $op:tt) => {{
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
            ($index:expr) => {
                arg_addr!($index, fp)
            };
            ($index:expr, $fp:expr) => {{
                let fp = $fp;
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
                    unwind_errorf!("number has no integer representation")
                } else {
                    unwind_errorf!("cannot perform numeric operation on {:?} value", v)
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
                    unwind_errorf!("can't convert concatenation operand to string: {:?}", v)
                }
            }};
        }

        // lua_binop_bit implements the &, |, and ~ binary operators for Lua.
        // It unboxes its operands and converts them to integers, reporting an
        // error if either is not a number. It then performs the operation,
        // boxes, and pushes the result.
        macro_rules! lua_binop_bit {
            ($op:tt, $name:literal) => {{
                let r = NanBox(pop!());
                let l = NanBox(pop!());
                lua_try_meta_binop!(l, r, $name);
                let li = lua_value_as_int!(l);
                let ri = lua_value_as_int!(r);
                let v = li $op ri;
                push!(maybe_box_int!(v).0);
            }};
        }

        macro_rules! lua_call_closure {
            ($callee:expr, $arg_count:expr) => {{
                let callee: NanBox = $callee;
                let arg_count: usize = $arg_count;

                // If the callee is not a function, try the __call metamethod.
                let callee_closure = if let Ok(c) = <NanBox as TryInto<&Closure>>::try_into(callee)
                {
                    c
                } else if let Some(v) = Interpreter::lua_load_meta_value(callee, "__call") {
                    match v.try_into() {
                        Ok(c) => c,
                        _ => unwind_errorf!("metamethod '__call' is not a function"),
                    }
                } else {
                    unwind_errorf!("called value is not a function")
                };
                let callee_func = callee_closure.function.unwrap_ref();

                // If the callee has bound arguments, insert them on the stack
                // before the regular arguments.
                if callee_closure.bound_arg_count > 0 {
                    let bound_arg_begin = sp + arg_count * 8 - 8;
                    let delta = callee_closure.bound_arg_count as usize * 8;
                    let mut from = sp;
                    sp -= delta;
                    let mut to = sp;
                    while from <= bound_arg_begin {
                        *(to as *mut u64) = *(from as *mut u64);
                        to += 8;
                        from += 8;
                    }
                    for i in 0..callee_closure.bound_arg_count {
                        let to = (bound_arg_begin - i as usize * 8) as *mut u64;
                        *to = callee_closure.bound_arg(i);
                    }
                }

                // If there are fewer arguments than parameters, push nils. If
                // the callee is variadic, push the number of arguments,
                // including pushed nils. If the callee is not variadic and
                // there are more arguments than parameters, pop the extra
                // arguments.
                let mut total_arg_count = arg_count + callee_closure.bound_arg_count as usize;
                if total_arg_count > u16::MAX as usize {
                    unwind_errorf!("too many arguments");
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
                    vc = total_arg_count - param_count;
                } else {
                    sp += (total_arg_count - param_count) * 8;
                    vc = 0;
                }

                // Construct a stack frame for the callee, and set the
                // "registers" so the function's instructions, cells,
                // and package will be used.
                sp -= FRAME_SIZE;
                *((sp as usize + 24) as *mut u64) = func as *const Function as u64;
                func = callee_func;
                *((sp as usize + 16) as *mut u64) = cp as u64;
                cp = callee_closure;
                *((sp as usize + 8) as *mut u64) = ip as u64 + inst::size(*ip) as u64;
                ip = &func.insts[0] as *const u8;
                *(sp as *mut u64) = fp as u64;
                fp = sp;
                pp = callee_func.package.as_mut().unwrap();
            }};
        }

        // Main loop
        'mainloop: loop {
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
                    binop_num!(i64, wrapping_add);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_I32) => {
                    binop_num!(i32, wrapping_add);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_I16) => {
                    binop_num!(i16, wrapping_add);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_I8) => {
                    binop_num!(i8, wrapping_add);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_U64) => {
                    binop_num!(u64, wrapping_add);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_U32) => {
                    binop_num!(u32, wrapping_add);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_U16) => {
                    binop_num!(u16, wrapping_add);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_U8) => {
                    binop_num!(u8, wrapping_add);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_F64) => {
                    binop_num!(f64, +);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_F32) => {
                    binop_num!(f32, +);
                    inst::size(inst::ADD)
                }
                (inst::ADD, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    lua_try_meta_binop!(l, r, "__add");
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
                        unwind_errorf!(
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
                    let ti = read_imm!(u32, 1) as usize;
                    let size = pp.types[ti].size();
                    push!(HEAP.allocate(size) as u64);
                    inst::size(inst::ALLOC)
                }
                (inst::AND, inst::MODE_LUA) => {
                    lua_binop_bit!(&, "__band");
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
                (inst::CALLHANDLER, inst::MODE_I64) => {
                    // Pop and execute an error handler but prepare to continue
                    // normal execution afterward. Used in the non-error case
                    // for constructs like "finally" where code must be run
                    // whether there's an error or not.
                    sp -= FRAME_SIZE;
                    *((sp + FRAME_FUNC_OFFSET) as *mut *const Function) = func;
                    *((sp + FRAME_CP_OFFSET) as *mut *const Closure) = cp;
                    *((sp + FRAME_IP_OFFSET) as *mut usize) =
                        (ip as usize) + inst::size(inst::CALLHANDLER);
                    *((sp + FRAME_FP_OFFSET) as *mut usize) = fp;
                    fp = sp;
                    ip = *((hp + HANDLER_IP_OFFSET) as *const *const u8);
                    hp = *((hp + HANDLER_HP_OFFSET) as *const usize);
                    continue;
                }
                (inst::CALLNAMEDPROP, inst::MODE_BOX) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let arg_count = read_imm!(u16, 5) as usize;
                    let receiver_addr = sp + arg_count * 8;
                    let receiver = NanBox(*(receiver_addr as *const u64));
                    let receiver_obj: &Object = match receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("receiver is not an object: {:?}", receiver),
                    };
                    let prop = match receiver_obj.lookup_property(key) {
                        Some(p) => p,
                        _ => unwind_errorf!("property {} is not defined", name),
                    };
                    let callee: &Closure = match prop.value.try_into() {
                        Ok(c) => c,
                        _ => unwind_errorf!("property {} is not a function", name),
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
                (inst::CALLNAMEDPROP, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let arg_count = read_imm!(u16, 5) as usize;
                    let receiver_addr = sp + arg_count * 8;
                    let receiver = NanBox(*(receiver_addr as *const u64));
                    let receiver_obj: &Object = match receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("receiver is not an object: {:?}", receiver),
                    };
                    let prop = match receiver_obj.lookup_property(key) {
                        Some(p) => p,
                        _ => unwind_errorf!("property {} is not defined", name),
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
                    lua_call_closure!(prop.value, arg_count_including_receiver);
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
                        _ => unwind_errorf!("receiver is not an object: {:?}", raw_receiver),
                    };
                    let prop = match receiver.lookup_property(key) {
                        Some(p) => p,
                        _ => unwind_errorf!("property {} is not defined", name),
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
                    lua_call_closure!(prop.value, arg_count_including_receiver);
                    continue;
                }
                (inst::CALLNAMEDPROPWITHPROTOTYPE, inst::MODE_BOX) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let arg_count = read_imm!(u16, 5) as usize;
                    let prototype_addr = sp + arg_count * 8;
                    let prototype = NanBox(*(prototype_addr as *const u64));
                    let prototype_obj: &Object = match prototype.try_into() {
                        Ok(p) => p,
                        _ => unwind_errorf!("prototype is not an object: {:?}", prototype),
                    };
                    let prop = match prototype_obj.lookup_property(key) {
                        Some(p) => p,
                        _ => unwind_errorf!("property {} is not defined", key),
                    };
                    let callee: &Closure = match prop.value.try_into() {
                        Ok(c) => c,
                        _ => unwind_errorf!("property {} is not a function", name),
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
                (inst::CALLVALUE, inst::MODE_BOX) => {
                    let arg_count = read_imm!(u16, 1) as usize;
                    let callee_addr = sp + arg_count * 8;
                    let callee = NanBox(*(callee_addr as *const u64));
                    let callee_closure: &Closure = match callee.try_into() {
                        Ok(c) => c,
                        _ => unwind_errorf!("called value is not a function"),
                    };
                    // Remove the callee from the stack before the call.
                    // CALLNAMEDPROP does this too when the called property
                    // is a field instead of a method. See comment there.
                    // TODO: this is a terrible, inefficient solution.
                    shift_args!(arg_count, 1);
                    call_closure!(callee_closure, arg_count);
                    continue;
                }
                (inst::CALLVALUE, inst::MODE_LUA) => {
                    let arg_count = read_imm!(u16, 1) as usize;
                    let callee_addr = sp + arg_count * 8;
                    let callee = NanBox(*(callee_addr as *const u64));
                    // Remove the callee from the stack before the call.
                    // CALLNAMEDPROP does this too when the called property
                    // is a field instead of a method. See comment there.
                    // TODO: this is a terrible, inefficient solution.
                    shift_args!(arg_count, 1);
                    lua_call_closure!(callee, arg_count);
                    continue;
                }
                (inst::CALLVALUEV, inst::MODE_LUA) => {
                    // Calls a function or value with __call metamethod with
                    // a variable number of arguments. Used for calls where the
                    // last expression expands to a variable number of values
                    // (like a call or '...'). vc must contain the total number
                    // of arguments.
                    let callee_addr = sp + vc * 8;
                    let callee = NanBox(*(callee_addr as *const u64));
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
                (inst::CONST, inst::MODE_I64) => {
                    let v = read_imm!(u64, 1);
                    push!(v);
                    inst::size(inst::CONST)
                }
                (inst::CONSTZERO, _) => {
                    push!(0);
                    inst::size(inst::CONSTZERO)
                }
                (inst::DIV, inst::MODE_I64) => {
                    binop_num!(i64, wrapping_div);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_I32) => {
                    binop_num!(i32, wrapping_div);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_I16) => {
                    binop_num!(i16, wrapping_div);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_I8) => {
                    binop_num!(i8, wrapping_div);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_U64) => {
                    binop_num!(u64, wrapping_div);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_U32) => {
                    binop_num!(u32, wrapping_div);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_U16) => {
                    binop_num!(u16, wrapping_div);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_U8) => {
                    binop_num!(u8, wrapping_div);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_F64) => {
                    binop_num!(f64, /);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_F32) => {
                    binop_num!(f32, /);
                    inst::size(inst::DIV)
                }
                (inst::DIV, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    lua_try_meta_binop!(l, r, "__div");
                    let v = if let (Ok(lf), Ok(rf)) = (l.as_f64_imprecise(), r.as_f64_imprecise()) {
                        NanBox::from(lf / rf)
                    } else {
                        unwind_errorf!(
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
                    binop_eq!(i64, ==);
                    inst::size(inst::EQ)
                }
                (inst::EQ, inst::MODE_F64) => {
                    binop_eq!(f64, ==);
                    inst::size(inst::EQ)
                }
                (inst::EQ, inst::MODE_F32) => {
                    binop_eq!(f32, ==);
                    inst::size(inst::EQ)
                }
                (inst::EQ, inst::MODE_BOX) => {
                    binop_eq!(box, ==);
                    inst::size(inst::EQ)
                }
                (inst::EQ, inst::MODE_LUA) => {
                    binop_eq!(lua, ==, "__eq");
                    inst::size(inst::EQ)
                }
                (inst::EXP, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    lua_try_meta_binop!(l, r, "__pow");
                    let v = if let (Ok(lf), Ok(rf)) = (l.as_f64_imprecise(), r.as_f64_imprecise()) {
                        NanBox::from(f64::powf(lf, rf))
                    } else {
                        unwind_errorf!(
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
                    lua_try_meta_binop!(l, r, "__idiv");
                    let v = if let (Ok(li), Ok(ri)) = (l.as_i64(), r.as_i64()) {
                        maybe_box_int!(li / ri)
                    } else if let (Ok(lf), Ok(rf)) = (l.as_f64_imprecise(), r.as_f64_imprecise()) {
                        NanBox::from(lf.floor() / rf.floor())
                    } else {
                        unwind_errorf!(
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
                    binop_cmp!(i64, >=);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_I32) => {
                    binop_cmp!(i32, >=);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_I16) => {
                    binop_cmp!(i16, >=);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_I8) => {
                    binop_cmp!(i8, >=);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_U64) => {
                    binop_cmp!(u64, >=);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_U32) => {
                    binop_cmp!(u32, >=);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_U16) => {
                    binop_cmp!(u16, >=);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_U8) => {
                    binop_cmp!(u8, >=);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_F64) => {
                    binop_cmp!(f64, >=);
                    inst::size(inst::GE)
                }
                (inst::GE, inst::MODE_F32) => {
                    binop_cmp!(f32, >=);
                    inst::size(inst::GE)
                }
                (inst::GETERROR, inst::MODE_LUA) => {
                    // Box and push the current error value, or push nil if
                    // there is no error.
                    let v = match &self.error {
                        Some(e) => {
                            let s = data::String::from_bytes(e.to_string().as_bytes());
                            NanBox::from(s)
                        }
                        None => NanBox::from_nil(),
                    };
                    push!(v.0);
                    inst::size(inst::GETERROR)
                }
                (inst::GETV, inst::MODE_I64) => {
                    push!(vc as u64);
                    inst::size(inst::GETV)
                }
                (inst::GT, inst::MODE_I64) => {
                    binop_cmp!(i64, >);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_I32) => {
                    binop_cmp!(i32, >);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_I16) => {
                    binop_cmp!(i16, >);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_I8) => {
                    binop_cmp!(i8, >);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_U64) => {
                    binop_cmp!(u64, >);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_U32) => {
                    binop_cmp!(u32, >);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_U16) => {
                    binop_cmp!(u16, >);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_U8) => {
                    binop_cmp!(u8, >);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_F64) => {
                    binop_cmp!(f64, >);
                    inst::size(inst::GT)
                }
                (inst::GT, inst::MODE_F32) => {
                    binop_cmp!(f32, >);
                    inst::size(inst::GT)
                }
                (inst::LE, inst::MODE_I64) => {
                    binop_cmp!(i64, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_I32) => {
                    binop_cmp!(i32, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_I16) => {
                    binop_cmp!(i16, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_I8) => {
                    binop_cmp!(i8, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_U64) => {
                    binop_cmp!(u64, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_U32) => {
                    binop_cmp!(u32, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_U16) => {
                    binop_cmp!(u16, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_U8) => {
                    binop_cmp!(u8, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_F64) => {
                    binop_cmp!(f64, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_F32) => {
                    binop_cmp!(f32, <=);
                    inst::size(inst::LE)
                }
                (inst::LE, inst::MODE_LUA) => {
                    binop_cmp!(lua, is_le, "__le");
                    inst::size(inst::LE)
                }
                (inst::LEN, inst::MODE_BOX) => {
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
                            match o.lookup_own_array_property(n) {
                                Some(Property { value, .. }) if !value.is_nil() => break,
                                _ => (),
                            }
                            n -= 1;
                        }
                        n
                    } else {
                        unwind_errorf!("value is not an object: {:?}", o);
                    };
                    push!(maybe_box_int!(v).0);
                    inst::size(inst::LEN)
                }
                (inst::LEN, inst::MODE_LUA) => {
                    let o = NanBox(pop!());
                    lua_try_meta_unop!(o, "__len");
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
                            match o.lookup_own_array_property(n) {
                                Some(Property { value, .. }) if !value.is_nil() => break,
                                _ => (),
                            }
                            n -= 1;
                        }
                        n
                    } else {
                        unwind_errorf!("value is not an object: {:?}", o);
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
                (inst::LOADARGPARENT, inst::MODE_I64) => {
                    // Like LOADARG, but loads from the caller's frame instead
                    // of the current frame. The caller must be an instance of
                    // the same function. Used by error handlers.
                    let i = read_imm!(u16, 1) as usize;
                    let caller_fp = *((fp + FRAME_FP_OFFSET) as *const usize);
                    let slot = arg_addr!(i, caller_fp);
                    let v = *(slot as *const u64);
                    push!(v);
                    inst::size(inst::LOADARGPARENT)
                }
                (inst::LOADERROR, inst::MODE_LUA) => {
                    // Box and push the current error value. Push nil if there
                    // is no error.
                    let v = match &self.error {
                        None => NanBox::from_nil(),
                        Some(err) => {
                            let str = data::String::from_bytes(err.to_string().as_bytes());
                            NanBox::from(str)
                        }
                    };
                    push!(v.0);
                    inst::size(inst::LOADERROR)
                }
                (inst::LOADGLOBAL, inst::MODE_I64) => {
                    let i = read_imm!(u32, 1) as usize;
                    let v = pp.globals[i].value;
                    push!(v);
                    inst::size(inst::LOADGLOBAL)
                }
                (inst::LOADIMPORTGLOBAL, inst::MODE_I64) => {
                    let imp_index = read_imm!(u16, 1) as usize;
                    let index = read_imm!(u32, 3) as usize;
                    let v = pp.imports[imp_index].globals[index].as_ref().unwrap().value;
                    push!(v);
                    inst::size(inst::LOADIMPORTGLOBAL)
                }
                (inst::LOADINDEXPROPORNIL, inst::MODE_BOX) => {
                    let index = NanBox(pop!());
                    let receiver = NanBox(pop!());
                    let receiver_obj: &Object = match receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("value is not an object: {:?}", receiver),
                    };
                    let key: NanBoxKey = match index.try_into() {
                        Ok(k) => k,
                        _ => NanBox::from_nil().try_into().unwrap(),
                    };
                    let result = receiver_obj.own_property_or_nil(key);
                    push!(result.0);
                    inst::size(inst::LOADINDEXPROPORNIL)
                }
                (inst::LOADINDEXPROPORNIL, inst::MODE_LUA) => {
                    let index = NanBox(pop!());
                    let receiver = NanBox(pop!());
                    let key: NanBoxKey = match index.try_into() {
                        Ok(k) => k,
                        _ => NanBox::from_nil().try_into().unwrap(),
                    };
                    let result_opt = lua_meta_index!(receiver, key, 'mainloop);
                    let result = result_opt.unwrap_or(NanBox::from_nil());
                    push!(result.0);
                    inst::size(inst::LOADINDEXPROPORNIL)
                }
                (inst::LOADLOCAL, inst::MODE_I64) => {
                    let i = read_imm!(u16, 1) as usize;
                    let addr = fp - (i + 1) * 8;
                    let v = *(addr as *const u64);
                    push!(v);
                    inst::size(inst::LOADLOCAL)
                }
                (inst::LOADLOCALPARENT, inst::MODE_I64) => {
                    // Like LOADLOCAL, but loads from the caller's frame instead
                    // of the current frame. The caller must be an instance of
                    // the same function. Used by error handlers.
                    let i = read_imm!(u16, 1) as usize;
                    let caller_fp = *((fp + FRAME_FP_OFFSET) as *const usize);
                    let addr = caller_fp - (i + 1) * 8;
                    let v = *(addr as *const u64);
                    push!(v);
                    inst::size(inst::LOADLOCALPARENT)
                }
                (inst::LOADNAMEDPROP, inst::MODE_BOX) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let receiver = NanBox(pop!());
                    let receiver_obj: &Object = match receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("value is not an object: {:?}", receiver),
                    };
                    let prop = match receiver_obj.lookup_property(key) {
                        Some(p) => p,
                        None => unwind_errorf!("object does not have property {}", key),
                    };
                    let value = receiver_obj.property_value(prop);
                    push!(value.0);
                    inst::size(inst::LOADNAMEDPROP)
                }
                (inst::LOADNAMEDPROP, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let receiver = NanBox(pop!());
                    let result_opt = lua_meta_index!(receiver, key, 'mainloop);
                    let result = match result_opt {
                        Some(v) => v,
                        None => unwind_errorf!("object does not have property {}", key),
                    };
                    push!(result.0);
                    inst::size(inst::LOADNAMEDPROP)
                }
                (inst::LOADNAMEDPROPORNIL, inst::MODE_BOX) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let receiver = NanBox(pop!());
                    let receiver_obj: &Object = match receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("value is not an object: {:?}", receiver),
                    };
                    let value = receiver_obj
                        .lookup_property(key)
                        .map(|prop| receiver_obj.property_value(prop))
                        .unwrap_or(NanBox::from_nil());
                    push!(value.0);
                    inst::size(inst::LOADNAMEDPROPORNIL)
                }
                (inst::LOADNAMEDPROPORNIL, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let receiver = NanBox(pop!());
                    let result_opt = lua_meta_index!(receiver, key, 'mainloop);
                    let result = result_opt.unwrap_or(NanBox::from_nil());
                    push!(result.0);
                    inst::size(inst::LOADNAMEDPROPORNIL)
                }
                (inst::LOADNEXTINDEXPROPORNIL, inst::MODE_LUA) => {
                    let index = NanBox(pop!());
                    let boxed_receiver = NanBox(pop!());
                    let receiver: &Object = match boxed_receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("value is not an object: {:?}", boxed_receiver),
                    };
                    let entry_opt = if index.is_nil() {
                        receiver.first_own_property()
                    } else if let Ok(key) = NanBoxKey::try_from(index) {
                        receiver.next_own_property(key)
                    } else {
                        unwind_errorf!("index is not a valid key");
                    };
                    let (key, value) = if let Some((key, prop)) = entry_opt {
                        (NanBox::from(key), receiver.property_value(prop))
                    } else {
                        if !index.is_nil()
                            && receiver
                                .lookup_own_property(NanBoxKey::try_from(index).unwrap())
                                .is_none()
                        {
                            unwind_errorf!("index is not a key in receiver");
                        }
                        (NanBox::from_nil(), NanBox::from_nil())
                    };
                    push!(key.0);
                    push!(value.0);
                    inst::size(inst::LOADNEXTINDEXPROPORNIL)
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
                        unwind_errorf!("value is not an object: {:?}", v)
                    };
                    push!(NanBox::from(p).0);
                    inst::size(inst::LOADPROTOTYPE)
                }
                (inst::LOADVARARGS, inst::MODE_LUA) => {
                    // Copies the function's variadic arguments onto the stack
                    // and sets vc to the number of variadic arguments. Used to
                    // implement the "..." expression. The function must be
                    // variadic. The number of variadic arguments should be
                    // between the last argument and the frame.
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
                    binop_cmp!(i64, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_I32) => {
                    binop_cmp!(i32, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_I16) => {
                    binop_cmp!(i16, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_I8) => {
                    binop_cmp!(i8, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_U64) => {
                    binop_cmp!(u64, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_U32) => {
                    binop_cmp!(u32, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_U16) => {
                    binop_cmp!(u16, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_U8) => {
                    binop_cmp!(u8, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_F64) => {
                    binop_cmp!(f64, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_F32) => {
                    binop_cmp!(f32, <);
                    inst::size(inst::LT)
                }
                (inst::LT, inst::MODE_LUA) => {
                    binop_cmp!(lua, is_lt, "__lt");
                    inst::size(inst::LT)
                }
                (inst::MOD, inst::MODE_I64) => {
                    binop_num!(i64, wrapping_rem);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_I32) => {
                    binop_num!(i32, wrapping_rem);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_I16) => {
                    binop_num!(i16, wrapping_rem);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_I8) => {
                    binop_num!(i8, wrapping_rem);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_U64) => {
                    binop_num!(u64, wrapping_rem);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_U32) => {
                    binop_num!(u32, wrapping_rem);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_U16) => {
                    binop_num!(u16, wrapping_rem);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_U8) => {
                    binop_num!(u8, wrapping_rem);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_F64) => {
                    binop_num!(f64, %);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_F32) => {
                    binop_num!(f32, %);
                    inst::size(inst::MOD)
                }
                (inst::MOD, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    lua_try_meta_binop!(l, r, "__mod");
                    let v = if let (Ok(li), Ok(ri)) = (l.as_i64(), r.as_i64()) {
                        if ri == 0 {
                            unwind_errorf!("attempt to perform n%0");
                        }
                        let vi = li.wrapping_rem(ri);
                        maybe_box_int!(vi)
                    } else if let (Ok(lf), Ok(rf)) = (l.as_f64_imprecise(), r.as_f64_imprecise()) {
                        NanBox::from(lf.floor() % rf.floor())
                    } else {
                        unwind_errorf!(
                            "arithmetic operands must both be numbers: {:?} and {:?}",
                            l,
                            r
                        )
                    };
                    push!(v.0);
                    inst::size(inst::MOD)
                }
                (inst::MUL, inst::MODE_I64) => {
                    binop_num!(i64, wrapping_mul);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_I32) => {
                    binop_num!(i32, wrapping_mul);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_I16) => {
                    binop_num!(i16, wrapping_mul);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_I8) => {
                    binop_num!(i8, wrapping_mul);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_U64) => {
                    binop_num!(u64, wrapping_mul);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_U32) => {
                    binop_num!(u32, wrapping_mul);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_U16) => {
                    binop_num!(u16, wrapping_mul);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_U8) => {
                    binop_num!(u8, wrapping_mul);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_F64) => {
                    binop_num!(f64, *);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_F32) => {
                    binop_num!(f32, *);
                    inst::size(inst::MUL)
                }
                (inst::MUL, inst::MODE_LUA) => {
                    binop_num!(lua, *, checked_mul, "__mul");
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
                        unwind_errorf!("can't box non-zero value as nil");
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
                    binop_eq!(i64, !=);
                    inst::size(inst::NE)
                }
                (inst::NE, inst::MODE_F64) => {
                    binop_eq!(f64, !=);
                    inst::size(inst::NE)
                }
                (inst::NE, inst::MODE_F32) => {
                    binop_eq!(f32, !=);
                    inst::size(inst::NE)
                }
                (inst::NEG, inst::MODE_I64) => {
                    unop_num!(i64, -);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_I32) => {
                    unop_num!(i32, -);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_I16) => {
                    unop_num!(i16, -);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_I8) => {
                    unop_num!(i8, -);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_F64) => {
                    unop_num!(f64, -);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_F32) => {
                    unop_num!(f32, -);
                    inst::size(inst::NEG)
                }
                (inst::NEG, inst::MODE_LUA) => {
                    unop_num!(lua, -, "__unm");
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
                (inst::NEXTHANDLER, inst::MODE_I64) => {
                    // Used at the end of an error handler.
                    // If there is an error, continue unwinding by popping and
                    // executing the next handler, or returning the error if
                    // there is no handler.
                    // If there is no error, either because the handler was
                    // started with CALLHANDLER or because STOPERROR was called,
                    // pop vc and ip from the stack.
                    save_regs!();
                    if self.error.is_some() {
                        match self.unwind() {
                            Ok(()) => {
                                load_regs!();
                                continue;
                            }
                            Err(err) => return Err(err),
                        }
                    } else {
                        return_ok!(0);
                    }
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
                    unop_num!(i64, !);
                    inst::size(inst::NOTB)
                }
                (inst::NOTB, inst::MODE_I32) => {
                    unop_num!(i32, !);
                    inst::size(inst::NOTB)
                }
                (inst::NOTB, inst::MODE_I16) => {
                    unop_num!(i16, !);
                    inst::size(inst::NOTB)
                }
                (inst::NOTB, inst::MODE_I8) => {
                    unop_num!(i8, !);
                    inst::size(inst::NOTB)
                }
                (inst::NOTB, inst::MODE_LUA) => {
                    let v = NanBox(pop!());
                    lua_try_meta_unop!(v, "__bnot");
                    let vi = lua_value_as_int!(v);
                    let b = !vi;
                    push!(maybe_box_int!(b).0);
                    inst::size(inst::NOTB)
                }
                (inst::OR, inst::MODE_LUA) => {
                    lua_binop_bit!(|, "__bor");
                    inst::size(inst::OR)
                }
                (inst::PANIC, inst::MODE_STRING) => {
                    let level = read_imm!(u8, 1) as usize;
                    let s = (*(sp as *const *const data::String)).as_ref().unwrap();
                    let message = s.to_string();
                    save_regs!();
                    let error = self.error_level(level, message);
                    match self.unwind_with_error(error) {
                        Ok(()) => {
                            load_regs!();
                            continue;
                        }
                        Err(err) => return Err(err),
                    }
                }
                (inst::PANIC, inst::MODE_LUA) => {
                    let level = read_imm!(u8, 1) as usize;
                    let v = NanBox(*(sp as *const u64));
                    let s = v.to_string();
                    let message = s.to_string();
                    save_regs!();
                    let error = self.error_level(level, message);
                    match self.unwind_with_error(error) {
                        Ok(()) => {
                            load_regs!();
                            continue;
                        }
                        Err(err) => return Err(err),
                    }
                }
                (inst::PANICLEVEL, inst::MODE_LUA) => {
                    let raw_level = NanBox(*(sp as *const u64));
                    let raw_message = NanBox(*((sp + 8) as *const u64));
                    let level: usize = match <NanBox as TryInto<i64>>::try_into(raw_level) {
                        Ok(n) if n >= 0 => n as usize,
                        _ => 0,
                    };
                    let message = raw_message.to_string();
                    save_regs!();
                    let error = self.error_level(level, message);
                    match self.unwind_with_error(error) {
                        Ok(()) => {
                            load_regs!();
                            continue;
                        }
                        Err(err) => return Err(err),
                    }
                }
                (inst::POP, inst::MODE_I64) => {
                    sp += 8;
                    inst::size(inst::POP)
                }
                (inst::POPHANDLER, inst::MODE_I64) => {
                    // Set hp to the next error handler without executing the
                    // handler. This instruction doesn't actually remove the
                    // handler's data from the stack or change sp or ip.
                    hp = *((hp + HANDLER_HP_OFFSET) as *const usize);
                    inst::size(inst::POPHANDLER)
                }
                (inst::PUSHHANDLER, inst::MODE_I64) => {
                    // Adds an error handler by pushing the entry address
                    // in the current function and the current value of hp,
                    // then setting hp to the new sp. Effectively, handlers
                    // are a singly linked list threaded through stack frames.
                    let delta = read_imm!(i32, 1) as usize;
                    let eip = ((ip as isize) + (delta as isize) + 1) as u64;
                    push!(eip);
                    push!(hp as u64);
                    hp = sp;
                    inst::size(inst::PUSHHANDLER)
                }
                (inst::PROTOTYPE, inst::MODE_I64) => {
                    let c = cp.as_ref().unwrap();
                    let p = c.prototype.unwrap();
                    assert!(!p.is_null());
                    push!(p as u64);
                    inst::size(inst::PROTOTYPE)
                }
                (inst::RET, inst::MODE_I64) => {
                    return_ok!(1);
                }
                (inst::RETV, inst::MODE_LUA) => {
                    return_ok!(vc);
                }
                (inst::SHL, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    lua_try_meta_binop!(l, r, "__shl");
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
                    lua_try_meta_binop!(l, r, "__shr");
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
                (inst::SETV, inst::MODE_I64) => {
                    vc = pop!() as usize;
                    inst::size(inst::SETV)
                }
                (inst::SETVI, inst::MODE_I64) => {
                    vc = read_imm!(u16, 1) as usize;
                    inst::size(inst::SETVI)
                }
                (inst::STOPERROR, inst::MODE_I64) => {
                    // Recovers from the current error by clearing the error
                    // state and popping the error handler's stack frame.
                    // May only be used within an error handler that was not
                    // invoked with CALLHANDLER. Execution resumes at the next
                    // instruction; the frame's return address is ignored.
                    self.error = None;
                    sp = fp + FRAME_SIZE;
                    fp = *((fp + FRAME_FP_OFFSET) as *const usize);
                    inst::size(inst::STOPERROR)
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
                (inst::STOREIMPORTGLOBAL, inst::MODE_I64) => {
                    let imp_index = read_imm!(u16, 1) as usize;
                    let index = read_imm!(u32, 3) as usize;
                    let v = pop!();
                    pp.imports[imp_index].globals[index].as_mut().unwrap().value = v;
                    inst::size(inst::STOREIMPORTGLOBAL)
                }
                (inst::STOREINDEXPROP, inst::MODE_BOX) => {
                    let value = NanBox(pop!());
                    let index = NanBox(pop!());
                    let receiver = NanBox(pop!());
                    let receiver_obj: &mut Object = match receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("value is not an object: {:?}", receiver),
                    };
                    let key: NanBoxKey = match index.try_into() {
                        Ok(k) => k,
                        _ => unwind_errorf!("cannot use NaN or nil as property key"),
                    };
                    receiver_obj.set_own_property(key, PropertyKind::Field, value);
                    inst::size(inst::STOREINDEXPROP)
                }
                (inst::STOREINDEXPROP, inst::MODE_LUA) => {
                    let value = NanBox(pop!());
                    let index = NanBox(pop!());
                    let receiver = NanBox(pop!());
                    let key: NanBoxKey = match index.try_into() {
                        Ok(k) => k,
                        _ => unwind_errorf!("cannot use NaN or nil as property key"),
                    };
                    lua_meta_newindex!(receiver, key, value, 'mainloop);
                    inst::size(inst::STOREINDEXPROP)
                }
                (inst::STORELOCAL, inst::MODE_I64) => {
                    let i = read_imm!(u16, 1) as usize;
                    let v = pop!();
                    let addr = fp - (i + 1) * 8;
                    *(addr as *mut u64) = v;
                    inst::size(inst::STORELOCAL)
                }
                (inst::STORELOCALPARENT, inst::MODE_I64) => {
                    // Like STORELOCAL, but writes to the caller's frame instead
                    // of the current frame. The caller must be an instance of
                    // the same function. Used by error handlers.
                    let i = read_imm!(u16, 1) as usize;
                    let caller_fp = *((fp + FRAME_FP_OFFSET) as *const usize);
                    let addr = caller_fp - (i + 1) * 8;
                    let v = pop!();
                    *(addr as *mut u64) = v;
                    inst::size(inst::STORELOCALPARENT)
                }
                (inst::STOREMETHOD, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let raw_method = NanBox(pop!());
                    if raw_method.type_tag() != nanbox::TAG_CLOSURE {
                        unwind_errorf!("method value is not a function: {:?}", raw_method);
                    }
                    let raw_receiver = NanBox(pop!());
                    let receiver: &mut Object = match raw_receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("value is not an object: {:?}", raw_receiver),
                    };
                    receiver.set_own_property(key, PropertyKind::Method, raw_method);
                    inst::size(inst::STOREMETHOD)
                }
                (inst::STORENAMEDPROP, inst::MODE_BOX) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key = NanBox::from(name).try_into().unwrap();
                    let value = NanBox(pop!());
                    let raw_receiver = NanBox(pop!());
                    let receiver: &mut Object = match raw_receiver.try_into() {
                        Ok(o) => o,
                        _ => unwind_errorf!("value is not an object: {:?}", raw_receiver),
                    };
                    receiver.set_property(key, PropertyKind::Field, value);
                    inst::size(inst::STORENAMEDPROP)
                }
                (inst::STORENAMEDPROP, inst::MODE_LUA) => {
                    let name_index = read_imm!(u32, 1) as usize;
                    let name = &pp.strings[name_index];
                    let key: NanBoxKey = NanBox::from(name).try_into().unwrap();
                    let value = NanBox(pop!());
                    let receiver = NanBox(pop!());
                    lua_meta_newindex!(receiver, key, value, 'mainloop);
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
                (inst::STOREPROTOTYPE, inst::MODE_LUA) => {
                    let boxed_prototype = NanBox(pop!());
                    let boxed_receiver = NanBox(pop!());
                    let receiver = match <NanBox as TryInto<&mut Object>>::try_into(boxed_receiver)
                    {
                        Ok(r) => r,
                        _ => unwind_errorf!("value is not an object: {:?}", boxed_receiver),
                    };
                    if boxed_prototype.is_nil() {
                        receiver.prototype.set_ptr(0 as *mut Object);
                    } else if let Ok(p) =
                        <NanBox as TryInto<*mut Object>>::try_into(boxed_prototype)
                    {
                        receiver.prototype.set_ptr(p);
                    } else {
                        unwind_errorf!("prototype is not an object or nil: {:?}", boxed_prototype);
                    }
                    inst::size(inst::STOREPROTOTYPE)
                }
                (inst::STRCAT, inst::MODE_LUA) => {
                    let r = NanBox(pop!());
                    let l = NanBox(pop!());
                    lua_try_meta_binop!(l, r, "__concat");
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
                    binop_num!(i64, wrapping_sub);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_I32) => {
                    binop_num!(i32, wrapping_sub);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_I16) => {
                    binop_num!(i16, wrapping_sub);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_I8) => {
                    binop_num!(i8, wrapping_sub);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_U64) => {
                    binop_num!(u64, wrapping_sub);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_U32) => {
                    binop_num!(u32, wrapping_sub);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_U16) => {
                    binop_num!(u16, wrapping_sub);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_U8) => {
                    binop_num!(u8, wrapping_sub);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_F64) => {
                    binop_num!(f64, -);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_F32) => {
                    binop_num!(f32, -);
                    inst::size(inst::SUB)
                }
                (inst::SUB, inst::MODE_LUA) => {
                    binop_num!(lua, -, checked_sub, "__sub");
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
                    let mut args = vec![NanBox(0); vc];
                    for i in 0..vc {
                        let argp = sp + (vc - i - 1) * 8;
                        args[i] = NanBox(*(argp as *const u64));
                    }
                    sp += vc * 8;
                    ip = (ip as usize + inst::size(inst::SYS)) as *const u8;
                    save_regs!();
                    let rets = match sys {
                        inst::SYS_DOFILE => self.sys_lua_dofile(&args)?,
                        inst::SYS_LOAD => self.sys_lua_load(&args)?,
                        inst::SYS_LOADFILE => self.sys_lua_loadfile(&args)?,
                        inst::SYS_PRINT => self.sys_lua_print(&args)?,
                        inst::SYS_TONUMBER => self.sys_lua_tonumber(&args)?,
                        inst::SYS_TOSTRING => self.sys_lua_tostring(&args)?,
                        _ => panic!("unknown sys {}", sys),
                    };
                    load_regs!();
                    vc = rets.len();
                    for ret in rets {
                        sp -= 8;
                        *(sp as *mut u64) = ret.0;
                    }
                    continue;
                }
                (inst::TOFLOAT, inst::MODE_LUA) => {
                    let i = NanBox(pop!());
                    match i.as_f64_imprecise() {
                        Ok(o) => push!(o.to_bits()),
                        _ => unwind_errorf!("could not convert value of type {:?} to float", i),
                    }
                    inst::size(inst::TOFLOAT)
                }
                (inst::TYPEOF, inst::MODE_LUA) => {
                    let i = NanBox(pop!());
                    let o = i.type_tag();
                    push!(o);
                    inst::size(inst::TYPEOF)
                }
                (inst::UNBOX, inst::MODE_I64) => {
                    // Pops a nanboxed number and pushes the corresponding
                    // integer. Raises an error if the value is not a number or
                    // is a float without a precise integer representation.
                    let i = NanBox(pop!());
                    let o = match i.as_i64() {
                        Ok(n) => n,
                        _ => unwind_errorf!("could not convert value to integer"),
                    };
                    push!(o as u64);
                    inst::size(inst::UNBOX)
                }
                (inst::XOR, inst::MODE_LUA) => {
                    lua_binop_bit!(^, "__bxor");
                    inst::size(inst::XOR)
                }
                (_, inst::MODE_I64) => {
                    save_regs!();
                    panic!(
                        "{}",
                        self.error(format!("unknown opcode {} code {}", inst::mnemonic(op), op))
                    );
                }
                _ => {
                    save_regs!();
                    let err = self.error(format!(
                        "unknown opcode {}{} code {} {}",
                        inst::mnemonic(op),
                        inst::mode_mnemonic(mode),
                        mode,
                        op
                    ));
                    panic!("{}", err);
                }
            };
            ip = (ip as usize + inst_size) as *const u8;
        }

        // We break out of the loop above after popping a stack frame with a
        // null func and return address. ret_sp points to the last result.
        // We need to move results into a Vec for native code, the save
        // registers and return.
        let retc = if func.var_return_type.is_some() {
            assert!(vc >= func.return_types.len());
            vc
        } else {
            func.return_types.len()
        };
        let mut rets = Vec::with_capacity(retc);
        for i in 0..retc {
            let retp = ret_sp + (retc - i - 1) * 8;
            let ret = *(retp as *const u64);
            rets.push(ret);
        }
        self.func = 0 as *const Function;
        self.vc = vc;
        self.cp = 0 as *const Closure;
        self.sp = sp;
        self.fp = fp;
        self.ip = 0 as *const u8;
        Ok(rets)
    }

    unsafe fn sys_lua_dofile(&mut self, args: &[NanBox]) -> Result<Vec<NanBox>, Error> {
        let (path, data) = if args.len() == 0 || args[0].is_nil() {
            let mut buf = Vec::new();
            let mut env = self.env.borrow_mut();
            env.r
                .read_to_end(&mut buf)
                .map_err(|err| self.wrap_error(&err))?;
            (PathBuf::from("<stdin>"), buf)
        } else {
            let path_dstr: &data::String = args[0]
                .try_into()
                .map_err(|_| self.error(String::from("argument must be a string")))?;
            let path_str = path_dstr
                .as_str()
                .map_err(|_| self.error(String::from("argument must be a valid path")))?;
            let path = PathBuf::from(path_str);
            let data =
                fs::read(&path).map_err(|err| self.error(format!("{}: {}", path_str, err)))?;
            (path, data)
        };
        let package = self
            .lua_runtime
            .compile(&path, &data)
            .map_err(|mut errs| errs.0.remove(0))?;
        let interp_fac = InterpreterFactory::new(self.env, self.loader.clone(), self.lua_runtime);
        let (_, result) = self.loader.load_given_package(&interp_fac, package)?;
        Ok(result.into_iter().map(|v| NanBox(v)).collect())
    }

    unsafe fn sys_lua_load(&mut self, args: &[NanBox]) -> Result<Vec<NanBox>, Error> {
        let chunk_source: Vec<u8> =
            if let Ok(s) = <NanBox as TryInto<&data::String>>::try_into(args[0]) {
                Vec::from(s.as_bytes())
            } else if let Ok(f) = <NanBox as TryInto<&Closure>>::try_into(args[0]) {
                let mut buf = Vec::new();
                loop {
                    let rets = self.interpret_closure_rec(f, &[])?;
                    if rets.is_empty() || NanBox(rets[0]).is_nil() {
                        break;
                    }
                    let piece: &data::String = NanBox(rets[0]).try_into().map_err(|_| {
                        self.error(String::from(
                            "chunk function must return string, nil, or nothing",
                        ))
                    })?;
                    if piece.is_empty() {
                        break;
                    }
                    buf.extend_from_slice(piece.as_bytes());
                }
                buf
            } else {
                return Err(self.error(String::from(
                    "chunk argument must be a string or a function",
                )));
            };

        let chunk_name = if let Ok(s) = <NanBox as TryInto<&data::String>>::try_into(args[1]) {
            PathBuf::from(s.as_str().map_err(|_| {
                self.error(String::from(
                    "chunkname argument must be a valid UTF-8 string or nil",
                ))
            })?)
        } else if args[1].is_nil() {
            if args[0].type_tag() == nanbox::TAG_STRING {
                PathBuf::from("chunk")
            } else {
                PathBuf::from("=(load)")
            }
        } else {
            return Err(self.error(String::from(
                "chunkname argument must be a valid UTF-8 string or nil",
            )));
        };

        let mode = if let Ok(s) = <NanBox as TryInto<&data::String>>::try_into(args[2]) {
            s.as_str().map_err(|_| {
                self.error(String::from(
                    "mode argument must be \"b\", \"t\", \"bt\", or nil",
                ))
            })?
        } else if args[2].is_nil() {
            "bt"
        } else {
            return Err(self.error(String::from(
                "mode argument must be \"b\", \"t\", \"bt\", or nil",
            )));
        };
        match mode {
            "t" | "bt" => (),
            // TODO: maybe support binary chunks?
            "b" => return Err(self.error(String::from("binary chunks not supported"))),
            _ => {
                return Err(self.error(String::from(
                    "mode argument must be \"b\", \"t\", \"bt\", or nil",
                )))
            }
        };

        if !args[3].is_nil() {
            // TODO: support it. This requires more Lua-specific hacks on the
            // package loader though.
            return Err(self.error(String::from("env argument not supported")));
        }

        let mut package = self
            .lua_runtime
            .compile(&chunk_name, &chunk_source)
            .map_err(|mut errs| errs.0.remove(0))?;
        let init_index = package.init_index.unwrap() as usize;
        package.init_index = None;
        let interp_fac = InterpreterFactory::new(self.env, self.loader.clone(), self.lua_runtime);
        let (index, _) = self.loader.load_given_package(&interp_fac, package)?;
        let init_closure = Closure::alloc(0, 0).as_mut().unwrap();
        let loaded_package = self.loader.unnamed_package_by_index(index).unwrap();
        let init_func = &mut loaded_package.functions[init_index] as *mut Function;
        init_closure.function.set_ptr(init_func);
        Ok(vec![NanBox::from(init_closure)])
    }

    unsafe fn sys_lua_loadfile(&mut self, args: &[NanBox]) -> Result<Vec<NanBox>, Error> {
        let (chunk_name, chunk_source) =
            if let Ok(s) = <NanBox as TryInto<&data::String>>::try_into(args[0]) {
                let path_str = s.as_str().map_err(|_| {
                    self.error(String::from("filename argument must be a valid path"))
                })?;
                let path = PathBuf::from(path_str);
                let data =
                    fs::read(&path).map_err(|err| self.error(format!("{}: {}", path_str, err)))?;
                (path, data)
            } else if args[0].is_nil() {
                let mut buf = Vec::new();
                let mut env = self.env.borrow_mut();
                env.r
                    .read_to_end(&mut buf)
                    .map_err(|err| self.wrap_error(&err))?;
                (PathBuf::from("<stdin>"), buf)
            } else {
                return Err(self.error(String::from("filename argument must be string or nil")));
            };

        let mode = if let Ok(s) = <NanBox as TryInto<&data::String>>::try_into(args[1]) {
            s.as_str().map_err(|_| {
                self.error(String::from(
                    "mode argument must be \"b\", \"t\", \"bt\", or nil",
                ))
            })?
        } else if args[1].is_nil() {
            "bt"
        } else {
            return Err(self.error(String::from(
                "mode argument must be \"b\", \"t\", \"bt\", or nil",
            )));
        };
        match mode {
            "t" | "bt" => (),
            // TODO: maybe support binary chunks?
            "b" => return Err(self.error(String::from("binary chunks not supported"))),
            _ => {
                return Err(self.error(String::from(
                    "mode argument must be \"b\", \"t\", \"bt\", or nil",
                )))
            }
        };

        if !args[2].is_nil() {
            // TODO: support it. This requires more Lua-specific hacks on the
            // package loader though.
            return Err(self.error(String::from("env argument not supported")));
        }

        let mut package = self
            .lua_runtime
            .compile(&chunk_name, &chunk_source)
            .map_err(|mut errs| errs.0.remove(0))?;
        let init_index = package.init_index.unwrap() as usize;
        package.init_index = None;
        let interp_fac = InterpreterFactory::new(self.env, self.loader.clone(), self.lua_runtime);
        let (index, _) = self.loader.load_given_package(&interp_fac, package)?;
        let init_closure = Closure::alloc(0, 0).as_mut().unwrap();
        let loaded_package = self.loader.unnamed_package_by_index(index).unwrap();
        let init_func = &mut loaded_package.functions[init_index] as *mut Function;
        init_closure.function.set_ptr(init_func);
        Ok(vec![NanBox::from(init_closure)])
    }

    unsafe fn sys_lua_print(&mut self, args: &[NanBox]) -> Result<Vec<NanBox>, Error> {
        let strs = args
            .iter()
            .map(|&v| self.lua_tostring(v))
            .collect::<Result<Vec<NanBox>, Error>>()?;
        let mut env = self.env.borrow_mut();
        let mut sep = "";
        for s in strs {
            let _ = write!(env.w, "{}{}", sep, s);
            sep = " ";
        }
        let _ = write!(env.w, "\n");
        Ok(Vec::new())
    }

    unsafe fn sys_lua_tonumber(&mut self, args: &[NanBox]) -> Result<Vec<NanBox>, Error> {
        if args.is_empty() {
            return Err(
                self.error_level(1, String::from("tonumber: requires at least one argument"))
            );
        }
        match args.get(1).filter(|v| !v.is_nil()) {
            Some(&raw_base) => {
                let s: &data::String = match args[0].try_into() {
                    Ok(s) => s,
                    _ => {
                        return Err(self.error_level(
                            1,
                            format!(
                                "tonumber: for first argument, expected string, got {:?}",
                                args[0]
                            ),
                        ))
                    }
                };
                let base: u32 = match <NanBox as TryInto<i64>>::try_into(raw_base) {
                    Ok(n) if 2 <= n && n <= 36 => n as u32,
                    _ => {
                        return Err(self
                            .error_level(1, String::from("tonumber: base argument out of range")))
                    }
                };
                let s_str = match s.as_str() {
                    Ok(s) => s.trim(),
                    _ => return Ok(vec![NanBox::from_nil()]),
                };
                match i64::from_str_radix(s_str, base) {
                    Ok(n) => return Ok(vec![NanBox::from_small_or_big_i64(n)]),
                    _ => return Ok(vec![NanBox::from_nil()]),
                }
            }
            None => {
                if args[0].is_number() {
                    return Ok(vec![args[0]]);
                }
                let s: &data::String = match args[0].try_into() {
                    Ok(s) => s,
                    _ => return Ok(vec![NanBox::from_nil()]),
                };
                let s_str = match s.as_str() {
                    Ok(s) => s.trim(),
                    _ => return Ok(vec![NanBox::from_nil()]),
                };
                match self.lua_runtime.convert_number(s_str) {
                    LuaConvertedNumber::Malformed => return Ok(vec![NanBox::from_nil()]),
                    LuaConvertedNumber::Int(n) => {
                        return Ok(vec![NanBox::from_small_or_big_i64(n)])
                    }
                    LuaConvertedNumber::Float(n) => return Ok(vec![NanBox::from(n)]),
                }
            }
        }
    }

    unsafe fn sys_lua_tostring(&mut self, args: &[NanBox]) -> Result<Vec<NanBox>, Error> {
        self.lua_tostring(args[0]).map(|v| vec![v])
    }

    unsafe fn lua_tostring(&mut self, v: NanBox) -> Result<NanBox, Error> {
        if v.type_tag() == nanbox::TAG_STRING {
            return Ok(v);
        }
        if let Ok(o) = <NanBox as TryInto<&Object>>::try_into(v) {
            let tostring_name = data::String::from_bytes(b"__tostring");
            let tostring_box: NanBox = tostring_name.into();
            let tostring_key: NanBoxKey = tostring_box.try_into().unwrap();
            let tostring_raw = o
                .prototype
                .as_ref()
                .and_then(|p| p.own_property(tostring_key))
                .unwrap_or(NanBox::from_nil());
            if !tostring_raw.is_nil() {
                if let Ok(c) = <NanBox as TryInto<&Closure>>::try_into(tostring_raw) {
                    let ret = self.lua_interpret_closure(c, &[v])?;
                    if ret.type_tag() != nanbox::TAG_STRING {
                        return Err(self.error_level(
                            0,
                            format!("__tostring returned {:?}, not a string", ret),
                        ));
                    }
                    return Ok(ret);
                } else {
                    return Err(self.error_level(0, String::from("__tostring is not a method")));
                }
            }
            // TODO: use the __name field and return something like "<name>".

            // fall through
        }
        Ok(data::String::from_bytes(v.to_string().as_bytes()).into())
    }

    unsafe fn interpret_closure_rec(
        &mut self,
        closure: &Closure,
        args: &[u64],
    ) -> Result<Vec<u64>, Error> {
        // Construct a frame for the caller and clear the saved registers. This
        // will cause the recursive interpreter call to return here instead of
        // into the previous stack frame.
        let fp = self.sp - FRAME_SIZE;
        *((fp + FRAME_FUNC_OFFSET) as *mut *const Function) = self.func;
        self.func = 0 as *const Function;
        *((fp + FRAME_CP_OFFSET) as *mut *const Closure) = self.cp;
        self.cp = 0 as *const Closure;
        *((fp + FRAME_IP_OFFSET) as *mut *const u8) = self.ip;
        self.ip = 0 as *const u8;
        *((fp + FRAME_FP_OFFSET) as *mut usize) = self.fp;
        self.fp = fp;
        self.sp = fp;

        // Call the closure. This pushes arguments, constructs a stack frame
        // for the callee, and begins the interpreter loop. Because we set
        // self.ip to 0 above, interpret_closure will stop and return when
        // the callee returns.
        let rets = self.interpret_closure(closure, args)?;

        // Pop the caller's frame.
        debug_assert_eq!(self.fp, fp);
        debug_assert_eq!(self.sp, fp);
        self.func = *((fp + FRAME_FUNC_OFFSET) as *const *const Function);
        self.cp = *((fp + FRAME_CP_OFFSET) as *const *const Closure);
        self.ip = *((fp + FRAME_IP_OFFSET) as *const *const u8);
        self.fp = *((fp + FRAME_FP_OFFSET) as *const usize);
        self.sp = fp + FRAME_SIZE;

        Ok(rets)
    }

    unsafe fn lua_interpret_closure(
        &mut self,
        closure: &Closure,
        args: &[NanBox],
    ) -> Result<NanBox, Error> {
        let rets = self.lua_interpret_closure_any(closure, args)?;
        Ok(rets.first().map(|&v| v).unwrap_or(NanBox::from_nil()))
    }

    unsafe fn lua_interpret_closure_any(
        &mut self,
        closure: &Closure,
        args: &[NanBox],
    ) -> Result<Vec<NanBox>, Error> {
        let argc = if closure.function.var_param_type.is_some() {
            args.len().max(closure.function.param_types.len())
        } else {
            closure.function.param_types.len()
        };
        let mut raw_args = Vec::with_capacity(argc);
        raw_args.extend(args.iter().take(args.len().min(argc)).map(|n| n.0));
        raw_args.resize(argc, NanBox::from_nil().0);
        let raw_rets = self.interpret_closure_rec(closure, &raw_args)?;
        let rets = raw_rets.iter().map(|&n| NanBox(n)).collect();
        Ok(rets)
    }

    unsafe fn lua_load_meta_value(v: NanBox, name: &str) -> Option<NanBox> {
        <NanBox as TryInto<&Object>>::try_into(v)
            .ok()
            .and_then(|o| o.prototype.as_ref())
            .and_then(|p| p.own_named_property(name.as_bytes()))
            .filter(|m| !m.is_nil())
    }

    unsafe fn lua_load_std_function(&mut self, name: &str) -> Option<*const Function> {
        self.loader
            .package_by_name("luastd")
            .and_then(|p| p.function_by_name(name))
            .map(|f| f as *const Function)
    }

    unsafe fn unwind_with_error(&mut self, error: Error) -> Result<(), Error> {
        // TODO: wrap any previous error. Currently, we ignore it, which makes
        // double panics confusing to debug.
        self.error = Some(error);
        self.unwind()
    }

    /// Pop frames from the stack until reaching the function containing the
    /// next error handler, then prepares the interpreter to execute that
    /// handler.
    ///
    /// If there is no handler, clear all state and return the current error.
    ///
    /// Otherwise, after popping frames, push a new frame for the same function
    /// containing the error handler, but instead of starting at instruction 0,
    /// set ip to the handler address.
    unsafe fn unwind(&mut self) -> Result<(), Error> {
        if self.hp == 0 {
            // No error handler. Clear all state, and return the error result.
            self.func = 0 as *const Function;
            self.vc = 0;
            self.cp = 0 as *const Closure;
            self.sp = self.stack.end();
            self.fp = self.stack.end();
            self.ip = 0 as *const u8;
            let mut error: Option<Error> = None;
            mem::swap(&mut self.error, &mut error);
            Err(error.unwrap())
        } else {
            // Pop stack frames until we reach the frame that pushed the
            // handler. Also, pop the handler, and any words pushed after it.
            while self.fp < self.hp {
                self.func = *((self.fp + FRAME_FUNC_OFFSET) as *const *const Function);
                self.cp = *((self.fp + FRAME_CP_OFFSET) as *const *const Closure);
                self.ip = *((self.fp + FRAME_IP_OFFSET) as *const *const u8);
                self.fp = *(self.fp as *const usize);
            }
            self.sp = self.hp + HANDLER_SIZE;
            let hip = *((self.hp + HANDLER_IP_OFFSET) as *const *const u8);
            self.hp = *((self.hp + HANDLER_HP_OFFSET) as *const usize);

            // Push a stack frame for the handler.
            self.sp -= FRAME_SIZE;
            *((self.sp + FRAME_FUNC_OFFSET) as *mut *const Function) = self.func;
            *((self.sp + FRAME_CP_OFFSET) as *mut *const Closure) = self.cp;
            *((self.sp + FRAME_IP_OFFSET) as *mut *const u8) = self.ip;
            self.ip = hip;
            *((self.sp + FRAME_FP_OFFSET) as *mut usize) = self.fp;
            self.fp = self.sp;

            Ok(())
        }
    }

    unsafe fn error(&self, message: String) -> Error {
        self.error_level(0, message)
    }

    unsafe fn error_level(&self, mut level: usize, mut message: String) -> Error {
        let mut func = self.func.as_ref().unwrap();
        let mut fp = self.fp;
        let mut ip = self.ip;
        while level > 0 {
            func = match (*((fp + FRAME_FUNC_OFFSET) as *const *const Function)).as_ref() {
                Some(f) => f,
                None => break,
            };
            ip = *((fp + FRAME_IP_OFFSET) as *const *const u8);
            fp = *((fp + FRAME_FP_OFFSET) as *const usize);
            level -= 1;
        }
        let inst_offset = (ip as usize - &func.insts[0] as *const u8 as usize)
            .try_into()
            .unwrap();
        let position = self.position_at(func, inst_offset);
        if !func.name.is_empty() {
            message = format!("{}: {}", func.name, message);
        }
        Error { position, message }
    }

    unsafe fn wrap_error(&self, err: &dyn Display) -> Error {
        Error {
            position: self.position(),
            message: err.to_string(),
        }
    }

    unsafe fn position(&self) -> Position {
        let func = self.func.as_ref().unwrap();
        let inst_offset = (self.ip as usize - &func.insts[0] as *const u8 as usize)
            .try_into()
            .unwrap();
        self.position_at(func, inst_offset)
    }

    unsafe fn position_at(&self, func: &Function, inst_offset: u32) -> Position {
        func.package
            .as_ref()
            .unwrap()
            .line_map
            .position(inst_offset, &func.line_map)
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

    fn end(&self) -> usize {
        &self.data[0] as *const u8 as usize + self.data.len()
    }
}

pub struct InterpreterFactory<'a> {
    env: &'a RefCell<Env<'a>>,
    loader: Arc<PackageLoader>,
    lua_runtime: &'a dyn LuaRuntime,
}

impl<'a> InterpreterFactory<'a> {
    pub fn new(
        env: &'a RefCell<Env<'a>>,
        loader: Arc<PackageLoader>,
        lua_runtime: &'a dyn LuaRuntime,
    ) -> InterpreterFactory<'a> {
        InterpreterFactory {
            env,
            loader,
            lua_runtime,
        }
    }

    pub fn get(&self) -> Interpreter<'a> {
        Interpreter::new(self.env, self.loader.clone(), self.lua_runtime)
    }
}
