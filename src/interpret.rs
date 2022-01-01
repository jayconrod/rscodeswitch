use crate::inst;
use crate::nanbox;
use crate::package::{Package, Type};

use std::error;
use std::fmt;
use std::io::Write;

pub struct Interpreter<'a> {
    w: &'a mut dyn Write,
    pub package: Box<Package>,
    global_slots: Vec<u64>,
}

impl<'a> Interpreter<'a> {
    pub fn new(w: &'a mut dyn Write, package: Box<Package>) -> Interpreter<'a> {
        let mut global_slots = Vec::new();
        global_slots.resize(package.globals.len() + package.functions.len(), 0);
        Interpreter {
            w,
            package,
            global_slots,
        }
    }

    pub fn interpret(&mut self, func_name: &str) -> Result<(), Error> {
        unsafe {
            let func = self
                .package
                .function_by_name(func_name)
                .ok_or_else(|| Error {
                    message: format!("no such function: '{}'", func_name),
                })?;

            let mut stack = Stack::new();
            let mut sp = stack.end();
            let fp = sp;
            let mut ip = &func.insts[0] as *const u8;
            let mut types = Vec::new();

            macro_rules! return_errorf {
                ($($x:expr),*) => {
                    return Err(Error{message: format!($($x,)*)})
                };
            }

            macro_rules! pop {
                () => {{
                    let v = *(sp as *mut u64);
                    sp += 8;
                    v
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

            macro_rules! push {
                ($x:expr, $t:expr) => {{
                    sp -= 8;
                    *(sp as *mut u64) = $x;
                    types.push($t);
                }};
            }

            macro_rules! binop_eq {
                ($op:tt) => {{
                    let rty = types.pop().unwrap();
                    let lty = types.pop().unwrap();
                    assert_eq!(lty, rty);
                    match lty {
                        Type::Bool => {
                            let r = pop!();
                            let l = pop!();
                            push!((l $op r) as u64, Type::Bool);
                        }
                        Type::Float64 => {
                            // Float comparison can't use raw bit comparison
                            // because NaN != NaN.
                            let r = f64::from_bits(pop!());
                            let l = f64::from_bits(pop!());
                            push!((l $op r) as u64, Type::Bool);
                        }
                        Type::Nanbox => {
                            let r = pop!();
                            let l = pop!();
                            let v = if let Some(lb) = nanbox::to_bool(l) {
                                if let Some(rb) = nanbox::to_bool(r) {
                                    lb $op rb
                                } else {
                                    true $op false
                                }
                            } else if let Some(ln) = nanbox::to_f64(l) {
                                if let Some(rn) = nanbox::to_f64(r) {
                                    (ln $op rn)
                                } else {
                                    true $op false
                                }
                            } else {
                                unreachable!()
                            };
                            push!(v as u64, Type::Bool);
                        }
                    }
                }};
            }

            macro_rules! binop_cmp {
                ($op:tt) => {{
                    let rty = types.pop().unwrap();
                    let lty = types.pop().unwrap();
                    assert_eq!(lty, rty);
                    match lty {
                        Type::Float64 => {
                            let r = pop!() as f64;
                            let l = pop!() as f64;
                            push!((l $op r) as u64, Type::Bool);
                        }
                        Type::Nanbox => {
                            let r = pop!();
                            let rn = nanbox::to_f64(r).ok_or_else(|| Error{message: format!("invalid value in comparison operation: {}", nanbox::debug_str(r))})?;
                            let l = pop!();
                            let ln = nanbox::to_f64(l).ok_or_else(|| Error{message: format!("invalid value in comparison operation: {}", nanbox::debug_str(l))})?;
                            push!((ln $op rn) as u64, Type::Bool);
                        }
                        _ => unreachable!(),
                    }
                }}
            }

            macro_rules! binop_num {
                ($op:tt) => {{
                    let rty = types.pop().unwrap();
                    let lty = types.pop().unwrap();
                    assert_eq!(lty, rty);
                    match lty {
                        Type::Float64 => {
                            let r = pop!();
                            let l = pop!();
                            push!(l $op r, Type::Float64);
                        }
                        Type::Nanbox => {
                            let r = pop!();
                            let rn = nanbox::to_f64(r).ok_or_else(|| Error{message: format!("invalid value in numeric operation: {}", nanbox::debug_str(r))})?;
                            let l = pop!();
                            let ln = nanbox::to_f64(l).ok_or_else(|| Error{message: format!("invalid value in numeric operation: {}", nanbox::debug_str(l))})?;
                            let x = ln $op rn;
                            push!(nanbox::from_f64(x), Type::Nanbox)
                        }
                        _ => unreachable!(),
                    }
                }};
            }

            loop {
                match *ip {
                    inst::ADD => {
                        binop_num!(+);
                    }
                    inst::DIV => {
                        binop_num!(/);
                    }
                    inst::DUP => {
                        let v = *(sp as *mut u64);
                        sp -= 8;
                        *(sp as *mut u64) = v;
                        types.push(types[types.len() - 1]);
                    }
                    inst::EQ => {
                        binop_eq!(==)
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
                        sp -= 8;
                        *(sp as *mut u64) = 0;
                        types.push(Type::Bool);
                    }
                    inst::FLOAT64 => {
                        let n = f64::from_le_bytes(*((ip as usize + 1) as *const [u8; 8]));
                        sp -= 8;
                        *(sp as *mut f64) = n;
                        types.push(Type::Float64);
                    }
                    inst::LOADGLOBAL => {
                        let i = *((ip as usize + 1) as *const u32) as usize;
                        let v = self.global_slots[i];
                        sp -= 8;
                        *(sp as *mut u64) = v;
                        types.push(Type::Nanbox)
                    }
                    inst::LT => {
                        binop_cmp!(<)
                    }
                    inst::LOADLOCAL => {
                        let i = *((ip as usize + 1) as *const u16) as usize;
                        let v = *((fp as usize - (i + 1) * 8) as *const u64);
                        sp -= 8;
                        *(sp as *mut u64) = v;
                        types.push(types[i]);
                    }
                    inst::MUL => {
                        binop_num!(*)
                    }
                    inst::NANBOX => {
                        match types.pop().unwrap() {
                            Type::Bool => {
                                let b = *(sp as *mut bool);
                                let v = nanbox::from_bool(b);
                                *(sp as *mut u64) = v;
                            }
                            Type::Float64 | Type::Nanbox => (),
                        };
                        types.push(Type::Nanbox);
                    }
                    inst::NE => {
                        binop_eq!(!=)
                    }
                    inst::NEG => {
                        let ty = types.pop().unwrap();
                        let v = pop!();
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
                                        nanbox::debug_str(v)
                                    )
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    inst::NOP => (),
                    inst::NOT => {
                        let ty = types.pop().unwrap();
                        let v = pop!();
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
                    inst::RET => return Ok(()),
                    inst::STOREGLOBAL => {
                        let i = *((ip as usize + 1) as *const u32) as usize;
                        let v = *(sp as *mut u64);
                        sp += 8;
                        types.pop();
                        self.global_slots[i] = v;
                    }
                    inst::STORELOCAL => {
                        let i = *((ip as usize + 1) as *const u16) as usize;
                        let v = *(sp as *mut u64);
                        sp += 8;
                        types.pop();
                        *((fp as usize - (i + 1) * 8) as *mut u64) = v;
                    }
                    inst::SUB => {
                        binop_num!(-)
                    }
                    inst::SYS => {
                        let sys = *((ip as usize + 1) as *const u8);
                        match sys {
                            inst::SYS_PRINT => {
                                let v = *(sp as *mut u64);
                                sp = sp + 8;
                                self.sys_print(v, types.pop().unwrap())?;
                            }
                            _ => panic!("unknown sys"),
                        }
                    }
                    inst::TRUE => {
                        sp -= 8;
                        *(sp as *mut u64) = 1;
                        types.push(Type::Bool);
                    }
                    _ => panic!("unknown opcode"),
                }
                ip = ((ip as usize) + inst::size(*ip)) as *const u8;
            }
        }
    }

    fn sys_print(&mut self, v: u64, type_: Type) -> Result<(), Error> {
        let r = match type_ {
            Type::Bool => {
                write!(self.w, "{}\n", v != 0)
            }
            Type::Float64 => {
                write!(self.w, "{}\n", f64::from_bits(v))
            }
            Type::Nanbox => {
                write!(self.w, "{}\n", nanbox::debug_str(v))
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
