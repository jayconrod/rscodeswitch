use crate::data;
use crate::inst;
use crate::nanbox;
use crate::package::{Function, Package, Type};

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
                })? as *const Function;

            let mut stack = Stack::new();
            let mut sp = stack.end();
            let fp = sp;
            let mut ip = &func.as_ref().unwrap().insts[0] as *const u8;
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
                        Type::Bool => {
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
                            let v = if let (Some(lb), Some(rb)) = (nanbox::to_bool(l), nanbox::to_bool(r)) {
                                lb $op rb
                            } else if let (Some(ln), Some(rn)) = (nanbox::to_f64(l), nanbox::to_f64(r)) {
                                ln $op rn
                            } else if let (Some(ls), Some(rs)) = (nanbox::to_string(l), nanbox::to_string(r)) {
                                ls $op rs
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
                        push!(0, Type::Bool);
                    }
                    inst::FLOAT64 => {
                        let n = f64::from_le_bytes(*((ip as usize + 1) as *const [u8; 8]));
                        push!(n.to_bits(), Type::Float64);
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
                        push!(v, types[i]);
                    }
                    inst::MUL => {
                        binop_num!(*)
                    }
                    inst::NANBOX => {
                        let (v, ty) = pop!();
                        let b = match ty {
                            Type::Bool => nanbox::from_bool(v != 0),
                            Type::String => {
                                let s = v as *const data::String;
                                nanbox::from_string(s)
                            }
                            Type::Float64 | Type::Nanbox => v,
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
                    inst::RET => return Ok(()),
                    inst::STOREGLOBAL => {
                        let i = *((ip as usize + 1) as *const u32) as usize;
                        let v = pop!(Type::Nanbox);
                        self.global_slots[i] = v;
                    }
                    inst::STORELOCAL => {
                        let i = *((ip as usize + 1) as *const u16) as usize;
                        let (v, ty) = pop!();
                        *((fp as usize - (i + 1) * 8) as *mut u64) = v;
                        types[i] = ty;
                    }
                    inst::STRING => {
                        let i = *((ip as usize + 1) as *const u32) as usize;
                        let s = &func.as_ref().unwrap().package.as_ref().unwrap().strings[i]
                            as *const data::String as u64;
                        push!(s, Type::String);
                    }
                    inst::SUB => {
                        binop_num!(-)
                    }
                    inst::SYS => {
                        let sys = *((ip as usize + 1) as *const u8);
                        match sys {
                            inst::SYS_PRINT => {
                                let (v, ty) = pop!();
                                self.sys_print(v, ty)?;
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

    fn sys_print(&mut self, v: u64, type_: Type) -> Result<(), Error> {
        let r = match type_ {
            Type::Bool => {
                write!(self.w, "{}\n", v != 0)
            }
            Type::Float64 => {
                write!(self.w, "{}\n", f64::from_bits(v))
            }
            Type::String => unsafe {
                write!(self.w, "{}\n", (v as *const data::String).as_ref().unwrap())
            },
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
