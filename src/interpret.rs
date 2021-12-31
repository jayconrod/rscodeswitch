use crate::inst;
use crate::nanbox;
use crate::package::{Function, Type};

use std::error;
use std::fmt;
use std::io::Write;

pub fn interpret(w: &mut dyn Write, func: &Function) -> Result<(), Error> {
    unsafe {
        let mut stack = Stack::new();
        let mut sp = stack.end();
        let mut ip = &func.insts[0] as *const u8;
        let mut types = Vec::new();

        loop {
            match *ip {
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
                inst::NOP => (),
                inst::POP => {
                    sp += 8;
                    types.pop();
                }
                inst::RET => return Ok(()),
                inst::SYS => {
                    let sys = *((ip as usize + 1) as *const u8);
                    match sys {
                        inst::SYS_PRINT => {
                            let v = *(sp as *mut u64);
                            sp = sp + 8;
                            sys_print(w, v, types.pop().unwrap())?;
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

fn sys_print(w: &mut dyn Write, v: u64, type_: Type) -> Result<(), Error> {
    let r = match type_ {
        Type::Bool => {
            write!(w, "{}\n", v != 0)
        }
        Type::Float64 => {
            write!(w, "{}\n", f64::from_bits(v))
        }
        Type::Nanbox => {
            write!(w, "{}\n", nanbox::debug_str(v))
        }
    };
    r.map_err(|_| Error {
        message: String::from("error printing value"),
    })
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
