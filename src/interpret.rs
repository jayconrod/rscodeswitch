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

            loop {
                match *ip {
                    inst::DUP => {
                        let v = *(sp as *mut u64);
                        sp -= 8;
                        *(sp as *mut u64) = v;
                        types.push(types[types.len() - 1]);
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
                    inst::LOADLOCAL => {
                        let i = *((ip as usize + 1) as *const u16) as usize;
                        let v = *((fp as usize - (i + 1) * 8) as *const u64);
                        sp -= 8;
                        *(sp as *mut u64) = v;
                        types.push(types[i]);
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
