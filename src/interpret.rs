use crate::inst;
use crate::package::Function;

use std::error;
use std::fmt;
use std::io::Write;

pub fn interpret(w: &mut dyn Write, func: &Function) -> Result<(), Error> {
    unsafe {
        let mut stack = Stack::new();
        let mut sp = stack.end();
        let mut ip = &func.insts[0] as *const u8;

        loop {
            match *ip {
                inst::FLOAT64 => {
                    let n = f64::from_le_bytes(*((ip as usize + 1) as *const [u8; 8]));
                    sp -= 8;
                    *(sp as *mut f64) = n;
                }
                inst::NOP => (),
                inst::POP => {
                    sp += 8;
                }
                inst::RET => return Ok(()),
                inst::SYS => {
                    let sys = *((ip as usize + 1) as *const u8);
                    match sys {
                        inst::SYS_PRINT => {
                            let n = *(sp as *const f64);
                            write!(w, "{}", n).map_err(|_| Error {
                                message: format!("error printing value"),
                            })?;
                            sp = sp + 8;
                        }
                        _ => panic!("unknown sys"),
                    }
                }
                _ => panic!("unknown opcode"),
            }
            ip = ((ip as usize) + inst::size(*ip)) as *const u8;
        }
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
