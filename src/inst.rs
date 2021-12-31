use std::fmt;
use std::mem::swap;

// List of instructions.
// Keep sorted by name.
// Next opcode: 11.
pub const FALSE: u8 = 8;
pub const FLOAT64: u8 = 2;
pub const LOADGLOBAL: u8 = 9;
pub const NANBOX: u8 = 6;
pub const NOP: u8 = 1;
pub const POP: u8 = 3;
pub const RET: u8 = 4;
pub const STOREGLOBAL: u8 = 10;
pub const SYS: u8 = 5;
pub const TRUE: u8 = 7;

pub const SYS_PRINT: u8 = 1;

pub fn size(op: u8) -> usize {
    match op {
        FALSE | NANBOX | NOP | POP | RET | TRUE => 1,
        SYS => 2,
        LOADGLOBAL | STOREGLOBAL => 5,
        FLOAT64 => 9,
        _ => panic!("unknown opcode"),
    }
}

pub fn mnemonic(op: u8) -> &'static str {
    match op {
        FALSE => "false",
        FLOAT64 => "float64",
        LOADGLOBAL => "loadglobal",
        NANBOX => "nanbox",
        NOP => "nop",
        POP => "pop",
        RET => "ret",
        STOREGLOBAL => "storeglobal",
        SYS => "sys",
        TRUE => "true",
        _ => panic!("unknown opcode"),
    }
}

pub fn sys_mnemonic(sys: u8) -> &'static str {
    match sys {
        SYS_PRINT => "print",
        _ => panic!("unknown sys"),
    }
}

pub struct Assembler {
    insts: Vec<u8>,
}

impl Assembler {
    pub fn new() -> Assembler {
        Assembler { insts: Vec::new() }
    }

    pub fn finish(&mut self) -> Vec<u8> {
        let mut insts = Vec::new();
        swap(&mut self.insts, &mut insts);
        insts
    }

    pub fn false_(&mut self) {
        self.write_u8(FALSE);
    }

    pub fn float64(&mut self, n: f64) {
        self.write_u8(FLOAT64);
        self.write_f64(n);
    }

    pub fn loadglobal(&mut self, index: u32) {
        self.write_u8(LOADGLOBAL);
        self.write_u32(index);
    }

    pub fn nanbox(&mut self) {
        self.write_u8(NANBOX);
    }

    pub fn nop(&mut self) {
        self.write_u8(NOP);
    }

    pub fn pop(&mut self) {
        self.write_u8(POP);
    }

    pub fn ret(&mut self) {
        self.write_u8(RET);
    }

    pub fn storeglobal(&mut self, index: u32) {
        self.write_u8(STOREGLOBAL);
        self.write_u32(index);
    }

    pub fn sys(&mut self, sys: u8) {
        self.write_u8(SYS);
        self.write_u8(sys);
    }

    pub fn true_(&mut self) {
        self.write_u8(TRUE);
    }

    fn write_u8(&mut self, n: u8) {
        self.insts.push(n)
    }

    fn write_u32(&mut self, n: u32) {
        for b in n.to_le_bytes() {
            self.insts.push(b)
        }
    }

    fn write_f64(&mut self, n: f64) {
        for b in n.to_le_bytes() {
            self.insts.push(b)
        }
    }
}

pub fn disassemble(insts: &[u8], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut p = 0;
    while p < insts.len() {
        f.write_str("  ")?;
        f.write_str(mnemonic(insts[p]))?;
        match insts[p] {
            FALSE | NANBOX | NOP | POP | RET | TRUE => {
                f.write_str("\n")?;
            }
            FLOAT64 => {
                if p + 9 > insts.len() {
                    return Err(fmt::Error);
                }
                let n = f64::from_le_bytes(insts[p + 1..p + 9].try_into().unwrap());
                write!(f, " {}\n", n)?;
            }
            LOADGLOBAL | STOREGLOBAL => {
                if p + 5 > insts.len() {
                    return Err(fmt::Error);
                }
                let n = u32::from_le_bytes(insts[p + 1..p + 5].try_into().unwrap());
                write!(f, " {}\n", n)?;
            }
            SYS => {
                if p + 2 > insts.len() {
                    return Err(fmt::Error);
                }
                let sys = insts[p + 1];
                write!(f, " {}\n", sys_mnemonic(sys))?;
            }
            _ => return Err(fmt::Error),
        }
        p += size(insts[p]);
    }
    Ok(())
}
