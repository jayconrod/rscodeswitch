use std::fmt;
use std::mem::swap;

// List of instructions.
// Keep sorted by name.
// Next opcode: 47.
pub const ADD: u8 = 20;
pub const ALLOC: u8 = 35;
pub const B: u8 = 27;
pub const BIF: u8 = 28;
pub const CALLNAMEDPROP: u8 = 45;
pub const CALLVALUE: u8 = 32;
pub const CELL: u8 = 38;
pub const DIV: u8 = 23;
pub const DUP: u8 = 13;
pub const EQ: u8 = 14;
pub const FALSE: u8 = 8;
pub const FLOAT64: u8 = 2;
pub const FUNCTION: u8 = 31;
pub const GE: u8 = 18;
pub const GT: u8 = 19;
pub const LE: u8 = 16;
pub const LOAD: u8 = 36;
pub const LOADARG: u8 = 29;
pub const LOADGLOBAL: u8 = 9;
pub const LOADLOCAL: u8 = 11;
pub const LOADNAMEDPROP: u8 = 42;
pub const LOADPROTOTYPE: u8 = 40;
pub const LT: u8 = 17;
pub const MUL: u8 = 22;
pub const NANBOX: u8 = 6;
pub const NE: u8 = 15;
pub const NEG: u8 = 25;
pub const NEWCLOSURE: u8 = 39;
pub const NIL: u8 = 33;
pub const NOP: u8 = 1;
pub const NOT: u8 = 24;
pub const POP: u8 = 3;
pub const RET: u8 = 4;
pub const STORE: u8 = 37;
pub const STOREARG: u8 = 30;
pub const STOREGLOBAL: u8 = 10;
pub const STORELOCAL: u8 = 12;
pub const STOREMETHOD: u8 = 46;
pub const STORENAMEDPROP: u8 = 43;
pub const STOREPROTOTYPE: u8 = 41;
pub const STRING: u8 = 26;
pub const SUB: u8 = 21;
pub const SWAP: u8 = 34;
pub const SWAPN: u8 = 44;
pub const SYS: u8 = 5;
pub const TRUE: u8 = 7;

pub const SYS_PRINT: u8 = 1;

pub fn size(op: u8) -> usize {
    match op {
        ADD | DIV | DUP | EQ | FALSE | GE | GT | LT | LE | LOAD | LOADPROTOTYPE | MUL | NANBOX
        | NE | NEG | NIL | NOP | NOT | POP | RET | STORE | STOREPROTOTYPE | SUB | SWAP | TRUE => 1,
        SWAPN | SYS => 2,
        CALLVALUE | CELL | LOADARG | LOADLOCAL | STOREARG | STORELOCAL => 3,
        ALLOC | B | BIF | FUNCTION | LOADGLOBAL | LOADNAMEDPROP | STOREGLOBAL | STOREMETHOD
        | STORENAMEDPROP | STRING => 5,
        CALLNAMEDPROP => 7,
        FLOAT64 | NEWCLOSURE => 9,
        _ => panic!("unknown opcode"),
    }
}

pub fn mnemonic(op: u8) -> &'static str {
    match op {
        ADD => "add",
        ALLOC => "alloc",
        B => "b",
        BIF => "bif",
        CALLNAMEDPROP => "callnamedprop",
        CALLVALUE => "callvalue",
        CELL => "cell",
        DIV => "div",
        DUP => "dup",
        EQ => "eq",
        FALSE => "false",
        FLOAT64 => "float64",
        FUNCTION => "function",
        GE => "ge",
        GT => "gt",
        LE => "le",
        LOAD => "load",
        LOADARG => "loadarg",
        LOADGLOBAL => "loadglobal",
        LOADLOCAL => "loadlocal",
        LOADNAMEDPROP => "loadnamedprop",
        LOADPROTOTYPE => "loadprototype",
        LT => "lt",
        MUL => "mul",
        NANBOX => "nanbox",
        NE => "ne",
        NEG => "neg",
        NEWCLOSURE => "newclosure",
        NIL => "nil",
        NOP => "nop",
        NOT => "not",
        POP => "pop",
        RET => "ret",
        STORE => "store",
        STOREARG => "storearg",
        STOREGLOBAL => "storeglobal",
        STORELOCAL => "storelocal",
        STOREMETHOD => "storemethod",
        STORENAMEDPROP => "storenamedprop",
        STOREPROTOTYPE => "storeprototype",
        STRING => "string",
        SUB => "sub",
        SWAP => "swap",
        SWAPN => "swapn",
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

    pub fn finish(&mut self) -> Result<Vec<u8>, impl std::error::Error> {
        if i32::try_from(self.insts.len()).is_err() {
            return Err(Error {
                message: String::from("function is too large (maximum size is 2 GiB)"),
            });
        }
        let mut insts = Vec::new();
        swap(&mut self.insts, &mut insts);
        Ok(insts)
    }

    pub fn bind(&mut self, label: &mut Label) {
        match label {
            Label::Bound { .. } => panic!("label already bound"),
            Label::Unbound {
                last_branch_offset: mut offset,
            } => {
                if i32::try_from(self.insts.len()).is_err() {
                    // Instruction list is too long to represent labels,
                    // but we can't return errors here. The client will
                    // see an error from finish though.
                    *label = Label::Bound { offset: !0 }
                }
                let bound_offset: i32 = self.insts.len().try_into().unwrap();
                while offset != -1 {
                    let patch_site = &mut self.insts[offset as usize..offset as usize + 4];
                    let prev_offset = i32::from_le_bytes((*patch_site).try_into().unwrap());
                    let delta = bound_offset - offset;
                    for (i, b) in delta.to_le_bytes().iter().enumerate() {
                        patch_site[i] = *b;
                    }
                    offset = prev_offset;
                }
                *label = Label::Bound {
                    offset: bound_offset,
                };
            }
        }
    }

    pub fn add(&mut self) {
        self.write_u8(ADD);
    }

    pub fn alloc(&mut self, index: u32) {
        self.write_u8(ALLOC);
        self.write_u32(index);
    }

    pub fn b(&mut self, label: &mut Label) {
        self.write_u8(B);
        self.write_label(label);
    }

    pub fn bif(&mut self, label: &mut Label) {
        self.write_u8(BIF);
        self.write_label(label);
    }

    pub fn callnamedprop(&mut self, name_index: u32, arg_count: u16) {
        self.write_u8(CALLNAMEDPROP);
        self.write_u32(name_index);
        self.write_u16(arg_count);
    }

    pub fn callvalue(&mut self, arg_count: u16) {
        self.write_u8(CALLVALUE);
        self.write_u16(arg_count);
    }

    pub fn cell(&mut self, i: u16) {
        self.write_u8(CELL);
        self.write_u16(i);
    }

    pub fn div(&mut self) {
        self.write_u8(DIV);
    }

    pub fn dup(&mut self) {
        self.write_u8(DUP);
    }

    pub fn eq(&mut self) {
        self.write_u8(EQ);
    }

    pub fn false_(&mut self) {
        self.write_u8(FALSE);
    }

    pub fn float64(&mut self, n: f64) {
        self.write_u8(FLOAT64);
        self.write_f64(n);
    }

    pub fn function(&mut self, index: u32) {
        self.write_u8(FUNCTION);
        self.write_u32(index);
    }

    pub fn ge(&mut self) {
        self.write_u8(GE);
    }

    pub fn gt(&mut self) {
        self.write_u8(GT);
    }

    pub fn le(&mut self) {
        self.write_u8(LE);
    }

    pub fn load(&mut self) {
        self.write_u8(LOAD);
    }

    pub fn loadarg(&mut self, index: u16) {
        self.write_u8(LOADARG);
        self.write_u16(index);
    }

    pub fn loadglobal(&mut self, index: u32) {
        self.write_u8(LOADGLOBAL);
        self.write_u32(index);
    }

    pub fn loadlocal(&mut self, index: u16) {
        self.write_u8(LOADLOCAL);
        self.write_u16(index);
    }

    pub fn loadnamedprop(&mut self, name: u32) {
        self.write_u8(LOADNAMEDPROP);
        self.write_u32(name);
    }

    pub fn loadprototype(&mut self) {
        self.write_u8(LOADPROTOTYPE);
    }

    pub fn lt(&mut self) {
        self.write_u8(LT);
    }

    pub fn mul(&mut self) {
        self.write_u8(MUL);
    }

    pub fn nanbox(&mut self) {
        self.write_u8(NANBOX);
    }

    pub fn ne(&mut self) {
        self.write_u8(NE);
    }

    pub fn neg(&mut self) {
        self.write_u8(NEG);
    }

    pub fn newclosure(&mut self, fn_index: u32, capture_count: u16, bound_arg_count: u16) {
        self.write_u8(NEWCLOSURE);
        self.write_u32(fn_index);
        self.write_u16(capture_count);
        self.write_u16(bound_arg_count);
    }

    pub fn nil(&mut self) {
        self.write_u8(NIL);
    }

    pub fn nop(&mut self) {
        self.write_u8(NOP);
    }

    pub fn not(&mut self) {
        self.write_u8(NOT);
    }

    pub fn pop(&mut self) {
        self.write_u8(POP);
    }

    pub fn ret(&mut self) {
        self.write_u8(RET);
    }

    pub fn store(&mut self) {
        self.write_u8(STORE);
    }

    pub fn storearg(&mut self, index: u16) {
        self.write_u8(STOREARG);
        self.write_u16(index);
    }

    pub fn storeglobal(&mut self, index: u32) {
        self.write_u8(STOREGLOBAL);
        self.write_u32(index);
    }

    pub fn storelocal(&mut self, index: u16) {
        self.write_u8(STORELOCAL);
        self.write_u16(index);
    }

    pub fn storemethod(&mut self, name: u32) {
        self.write_u8(STOREMETHOD);
        self.write_u32(name);
    }

    pub fn storenamedprop(&mut self, name: u32) {
        self.write_u8(STORENAMEDPROP);
        self.write_u32(name);
    }

    pub fn storeprototype(&mut self) {
        self.write_u8(STOREPROTOTYPE);
    }

    pub fn string(&mut self, i: u32) {
        self.write_u8(STRING);
        self.write_u32(i);
    }

    pub fn sub(&mut self) {
        self.write_u8(SUB);
    }

    pub fn swap(&mut self) {
        self.write_u8(SWAP);
    }

    pub fn swapn(&mut self, n: u8) {
        self.write_u8(SWAPN);
        self.write_u8(n);
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

    fn write_u16(&mut self, n: u16) {
        for b in n.to_le_bytes() {
            self.insts.push(b)
        }
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

    fn write_label(&mut self, label: &mut Label) {
        if i32::try_from(self.insts.len()).is_err() {
            self.write_u32(0);
            return;
        }
        match label {
            Label::Unbound {
                ref mut last_branch_offset,
            } => {
                let label_offset = self.insts.len() as i32;
                self.write_u32(*last_branch_offset as u32);
                *last_branch_offset = label_offset;
            }
            Label::Bound { offset } => {
                let delta = *offset - self.insts.len() as i32;
                self.write_u32(delta as u32);
            }
        }
    }
}

pub enum Label {
    Unbound { last_branch_offset: i32 },
    Bound { offset: i32 },
}

impl Label {
    pub fn new() -> Label {
        Label::Unbound {
            last_branch_offset: -1,
        }
    }
}

#[derive(Debug)]
struct Error {
    message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

pub fn disassemble(insts: &[u8], f: &mut fmt::Formatter) -> fmt::Result {
    // Scan the instructions for branches, so we know where to write labels.
    // We don't know the original names of the labels, so we'll number them.
    let mut label_offsets = Vec::new();
    let mut p = 0;
    while p < insts.len() {
        match insts[p] {
            B | BIF => {
                if p + 5 > insts.len() {
                    return Err(fmt::Error);
                }
                let delta = i32::from_le_bytes(insts[p + 1..p + 5].try_into().unwrap());
                let offset = (p as i32 + 1 + delta) as usize;
                label_offsets.push(offset);
            }
            _ => (),
        }
        p += size(insts[p]);
    }
    label_offsets.sort();
    label_offsets.dedup();

    // Print the instructions, with labels first where needed.
    let mut p = 0;
    let mut li = 0;
    while p < insts.len() {
        if li < label_offsets.len() && label_offsets[li] == p {
            write!(f, "L{}:\n", li)?;
            li += 1;
        }
        f.write_str("  ")?;
        f.write_str(mnemonic(insts[p]))?;
        match insts[p] {
            ADD | DIV | DUP | EQ | FALSE | GE | GT | LT | LE | LOAD | LOADPROTOTYPE | MUL
            | NANBOX | NE | NEG | NIL | NOP | NOT | POP | RET | STORE | STOREPROTOTYPE | SUB
            | SWAP | TRUE => {
                f.write_str("\n")?;
            }
            B | BIF => {
                if p + 5 > insts.len() {
                    return Err(fmt::Error);
                }
                let delta = i32::from_le_bytes(insts[p + 1..p + 5].try_into().unwrap());
                let offset = (p as i32 + 1 + delta) as usize;
                match label_offsets.binary_search(&offset) {
                    Ok(li) => {
                        write!(f, " L{}\n", li)?;
                    }
                    Err(_) => {
                        write!(f, " {}??\n", delta)?;
                    }
                }
            }
            CALLNAMEDPROP => {
                if p + 7 > insts.len() {
                    return Err(fmt::Error);
                }
                let name_index = u32::from_le_bytes(insts[p + 1..p + 5].try_into().unwrap());
                let arg_count = u16::from_le_bytes(insts[p + 5..p + 7].try_into().unwrap());
                write!(f, " {} {}\n", name_index, arg_count)?;
            }
            CALLVALUE | CELL | LOADARG | LOADLOCAL | STOREARG | STORELOCAL => {
                if p + 3 > insts.len() {
                    return Err(fmt::Error);
                }
                let n = u16::from_le_bytes(insts[p + 1..p + 3].try_into().unwrap());
                write!(f, " {}\n", n)?;
            }
            ALLOC | FUNCTION | LOADGLOBAL | LOADNAMEDPROP | STOREGLOBAL | STOREMETHOD
            | STORENAMEDPROP | STRING => {
                if p + 5 > insts.len() {
                    return Err(fmt::Error);
                }
                let n = u32::from_le_bytes(insts[p + 1..p + 5].try_into().unwrap());
                write!(f, " {}\n", n)?;
            }
            FLOAT64 => {
                if p + 9 > insts.len() {
                    return Err(fmt::Error);
                }
                let n = f64::from_le_bytes(insts[p + 1..p + 9].try_into().unwrap());
                write!(f, " {}\n", n)?;
            }
            NEWCLOSURE => {
                if p + 9 > insts.len() {
                    return Err(fmt::Error);
                }
                let fn_index = u32::from_le_bytes(insts[p + 1..p + 5].try_into().unwrap());
                let capture_count = u16::from_le_bytes(insts[p + 5..p + 7].try_into().unwrap());
                let bound_arg_count = u16::from_le_bytes(insts[p + 7..p + 9].try_into().unwrap());
                write!(f, " {} {} {}\n", fn_index, capture_count, bound_arg_count)?;
            }
            SWAPN => {
                if p + 2 > insts.len() {
                    return Err(fmt::Error);
                }
                let n = insts[p + 1];
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
