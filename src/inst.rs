use crate::pos::{EncodedLine, FunctionLineMap, FunctionLineMapBuilder};

use std::fmt;

// List of instructions.
// Keep sorted by name.
// Next opcode: 79.
pub const ADD: u8 = 20;
pub const ADJUSTV: u8 = 68;
pub const ALLOC: u8 = 35;
pub const AND: u8 = 60;
pub const APPENDV: u8 = 70;
pub const B: u8 = 27;
pub const BIF: u8 = 28;
pub const CALLNAMEDPROP: u8 = 45;
pub const CALLNAMEDPROPV: u8 = 74;
pub const CALLNAMEDPROPWITHPROTOTYPE: u8 = 47;
pub const CALLVALUE: u8 = 32;
pub const CALLVALUEV: u8 = 69;
pub const CAPTURE: u8 = 38;
pub const CONST: u8 = 51;
pub const CONSTZERO: u8 = 52;
pub const DIV: u8 = 23;
pub const DUP: u8 = 13;
pub const EQ: u8 = 14;
pub const EXP: u8 = 56;
// pub const FALSE: u8 = 8;
// pub const FLOAT64: u8 = 2;
pub const FLOORDIV: u8 = 54;
pub const FUNCTION: u8 = 31;
pub const GE: u8 = 18;
pub const GT: u8 = 19;
// pub const INT64: u8 = 49;
pub const LE: u8 = 16;
pub const LEN: u8 = 73;
pub const LOAD: u8 = 36;
pub const LOADARG: u8 = 29;
pub const LOADGLOBAL: u8 = 9;
pub const LOADIMPORTGLOBAL: u8 = 76;
pub const LOADINDEXPROPORNIL: u8 = 72;
pub const LOADLOCAL: u8 = 11;
pub const LOADNAMEDPROP: u8 = 42;
pub const LOADNAMEDPROPORNIL: u8 = 50;
pub const LOADPROTOTYPE: u8 = 40;
pub const LOADVARARGS: u8 = 75;
pub const LT: u8 = 17;
pub const MOD: u8 = 55;
pub const MUL: u8 = 22;
pub const NANBOX: u8 = 6;
pub const NE: u8 = 15;
pub const NEG: u8 = 25;
pub const NEWCLOSURE: u8 = 39;
// pub const NIL: u8 = 33;
pub const NOP: u8 = 1;
pub const NOT: u8 = 24;
pub const NOTB: u8 = 53;
pub const OR: u8 = 61;
pub const PANIC: u8 = 65;
pub const PANICLEVEL: u8 = 77;
pub const POP: u8 = 3;
pub const PROTOTYPE: u8 = 48;
pub const RET: u8 = 4;
pub const RETV: u8 = 67;
pub const TOFLOAT: u8 = 64;
pub const SETV: u8 = 66;
pub const SHL: u8 = 58;
pub const SHR: u8 = 59;
pub const STORE: u8 = 37;
pub const STOREARG: u8 = 30;
pub const STOREGLOBAL: u8 = 10;
pub const STOREIMPORTGLOBAL: u8 = 78;
pub const STORELOCAL: u8 = 12;
pub const STOREMETHOD: u8 = 46;
pub const STORENAMEDPROP: u8 = 43;
pub const STOREPROTOTYPE: u8 = 41;
pub const STOREINDEXPROP: u8 = 71;
pub const STRCAT: u8 = 57;
pub const STRING: u8 = 26;
pub const SUB: u8 = 21;
pub const SWAP: u8 = 34;
pub const SWAPN: u8 = 44;
pub const SYS: u8 = 5;
// pub const TRUE: u8 = 7;
pub const TYPEOF: u8 = 63;
pub const XOR: u8 = 62;

// Next sys: 4
pub const SYS_PRINT: u8 = 1;
pub const SYS_TONUMBER: u8 = 2;
pub const SYS_TOSTRING: u8 = 3;

pub const MODE_I64: u8 = 255;
pub const MODE_I32: u8 = 254;
pub const MODE_I16: u8 = 253;
pub const MODE_I8: u8 = 252;
pub const MODE_U64: u8 = 251;
pub const MODE_U32: u8 = 250;
pub const MODE_U16: u8 = 249;
pub const MODE_U8: u8 = 248;
pub const MODE_F64: u8 = 247;
pub const MODE_F32: u8 = 246;
pub const MODE_BOOL: u8 = 245;
pub const MODE_PTR: u8 = 244;
pub const MODE_STRING: u8 = 243;
pub const MODE_CLOSURE: u8 = 242;
pub const MODE_OBJECT: u8 = 241;
pub const MODE_LUA: u8 = 224;
pub const MODE_MIN: u8 = 224;

const INVALID_SIZE: usize = 255;

pub fn size_at(insts: &[u8]) -> usize {
    let (mode_size, inst_size) = if insts[0] >= MODE_MIN {
        (1, size(insts[1]))
    } else {
        (0, size(insts[0]))
    };
    assert_ne!(inst_size, INVALID_SIZE);
    mode_size + inst_size
}

pub const fn size(op: u8) -> usize {
    match op {
        ADD | AND | CALLVALUEV | CONSTZERO | DIV | DUP | EQ | EXP | FLOORDIV | GE | GT | LT
        | LE | LEN | LOAD | LOADINDEXPROPORNIL | LOADPROTOTYPE | LOADVARARGS | MOD | MUL
        | NANBOX | NE | NEG | NOP | NOT | NOTB | OR | PANICLEVEL | POP | PROTOTYPE | RET | RETV
        | SHL | SHR | STORE | STOREINDEXPROP | STOREPROTOTYPE | STRCAT | SUB | SWAP | TOFLOAT
        | TYPEOF | XOR => 1,
        PANIC | SWAPN | SYS => 2,
        ADJUSTV | APPENDV | CALLVALUE | CAPTURE | LOADARG | LOADLOCAL | SETV | STOREARG
        | STORELOCAL => 3,
        ALLOC | B | BIF | CALLNAMEDPROPV | FUNCTION | LOADGLOBAL | LOADNAMEDPROP
        | LOADNAMEDPROPORNIL | STOREGLOBAL | STOREMETHOD | STORENAMEDPROP | STRING => 5,
        CALLNAMEDPROP | CALLNAMEDPROPWITHPROTOTYPE | LOADIMPORTGLOBAL | STOREIMPORTGLOBAL => 7,
        CONST | NEWCLOSURE => 9,
        _ => 255,
    }
}

pub fn mnemonic(op: u8) -> &'static str {
    match op {
        ADD => "add",
        ADJUSTV => "adjustv",
        ALLOC => "alloc",
        AND => "and",
        APPENDV => "appendv",
        B => "b",
        BIF => "bif",
        CALLNAMEDPROP => "callnamedprop",
        CALLNAMEDPROPV => "callnamedpropv",
        CALLNAMEDPROPWITHPROTOTYPE => "callnamedpropwithprototype",
        CALLVALUE => "callvalue",
        CALLVALUEV => "callvaluev",
        CAPTURE => "capture",
        CONST => "const",
        CONSTZERO => "constzero",
        DIV => "div",
        DUP => "dup",
        EQ => "eq",
        EXP => "exp",
        FUNCTION => "function",
        FLOORDIV => "floordiv",
        GE => "ge",
        GT => "gt",
        LE => "le",
        LEN => "len",
        LOAD => "load",
        LOADARG => "loadarg",
        LOADGLOBAL => "loadglobal",
        LOADIMPORTGLOBAL => "loadimportglobal",
        LOADINDEXPROPORNIL => "loadindexpropornil",
        LOADLOCAL => "loadlocal",
        LOADNAMEDPROP => "loadnamedprop",
        LOADNAMEDPROPORNIL => "loadnamedpropornil",
        LOADPROTOTYPE => "loadprototype",
        LOADVARARGS => "loadvarargs",
        LT => "lt",
        MOD => "mod",
        MUL => "mul",
        NANBOX => "nanbox",
        NE => "ne",
        NEG => "neg",
        NEWCLOSURE => "newclosure",
        NOP => "nop",
        NOT => "not",
        NOTB => "notb",
        OR => "or",
        PANIC => "panic",
        PANICLEVEL => "paniclevel",
        POP => "pop",
        PROTOTYPE => "prototype",
        RET => "ret",
        RETV => "retv",
        SETV => "setv",
        SHL => "shl",
        SHR => "shr",
        STORE => "store",
        STOREARG => "storearg",
        STOREINDEXPROP => "storeindexprop",
        STOREGLOBAL => "storeglobal",
        STOREIMPORTGLOBAL => "storeimportglobal",
        STORELOCAL => "storelocal",
        STOREMETHOD => "storemethod",
        STORENAMEDPROP => "storenamedprop",
        STOREPROTOTYPE => "storeprototype",
        STRCAT => "strcat",
        STRING => "string",
        SUB => "sub",
        SWAP => "swap",
        SWAPN => "swapn",
        SYS => "sys",
        TOFLOAT => "tofloat",
        TYPEOF => "typeof",
        XOR => "xor",
        _ => "unknown",
    }
}

pub fn mode_mnemonic(mode: u8) -> &'static str {
    match mode {
        MODE_I32 => ".i32",
        MODE_I16 => ".i16",
        MODE_I8 => ".i8",
        MODE_U64 => ".u64",
        MODE_U32 => ".u32",
        MODE_U16 => ".u16",
        MODE_U8 => ".u8",
        MODE_F64 => ".f64",
        MODE_F32 => ".f32",
        MODE_BOOL => ".bool",
        MODE_PTR => ".ptr",
        MODE_STRING => ".string",
        MODE_CLOSURE => ".closure",
        MODE_OBJECT => ".object",
        MODE_LUA => ".lua",
        _ => ".unknown",
    }
}

pub fn sys_mnemonic(sys: u8) -> &'static str {
    match sys {
        SYS_PRINT => "print",
        SYS_TONUMBER => "tonumber",
        SYS_TOSTRING => "tostring",
        _ => "unknown",
    }
}

pub struct Assembler {
    insts: Vec<u8>,
    flmap: FunctionLineMapBuilder,
}

impl Assembler {
    pub fn new() -> Assembler {
        Assembler {
            insts: Vec::new(),
            flmap: FunctionLineMapBuilder::new(),
        }
    }

    pub fn finish(self) -> Result<(Vec<u8>, FunctionLineMap), impl std::error::Error> {
        if i32::try_from(self.insts.len()).is_err() {
            return Err(Error {
                message: String::from("function is too large (maximum size is 2 GiB)"),
            });
        }
        Ok((self.insts, self.flmap.build()))
    }

    pub fn line(&mut self, el: EncodedLine) {
        self.flmap.add_line(self.insts.len(), el);
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

    pub fn mode(&mut self, mode: u8) {
        self.write_u8(mode);
    }

    pub fn add(&mut self) {
        self.write_u8(ADD);
    }

    pub fn adjustv(&mut self, value_count: u16) {
        self.write_u8(ADJUSTV);
        self.write_u16(value_count);
    }

    pub fn alloc(&mut self, size: u32) {
        self.write_u8(ALLOC);
        self.write_u32(size);
    }

    pub fn and(&mut self) {
        self.write_u8(AND);
    }

    pub fn appendv(&mut self, value_count: u16) {
        self.write_u8(APPENDV);
        self.write_u16(value_count);
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

    pub fn callnamedpropv(&mut self, name_index: u32) {
        self.write_u8(CALLNAMEDPROPV);
        self.write_u32(name_index);
    }

    pub fn callnamedpropwithprototype(&mut self, name_index: u32, arg_count: u16) {
        self.write_u8(CALLNAMEDPROPWITHPROTOTYPE);
        self.write_u32(name_index);
        self.write_u16(arg_count);
    }

    pub fn callvalue(&mut self, arg_count: u16) {
        self.write_u8(CALLVALUE);
        self.write_u16(arg_count);
    }

    pub fn callvaluev(&mut self) {
        self.write_u8(CALLVALUEV);
    }

    pub fn capture(&mut self, i: u16) {
        self.write_u8(CAPTURE);
        self.write_u16(i);
    }

    pub fn const_(&mut self, v: u64) {
        self.write_u8(CONST);
        self.write_u64(v);
    }

    pub fn constzero(&mut self) {
        self.write_u8(CONSTZERO);
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

    pub fn exp(&mut self) {
        self.write_u8(EXP);
    }

    pub fn floordiv(&mut self) {
        self.write_u8(FLOORDIV);
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

    pub fn len(&mut self) {
        self.write_u8(LEN);
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

    pub fn loadimportglobal(&mut self, imp_index: u16, index: u32) {
        self.write_u8(LOADIMPORTGLOBAL);
        self.write_u16(imp_index);
        self.write_u32(index);
    }

    pub fn loadindexpropornil(&mut self) {
        self.write_u8(LOADINDEXPROPORNIL);
    }

    pub fn loadlocal(&mut self, index: u16) {
        self.write_u8(LOADLOCAL);
        self.write_u16(index);
    }

    pub fn loadnamedprop(&mut self, name: u32) {
        self.write_u8(LOADNAMEDPROP);
        self.write_u32(name);
    }

    pub fn loadnamedpropornil(&mut self, name: u32) {
        self.write_u8(LOADNAMEDPROPORNIL);
        self.write_u32(name);
    }

    pub fn loadprototype(&mut self) {
        self.write_u8(LOADPROTOTYPE);
    }

    pub fn loadvarargs(&mut self) {
        self.write_u8(LOADVARARGS);
    }

    pub fn lt(&mut self) {
        self.write_u8(LT);
    }

    pub fn mod_(&mut self) {
        self.write_u8(MOD);
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

    pub fn nop(&mut self) {
        self.write_u8(NOP);
    }

    pub fn not(&mut self) {
        self.write_u8(NOT);
    }

    pub fn notb(&mut self) {
        self.write_u8(NOTB);
    }

    pub fn or(&mut self) {
        self.write_u8(OR);
    }

    pub fn panic(&mut self, level: u8) {
        self.write_u8(PANIC);
        self.write_u8(level);
    }

    pub fn paniclevel(&mut self) {
        self.write_u8(PANICLEVEL);
    }

    pub fn pop(&mut self) {
        self.write_u8(POP);
    }

    pub fn prototype(&mut self) {
        self.write_u8(PROTOTYPE);
    }

    pub fn ret(&mut self) {
        self.write_u8(RET);
    }

    pub fn retv(&mut self) {
        self.write_u8(RETV);
    }

    pub fn setv(&mut self, value_count: u16) {
        self.write_u8(SETV);
        self.write_u16(value_count);
    }

    pub fn shl(&mut self) {
        self.write_u8(SHL);
    }

    pub fn shr(&mut self) {
        self.write_u8(SHR);
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

    pub fn storeimportglobal(&mut self, imp_index: u16, index: u32) {
        self.write_u8(STOREIMPORTGLOBAL);
        self.write_u16(imp_index);
        self.write_u32(index);
    }

    pub fn storeindexprop(&mut self) {
        self.write_u8(STOREINDEXPROP);
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

    pub fn strcat(&mut self) {
        self.write_u8(STRCAT);
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

    pub fn tofloat(&mut self) {
        self.write_u8(TOFLOAT);
    }

    pub fn typeof_(&mut self) {
        self.write_u8(TYPEOF);
    }

    pub fn xor(&mut self) {
        self.write_u8(XOR);
    }

    fn write_u8(&mut self, n: u8) {
        self.insts.push(n)
    }

    fn write_u16(&mut self, n: u16) {
        self.insts.extend_from_slice(&n.to_le_bytes());
    }

    fn write_u32(&mut self, n: u32) {
        self.insts.extend_from_slice(&n.to_le_bytes());
    }

    fn write_u64(&mut self, n: u64) {
        self.insts.extend_from_slice(&n.to_le_bytes());
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
        if insts[p] >= MODE_MIN {
            p += 1;
            continue;
        }
        if insts[p] == B || insts[p] == BIF {
            if p + 5 > insts.len() {
                return Err(fmt::Error);
            }
            let delta = i32::from_le_bytes(insts[p + 1..p + 5].try_into().unwrap());
            let offset = (p as i32 + 1 + delta) as usize;
            label_offsets.push(offset);
        }
        p += size_at(&insts[p..]);
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
        let mode = if insts[p] < MODE_MIN {
            ""
        } else {
            let m = insts[p];
            p += 1;
            match m {
                MODE_I32 => ".i32",
                MODE_I16 => ".i16",
                MODE_I8 => ".i8",
                MODE_U64 => ".u64",
                MODE_U32 => ".u32",
                MODE_U16 => ".u16",
                MODE_U8 => ".u8",
                MODE_F64 => ".f64",
                MODE_F32 => ".f32",
                MODE_BOOL => ".bool",
                MODE_PTR => ".ptr",
                MODE_STRING => ".string",
                MODE_CLOSURE => ".closure",
                MODE_OBJECT => ".object",
                MODE_LUA => ".lua",
                _ => return Err(fmt::Error),
            }
        };
        write!(f, "  {}{}", mnemonic(insts[p]), mode)?;
        match insts[p] {
            ADD | AND | CALLVALUEV | CONSTZERO | DIV | DUP | EXP | EQ | FLOORDIV | GE | GT | LT
            | LE | LEN | LOAD | LOADINDEXPROPORNIL | LOADPROTOTYPE | LOADVARARGS | MOD | MUL
            | NANBOX | NE | NEG | NOP | NOT | NOTB | OR | PANICLEVEL | POP | PROTOTYPE | RET
            | RETV | SHL | SHR | STORE | STOREINDEXPROP | STOREPROTOTYPE | STRCAT | SUB | SWAP
            | TOFLOAT | TYPEOF | XOR => {
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
            CALLNAMEDPROP | CALLNAMEDPROPWITHPROTOTYPE => {
                if p + 7 > insts.len() {
                    return Err(fmt::Error);
                }
                let name_index = u32::from_le_bytes(insts[p + 1..p + 5].try_into().unwrap());
                let arg_count = u16::from_le_bytes(insts[p + 5..p + 7].try_into().unwrap());
                write!(f, " {} {}\n", name_index, arg_count)?;
            }
            ADJUSTV | APPENDV | CALLVALUE | CAPTURE | LOADARG | LOADLOCAL | SETV | STOREARG
            | STORELOCAL => {
                if p + 3 > insts.len() {
                    return Err(fmt::Error);
                }
                let n = u16::from_le_bytes(insts[p + 1..p + 3].try_into().unwrap());
                write!(f, " {}\n", n)?;
            }
            ALLOC | CALLNAMEDPROPV | FUNCTION | LOADGLOBAL | LOADNAMEDPROP | LOADNAMEDPROPORNIL
            | STOREGLOBAL | STOREMETHOD | STORENAMEDPROP | STRING => {
                if p + 5 > insts.len() {
                    return Err(fmt::Error);
                }
                let n = u32::from_le_bytes(insts[p + 1..p + 5].try_into().unwrap());
                write!(f, " {}\n", n)?;
            }
            CONST => {
                if p + 9 > insts.len() {
                    return Err(fmt::Error);
                }
                let n = u64::from_le_bytes(insts[p + 1..p + 9].try_into().unwrap());
                write!(f, " {}\n", n)?;
            }
            LOADIMPORTGLOBAL | STOREIMPORTGLOBAL => {
                if p + 7 > insts.len() {
                    return Err(fmt::Error);
                }
                let imp_index = u16::from_le_bytes(insts[p + 1..p + 3].try_into().unwrap());
                let index = u32::from_le_bytes(insts[p + 3..p + 7].try_into().unwrap());
                write!(f, " {} {}\n", imp_index, index)?;
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
            PANIC | SWAPN => {
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
