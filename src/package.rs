use crate::inst;
use crate::pos::{FunctionLineMap, PackageLineMap};
use crate::runtime::Object;

use std::fmt::{self, Formatter};
use std::mem;

// TODO: divide Package and the structs it depends on into separate compile-time
// and run-time parts. For example, a run-time Global would have a value which
// could be mutated by the interpreter.
pub struct Package {
    pub name: String,
    pub globals: Vec<Global>,
    pub functions: Vec<Function>,
    pub strings: Vec<Vec<u8>>,
    pub line_map: PackageLineMap,
    pub imports: Vec<PackageImport>,
}

impl fmt::Display for Package {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut sep = "";
        for gbl in &self.globals {
            write!(f, "{}{}", sep, gbl)?;
            sep = "\n\n";
        }
        for func in &self.functions {
            write!(f, "{}{}", sep, func)?;
            sep = "\n\n";
        }
        sep = "\n\n";
        for (i, s) in self.strings.iter().enumerate() {
            let ss = String::from_utf8_lossy(s);
            write!(f, "{}string {} \"{}\"", sep, i, ss)?;
            sep = "\n";
        }
        Ok(())
    }
}

pub struct Global {
    pub name: std::string::String,
}

impl fmt::Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "var {};", self.name)
    }
}

pub struct Function {
    pub name: std::string::String,
    pub insts: Vec<u8>,
    pub param_types: Vec<Type>,
    pub cell_types: Vec<Type>,
    pub var_param_type: Option<Type>,
    pub line_map: FunctionLineMap,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "function {}() {{\n", self.name)?;
        inst::disassemble(&self.insts, f)?;
        f.write_str("}")
    }
}

pub struct PackageImport {
    pub name: String,
    pub globals: Vec<GlobalImport>,
    pub functions: Vec<FunctionImport>,
}

impl PackageImport {
    pub fn new(
        name: String,
        globals: Vec<GlobalImport>,
        functions: Vec<FunctionImport>,
    ) -> PackageImport {
        PackageImport {
            name,
            globals,
            functions,
        }
    }
}

pub struct GlobalImport {
    pub name: String,
    pub link: *mut Global,
}

impl GlobalImport {
    pub fn new(name: String) -> GlobalImport {
        GlobalImport {
            name,
            link: 0 as *mut Global,
        }
    }
}

pub struct FunctionImport {
    pub name: String,
    pub param_types: Vec<Type>,
    pub var_param_type: Option<Type>,
    pub link: *const Function,
}

impl FunctionImport {
    pub fn new(
        name: String,
        param_types: Vec<Type>,
        var_param_type: Option<Type>,
    ) -> FunctionImport {
        FunctionImport {
            name,
            param_types,
            var_param_type,
            link: 0 as *const Function,
        }
    }
}

// TODO: move Type onto the CodeSwitch heap. The interpreter needs to maintain
// a stack of these, and because types may point to other types, they may have
// parts allocated on the heap, which means a lot of instructions may allocate.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Nil,
    Bool,
    Int64,
    Float64,
    String,
    Function,
    Closure,
    Object,
    NanBox,
    Pointer(Box<Type>),
}

impl Type {
    pub fn size(&self) -> usize {
        match self {
            Type::Nil => 0,
            Type::Bool => 1,
            Type::Int64 => 8,
            Type::Float64 => 8,
            Type::NanBox => 8,
            Type::Object => mem::size_of::<Object>(),
            Type::String | Type::Function | Type::Closure | Type::Pointer(_) => {
                mem::size_of::<usize>()
            } // TODO: String should be data::String, not *const data::String.
        }
    }

    pub fn is_pointer(&self) -> bool {
        match self {
            // TODO: String should be data::String, not *const data::String
            Type::String | Type::Function | Type::Closure | Type::NanBox | Type::Pointer(_) => true,
            _ => false,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Pointer(t) => {
                write!(f, "*{}", t)
            }
            _ => {
                let s = match self {
                    Type::Nil => "nil",
                    Type::Bool => "bool",
                    Type::Int64 => "i64",
                    Type::Float64 => "f64",
                    Type::String => "string",
                    Type::Function => "function",
                    Type::Closure => "closure",
                    Type::Object => "object",
                    Type::NanBox => "nanbox",
                    _ => unreachable!(),
                };
                f.write_str(s)
            }
        }
    }
}
