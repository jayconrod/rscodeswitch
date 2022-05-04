use crate::inst::{self, Assembler};
use crate::pos::{FunctionLineMap, PackageLineMap};
use crate::runtime::Object;

use std::collections::HashMap;
use std::fmt::{self, Formatter};
use std::mem;

pub struct Package {
    pub name: String,
    pub globals: Vec<Global>,
    pub functions: Vec<Function>,
    pub init_index: Option<u32>,
    pub strings: Vec<Vec<u8>>,
    pub types: Vec<Type>,
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
        sep = "\n\n";
        for (i, t) in self.types.iter().enumerate() {
            write!(f, "{}type {} {}", sep, i, t)?;
            sep = "\n";
        }
        Ok(())
    }
}

pub struct Global {
    pub name: std::string::String,
    pub type_: Type,
}

impl fmt::Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "var {};", self.name)
    }
}

pub struct Function {
    pub name: std::string::String,
    pub insts: Vec<u8>,
    pub cell_types: Vec<Type>,
    pub param_types: Vec<Type>,
    pub var_param_type: Option<Type>,
    pub return_types: Vec<Type>,
    pub var_return_type: Option<Type>,
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
    pub type_: Type,
    pub link: *mut Global,
}

impl GlobalImport {
    pub fn new(name: String, type_: Type) -> GlobalImport {
        GlobalImport {
            name,
            type_,
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

pub struct Builder {
    pub string_index: HashMap<&'static str, u32>,
    pub type_index: HashMap<Type, u32>,
    pub asm: Assembler,
    pub package: Package,
    pub function_name_index: Vec<u32>,
}

impl Builder {
    pub fn new(name: String) -> Builder {
        Builder {
            string_index: HashMap::new(),
            type_index: HashMap::new(),
            asm: Assembler::new(),
            package: Package {
                name,
                globals: Vec::new(),
                functions: Vec::new(),
                init_index: None,
                strings: Vec::new(),
                types: Vec::new(),
                line_map: PackageLineMap { files: Vec::new() },
                imports: Vec::new(),
            },
            function_name_index: Vec::new(),
        }
    }

    pub fn build(mut self) -> Package {
        let init_index = (self.package.functions.len() - 1) as u32;
        self.package.init_index = Some(init_index);
        self.package
    }

    pub fn finish_function(
        &mut self,
        name: &'static str,
        param_count: usize,
        is_variadic: bool,
    ) -> u32 {
        let mut asm = Assembler::new();
        mem::swap(&mut self.asm, &mut asm);
        let (insts, flmap) = asm.finish().unwrap();
        let var_param_type = if is_variadic {
            Some(Type::NanBox)
        } else {
            None
        };
        let param_types = vec![Type::NanBox; param_count];
        let fi: u32 = self.package.functions.len().try_into().unwrap();
        self.package.functions.push(Function {
            name: String::from(name),
            insts,
            param_types,
            var_param_type,
            return_types: Vec::new(),
            var_return_type: Some(Type::NanBox),
            cell_types: Vec::new(),
            line_map: flmap,
        });
        let si = self.ensure_string(name);
        self.function_name_index.push(si);
        fi
    }

    pub fn add_global(&mut self, name: &'static str, type_: Type) -> u32 {
        let i = self.package.globals.len() as u32;
        self.package.globals.push(Global {
            name: String::from(name),
            type_,
        });
        i
    }

    pub fn ensure_string(&mut self, s: &'static str) -> u32 {
        match self.string_index.get(s) {
            Some(&i) => i,
            None => {
                let i = self.package.strings.len().try_into().unwrap();
                self.package.strings.push(Vec::from(s));
                self.string_index.insert(s, i);
                i
            }
        }
    }

    pub fn ensure_type(&mut self, t: Type) -> u32 {
        match self.type_index.get(&t) {
            Some(&i) => i,
            None => {
                let i = self.package.types.len().try_into().unwrap();
                self.type_index.insert(t.clone(), i);
                self.package.types.push(t);
                i
            }
        }
    }
}
