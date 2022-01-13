use crate::data::{self, SetValue, Slice};
use crate::heap::{Handle, Ptr, Set, HEAP};
use crate::inst;

use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::mem;

pub struct Package {
    pub globals: Vec<Global>,
    pub functions: Vec<Function>,
    pub types: Vec<Type>,
    pub strings: Handle<Slice<data::String>>,
}

impl Package {
    pub fn global_by_name(&self, name: &str) -> Option<&Global> {
        self.global_index_by_name(name).map(|i| &self.globals[i])
    }

    pub fn global_index_by_name(&self, name: &str) -> Option<usize> {
        self.globals
            .iter()
            .enumerate()
            .find(|(_, g)| g.name == name)
            .map(|(i, _)| i)
    }

    pub fn function_by_name(&self, name: &str) -> Option<&Function> {
        self.function_index_by_name(name)
            .map(|i| &self.functions[i])
    }

    pub fn function_index_by_name(&self, name: &str) -> Option<usize> {
        self.functions
            .iter()
            .enumerate()
            .find(|(_, f)| f.name == name)
            .map(|(i, _)| i)
    }
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
        for ty in &self.types {
            write!(f, "{}type {}", sep, ty)?;
            sep = "\n";
        }
        sep = "\n\n";
        for s in &*self.strings {
            write!(f, "{}string {}", sep, s)?;
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
    pub package: *const Package,
    pub param_types: Vec<Type>,
    pub cell_types: Vec<Type>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "function {}() {{\n", self.name)?;
        inst::disassemble(&self.insts, f)?;
        f.write_str("}")
    }
}

pub struct Class {
    pub name: std::string::String,
    pub methods: Vec<*const Function>,
}

impl fmt::Display for Class {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "class {} {{", self.name)?;
        for method in &self.methods {
            let name = unsafe { &method.as_ref().unwrap().name };
            write!(f, "\n  method {}", name)?;
        }
        f.write_str("\n}")
    }
}

// TODO: move Type onto the CodeSwitch heap. The interpreter needs to maintain
// a stack of these, and because types may point to other types, they may have
// parts allocated on the heap, which means a lot of instructions may allocate.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Nil,
    Bool,
    Float64,
    String,
    Function,
    Closure,
    Object,
    Nanbox,
    Pointer(Box<Type>),
}

impl Type {
    pub fn size(&self) -> usize {
        match self {
            Type::Nil => 0,
            Type::Bool => 1,
            Type::Float64 => 8,
            Type::Nanbox => 8,
            Type::Object => mem::size_of::<Object>(),
            Type::String | Type::Function | Type::Closure | Type::Pointer(_) => {
                mem::size_of::<usize>()
            } // TODO: String should be data::String, not *const data::String.
        }
    }

    pub fn is_pointer(&self) -> bool {
        match self {
            // TODO: String should be data::String, not *const data::String
            Type::String | Type::Function | Type::Closure | Type::Nanbox | Type::Pointer(_) => true,
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
                    Type::Float64 => "f64",
                    Type::String => "string",
                    Type::Function => "function",
                    Type::Closure => "closure",
                    Type::Object => "object",
                    Type::Nanbox => "nanbox",
                    _ => unreachable!(),
                };
                f.write_str(s)
            }
        }
    }
}

pub struct Closure {
    pub function: Ptr<Function>,
}

impl Closure {
    pub fn alloc(n: u16) -> *mut Closure {
        let size = mem::size_of::<Closure>() + n as usize * 8;
        HEAP.allocate(size) as *mut Closure
    }

    pub fn cell_addr(&self, i: u16) -> *mut *mut u64 {
        let base = self as *const Closure as usize;
        let offset = mem::size_of::<Closure>() + i as usize * 8;
        (base + offset) as *mut *mut u64
    }

    pub unsafe fn cell(&self, i: u16) -> *mut u64 {
        *(self.cell_addr(i))
    }

    pub unsafe fn set_cell(&mut self, i: u16, cell: *mut u64) {
        *(self.cell_addr(i)) = cell;
        HEAP.write_barrier(self.cell_addr(i) as usize, cell as usize);
    }
}

pub struct Object {
    pub prototype: Ptr<Object>,
    pub properties: data::HashMap<data::String, data::SetValue<u64>>,
}

impl Object {
    pub fn property(&self, name: &data::String) -> Option<u64> {
        unsafe {
            let mut o = self;
            loop {
                let v = o.properties.get(name);
                if let Some(v) = v {
                    return Some(v.value);
                }
                match o.prototype.unwrap().as_ref() {
                    Some(p) => {
                        o = p;
                    }
                    None => {
                        return None;
                    }
                }
            }
        }
    }

    pub fn set_property(&mut self, name: &data::String, value: u64) {
        unsafe {
            let mut o = (self as *mut Object).as_mut().unwrap();
            let value = SetValue { value };
            loop {
                let v = o.properties.get_mut(name);
                if let Some(v) = v {
                    v.set(&value);
                    return;
                }
                match o.prototype.unwrap_mut().as_mut() {
                    Some(p) => {
                        o = p;
                    }
                    None => {
                        self.properties.insert(name, &value);
                        return;
                    }
                }
            }
        }
    }
}

#[derive(Debug)]
struct SerializationError {
    message: String,
}

impl Display for SerializationError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl Error for SerializationError {}
