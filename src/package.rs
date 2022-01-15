use crate::data::{self, Slice};
use crate::heap::{self, Handle, Ptr, Set, HEAP};
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
        for (i, ty) in self.types.iter().enumerate() {
            write!(f, "{}type {} {}", sep, i, ty)?;
            sep = "\n";
        }
        sep = "\n\n";
        for (i, s) in self.strings.iter().enumerate() {
            write!(f, "{}string {} \"{}\"", sep, i, s)?;
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

/// A Closure is a callable object that consists of a function, a number of
/// captured variables from its declaring environment, and a number of
/// bound arguments.
pub struct Closure {
    pub function: Ptr<Function>,
    pub capture_count: u16,
    pub bound_arg_count: u16,
}

impl Closure {
    pub fn alloc(capture_count: u16, bound_arg_count: u16) -> *mut Closure {
        unsafe {
            let cell_count = capture_count as usize + bound_arg_count as usize;
            let size = mem::size_of::<Closure>() + cell_count * 8;
            let raw = HEAP.allocate(size) as *mut Closure;
            let c = raw.as_mut().unwrap();
            c.capture_count = capture_count;
            c.bound_arg_count = bound_arg_count;
            raw
        }
    }

    pub fn cell_addr(&self, i: u32) -> usize {
        let base = self as *const Closure as usize;
        let cell_base_offset =
            (mem::size_of::<Closure>() + heap::ALLOC_ALIGNMENT - 1) & !(heap::ALLOC_ALIGNMENT - 1);
        base + cell_base_offset + i as usize * 8
    }

    pub fn capture(&self, i: u16) -> *mut u64 {
        unsafe {
            assert!(i < self.capture_count);
            let addr = self.cell_addr(i as u32) as *mut *mut u64;
            *addr
        }
    }

    pub fn set_capture(&mut self, i: u16, cell: *mut u64) {
        unsafe {
            assert!(i < self.capture_count);
            let addr = self.cell_addr(i as u32) as *mut *mut u64;
            *addr = cell;
            HEAP.write_barrier(addr as usize, cell as usize);
        }
    }

    pub fn bound_arg(&self, i: u16) -> u64 {
        unsafe {
            assert!(i < self.bound_arg_count);
            let addr = self.cell_addr(self.capture_count as u32 + i as u32) as *mut u64;
            *addr
        }
    }

    pub fn set_bound_arg(&mut self, i: u16, arg: u64) {
        unsafe {
            assert!(i < self.bound_arg_count);
            let addr = self.cell_addr(self.capture_count as u32 + i as u32) as *mut u64;
            *addr = arg;
            let ty = &self.function.unwrap_ref().param_types[i as usize];
            if *ty == Type::Nanbox {
                HEAP.write_barrier_nanbox(addr as usize, arg);
            } else if ty.is_pointer() {
                HEAP.write_barrier(addr as usize, arg as usize);
            }
        }
    }
}

pub struct Object {
    pub prototype: Ptr<Object>,
    pub properties: data::HashMap<data::String, Property>,
}

impl Object {
    pub fn property(&self, name: &data::String) -> Option<&Property> {
        unsafe {
            let mut o = self;
            loop {
                let prop = o.properties.get(name);
                if prop.is_some() {
                    return prop;
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

    pub fn set_property(&mut self, name: &data::String, kind: PropertyKind, value: u64) {
        unsafe {
            let mut o = (self as *mut Object).as_mut().unwrap();
            let prop = Property { kind, value };
            loop {
                let existing = o.properties.get_mut(name);
                if let Some(existing) = existing {
                    existing.set(&prop);
                    return;
                }
                match o.prototype.unwrap_mut().as_mut() {
                    Some(p) => {
                        o = p;
                    }
                    None => {
                        self.properties.insert(name, &prop);
                        return;
                    }
                }
            }
        }
    }

    pub fn set_own_property(&mut self, name: &data::String, kind: PropertyKind, value: u64) {
        let prop = Property { kind, value };
        if let Some(existing) = self.properties.get_mut(name) {
            existing.set(&prop);
        } else {
            self.properties.insert(name, &prop);
        }
    }
}

pub struct Property {
    pub kind: PropertyKind,
    pub value: u64,
}

impl Property {
    pub fn init(&mut self, kind: PropertyKind, value: u64) {
        self.kind = kind;
        self.value = value;
        HEAP.write_barrier_nanbox(&self.value as *const u64 as usize, value);
    }
}

impl Set for Property {
    fn set(&mut self, other: &Property) {
        self.init(other.kind, other.value);
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum PropertyKind {
    Field,
    Method,
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
