use crate::data::{self, Slice};
use crate::heap::{self, Handle, Ptr, Set, HEAP};
use crate::inst;
use crate::nanbox::{NanBox, NanBoxKey};
use crate::pos::{FunctionLineMap, PackageLineMap};

use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::mem;

pub struct Package {
    pub globals: Vec<Global>,
    pub functions: Vec<Function>,
    pub strings: Handle<Slice<data::String>>,
    pub line_map: PackageLineMap,
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
    pub line_map: FunctionLineMap,
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
    Int64,
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
            Type::Int64 => 8,
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
                    Type::Int64 => "i64",
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
/// bound arguments. If the closure is to be used as a constructor, it may
/// contain a prototype object to be used by new instances.
pub struct Closure {
    pub function: Ptr<Function>,
    pub prototype: Ptr<Object>,
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

/// A run-time value that stores a prototype (a parent object) and a list of
/// "own" properties.
pub struct Object {
    /// An optional parent object. In JavaScript, this is the object's
    /// prototype, unique to each constructor. In Lua, this is the metatable.
    /// Prototypes provide a form of inheritance.
    pub prototype: Ptr<Object>,

    /// A set of "own" properties belonging to this object. Keys are arbitrary
    /// nanboxed values.
    pub properties: data::HashMap<NanBoxKey, Property>,
}

impl Object {
    /// Looks up and returns a property, which may be in this object or the
    /// prototype chain.
    pub fn property(&self, key: NanBoxKey) -> Option<&Property> {
        unsafe {
            let mut o = self;
            loop {
                let prop = o.properties.get(&key);
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

    /// Sets a property. If the property exists in this object or in the
    /// prototype chain, the existing property is written. Otherwise, a new
    /// property is added to this object.
    pub fn set_property(&mut self, key: NanBoxKey, kind: PropertyKind, value: NanBox) {
        unsafe {
            let mut o = (self as *mut Object).as_mut().unwrap();
            let prop = Property { kind, value };
            loop {
                let existing = o.properties.get_mut(&key);
                if let Some(existing) = existing {
                    existing.set(&prop);
                    return;
                }
                match o.prototype.unwrap_mut().as_mut() {
                    Some(p) => {
                        o = p;
                    }
                    None => {
                        self.properties.insert(&key, &prop);
                        return;
                    }
                }
            }
        }
    }

    /// Sets a property in this object. If the property exists in this object,
    /// the existing property is written. Otherwise, a new property is added
    /// to this object, even if a property of the same name exists in the
    /// prototype chain.
    pub fn set_own_property(&mut self, key: NanBoxKey, kind: PropertyKind, value: NanBox) {
        let prop = Property { kind, value };
        if let Some(existing) = self.properties.get_mut(&key) {
            existing.set(&prop);
        } else {
            self.properties.insert(&key, &prop);
        }
    }

    /// Loads the value of a property. For methods, this allocates a
    /// bound method closure.
    pub unsafe fn property_value(&self, prop: &Property) -> NanBox {
        match prop.kind {
            PropertyKind::Field => prop.value,
            PropertyKind::Method => {
                let method: &Closure = prop.value.try_into().unwrap();
                let raw = Closure::alloc(method.capture_count, method.bound_arg_count + 1);
                let bm = raw.as_mut().unwrap();
                bm.function.set(&method.function);
                for i in 0..method.capture_count {
                    bm.set_capture(i, method.capture(i));
                }
                for i in 0..method.bound_arg_count {
                    bm.set_bound_arg(i, method.bound_arg(i));
                }
                let r = NanBox::from(self);
                bm.set_bound_arg(method.bound_arg_count, r.0);
                NanBox::from(bm)
            }
        }
    }
}

/// A value held by an object.
pub struct Property {
    pub kind: PropertyKind,
    pub value: NanBox,
}

impl Property {
    pub fn init(&mut self, kind: PropertyKind, value: NanBox) {
        self.kind = kind;
        self.value.set(&value);
    }
}

impl Set for Property {
    fn set(&mut self, other: &Property) {
        self.init(other.kind, other.value);
    }
}

/// Describes what kind of value is stored in a property.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum PropertyKind {
    /// A regular value. Nothing special.
    Field,

    /// A function which accepts the object that holds it as a receiver.
    /// When a method is loaded without being called, the interpreter
    /// allocates a "bound method" closure that captures the receiver.
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
