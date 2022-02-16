use crate::data::{self, SetValue, Slice};
use crate::heap::{self, Handle, Ptr, Set, HEAP};
use crate::inst;
use crate::interpret::Interpreter;
use crate::nanbox::{NanBox, NanBoxKey};
use crate::pos::{Error, FunctionLineMap, PackageLineMap, Position};

use std::collections::HashMap;
use std::fmt::{self, Formatter};
use std::mem;

pub struct Package {
    pub name: String,
    pub globals: Vec<Global>,
    pub functions: Vec<Function>,
    pub strings: Handle<Slice<data::String>>,
    pub line_map: PackageLineMap,
    pub imports: Vec<ImportPackage>,
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

    pub value: u64,
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

    pub package: *mut Package,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "function {}() {{\n", self.name)?;
        inst::disassemble(&self.insts, f)?;
        f.write_str("}")
    }
}

pub struct ImportPackage {
    pub name: String,
    pub globals: Vec<ImportGlobal>,
    pub functions: Vec<ImportFunction>,
    pub link: *const Package,
}

impl ImportPackage {
    pub fn new(
        name: String,
        globals: Vec<ImportGlobal>,
        functions: Vec<ImportFunction>,
    ) -> ImportPackage {
        ImportPackage {
            name,
            globals,
            functions,
            link: 0 as *const Package,
        }
    }
}

pub struct ImportGlobal {
    pub name: String,
    pub link: *const Global,
}

impl ImportGlobal {
    pub fn new(name: String) -> ImportGlobal {
        ImportGlobal {
            name,
            link: 0 as *const Global,
        }
    }
}

pub struct ImportFunction {
    pub name: String,
    pub param_types: Vec<Type>,
    pub var_param_type: Option<Type>,
    pub link: *const Function,
}

impl ImportFunction {
    pub fn new(
        name: String,
        param_types: Vec<Type>,
        var_param_type: Option<Type>,
    ) -> ImportFunction {
        ImportFunction {
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

/// Finds, loads, links, and initializes packages.
///
/// PackageLoader maintains a graph of packages in memory. When a package that
/// hasn't been loaded is requested with load_package, PackageLoader queries
/// its given PackageSearcher. After recursively loading the package's
/// imports, PackageLoader links imported definitions to the actual definitions
/// in imported packages, then calls the package's initializer if it has one
/// using the provided interpreter.
pub struct PackageLoader {
    packages: HashMap<String, Box<Package>>,
    searcher: Box<dyn PackageSearcher>,
}

impl PackageLoader {
    pub fn new(searcher: Box<dyn PackageSearcher>) -> PackageLoader {
        PackageLoader {
            packages: HashMap::new(),
            searcher,
        }
    }

    pub unsafe fn load_package(
        &mut self,
        name: &str,
        interp: &mut Interpreter,
    ) -> Result<&Package, Error> {
        let mut search_stack = vec![String::from(name)];
        let mut link_stack = Vec::new();

        while let Some(name) = search_stack.pop() {
            if self.packages.contains_key(&name) {
                continue;
            }
            let package = self.searcher.search(&name)?;
            for imp in &package.imports {
                search_stack.push(imp.name.clone());
            }
            link_stack.push(package);
        }

        while let Some(mut package) = link_stack.pop() {
            self.link_package(&mut package);
            if let Some(init) = package.function_by_name("·init") {
                interp.interpret(init)?;
            }
            self.packages.insert(package.name.clone(), package);
        }

        Ok(self.packages.get(name).unwrap())
    }

    unsafe fn link_package(&mut self, package: &mut Package) {
        let pp = package as *mut Package;
        for f in &mut package.functions {
            f.package = pp;
        }
        for pi in &mut package.imports {
            let p = self.packages.get(&pi.name).unwrap();
            pi.link = &**p as *const Package;
            for gi in &mut pi.globals {
                let g = p.global_by_name(&gi.name).unwrap();
                gi.link = g as *const Global;
            }
            for fi in &mut pi.functions {
                let f = p.function_by_name(&fi.name).unwrap();
                fi.link = f as *const Function;
            }
        }
    }
}

/// Finds packages by name. This is dynamic, since it's likely to be highly
/// language-specific. For example, a language might have a list of directories
/// that could contain packages, specified with an environment variable.
pub trait PackageSearcher {
    fn search(&mut self, name: &str) -> Result<Box<Package>, Error>;
}

/// ProvidedPackageSearcher is a trivial implementation of PackageSearcher;
/// packages are added to it explicitly.
pub struct ProvidedPackageSearcher {
    packages: HashMap<String, Box<Package>>,
}

impl ProvidedPackageSearcher {
    pub fn new() -> ProvidedPackageSearcher {
        ProvidedPackageSearcher {
            packages: HashMap::new(),
        }
    }

    pub fn add(&mut self, package: Box<Package>) {
        let old = self.packages.insert(package.name.clone(), package);
        assert!(old.is_none());
    }
}

impl PackageSearcher for ProvidedPackageSearcher {
    fn search(&mut self, name: &str) -> Result<Box<Package>, Error> {
        match self.packages.remove(name) {
            Some(p) => Ok(p),
            None => Err(Error {
                position: Position::default(),
                message: format!("no such package: {}", name),
            }),
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
            if *ty == Type::NanBox {
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
    /// nanboxed values, except for array keys.
    pub properties: data::HashMap<NanBoxKey, Property>,

    /// A set of "own" properties belonging to this object. Keys are
    /// non-negative integers, less than i64::MAX.
    pub array_properties: data::HashMap<SetValue<i64>, Property>,

    /// If the object has no array properties, len is 0. Otherwise, len is the
    /// greatest array property key plus 1.
    pub len: i64,
}

impl Object {
    /// Looks up and returns a property, which may be in this object or the
    /// prototype chain.
    pub fn property(&self, key: NanBoxKey) -> Option<&Property> {
        unsafe {
            let mut o = self;
            loop {
                let prop = o.own_property(key);
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

    /// Looks up and returns a property stored in the object itself, not in
    /// its prototype chain.
    pub fn own_property(&self, key: NanBoxKey) -> Option<&Property> {
        if let Ok(i) = key.as_array_key() {
            self.own_array_property(i)
        } else {
            self.properties.get(&key)
        }
    }

    /// Looks up and returns an array property stored in the object itself, not
    /// in its prototype chain.
    pub fn own_array_property(&self, key: i64) -> Option<&Property> {
        self.array_properties.get(&SetValue { value: key })
    }

    /// Sets a property. If the property exists in this object or in the
    /// prototype chain, the existing property is written. Otherwise, a new
    /// property is added to this object.
    pub fn set_property(&mut self, key: NanBoxKey, kind: PropertyKind, value: NanBox) {
        unsafe {
            let mut o = (self as *mut Object).as_mut().unwrap();
            let prop = Property { kind, value };
            loop {
                let existing = if let Ok(i) = key.as_array_key() {
                    o.array_properties.get_mut(&SetValue { value: i })
                } else {
                    o.properties.get_mut(&key)
                };
                if let Some(existing) = existing {
                    existing.set(&prop);
                    return;
                }
                match o.prototype.unwrap_mut().as_mut() {
                    Some(p) => {
                        o = p;
                    }
                    None => {
                        self.set_own_property(key, kind, value);
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
        if let Ok(i) = key.as_array_key() {
            let ikey = SetValue { value: i };
            if let Some(existing) = self.array_properties.get_mut(&ikey) {
                existing.set(&prop);
            } else {
                self.array_properties.insert(&ikey, &prop);
                if i >= self.len {
                    self.len = i + 1;
                }
            }
        } else {
            if let Some(existing) = self.properties.get_mut(&key) {
                existing.set(&prop);
            } else {
                self.properties.insert(&key, &prop);
            }
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
