use crate::data::{self, SetValue, Slice};
use crate::heap::{self, Handle, Ptr, Set, HEAP};
use crate::interpret::Interpreter;
use crate::nanbox::{NanBox, NanBoxKey};
use crate::package::{self, Type};
use crate::pos::{Error, FunctionLineMap, PackageLineMap, Position};

use std::collections::HashMap;
use std::mem;

pub struct Package {
    pub name: String,
    pub globals: Vec<Global>,
    global_index: HashMap<String, usize>,
    pub functions: Vec<Function>,
    function_index: HashMap<String, usize>,
    pub strings: Handle<Slice<data::String>>,
    pub line_map: PackageLineMap,
    pub imports: Vec<PackageImport>,
}

impl Package {
    pub fn global_by_name(&mut self, name: &str) -> Option<&mut Global> {
        self.global_index.get(name).map(|&i| &mut self.globals[i])
    }

    pub fn function_by_name(&self, name: &str) -> Option<&Function> {
        self.function_index.get(name).map(|&i| &self.functions[i])
    }
}

pub struct Global {
    pub value: u64,
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

pub struct PackageImport {
    pub globals: Vec<*mut Global>,
    pub functions: Vec<*const Function>,
}

pub struct GlobalImport {
    pub link: *mut Global,
}

pub struct FunctionImport {
    pub link: *const Function,
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
    ) -> Result<&mut Package, Error> {
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

        while let Some(package) = link_stack.pop() {
            let name = package.name.clone();
            let linked_package = self.link_package(package);
            if let Some(init) = linked_package.function_by_name("·init") {
                interp.interpret(init)?;
            }
            self.packages.insert(name, linked_package);
        }

        Ok(self.packages.get_mut(name).unwrap())
    }

    unsafe fn link_package(&mut self, package: package::Package) -> Box<Package> {
        let mut globals = Vec::new();
        globals.resize_with(package.globals.len(), || Global { value: 0 });
        let global_index = HashMap::from_iter(
            package
                .globals
                .iter()
                .enumerate()
                .map(|(i, g)| (g.name.clone(), i)),
        );
        let functions: Vec<Function> = package
            .functions
            .into_iter()
            .map(|f| Function {
                name: f.name,
                insts: f.insts,
                param_types: f.param_types,
                cell_types: f.cell_types,
                var_param_type: f.var_param_type,
                line_map: f.line_map,
                package: 0 as *mut Package,
            })
            .collect();
        let function_index = HashMap::from_iter(
            functions
                .iter()
                .enumerate()
                .map(|(i, f)| (f.name.clone(), i)),
        );
        let mut strings = Handle::new(Slice::<data::String>::alloc_with_array(
            package.strings.len(),
        ));
        for (i, s) in package.strings.iter().enumerate() {
            strings[i].set_from_bytes(s);
        }
        let imports = package
            .imports
            .into_iter()
            .map(|pi| {
                let p = &mut *self.packages.get_mut(&pi.name).unwrap();
                let globals = pi
                    .globals
                    .into_iter()
                    .map(|gi| p.global_by_name(&gi.name).unwrap() as *mut Global)
                    .collect();
                let functions = pi
                    .functions
                    .into_iter()
                    .map(|fi| p.function_by_name(&fi.name).unwrap() as *const Function)
                    .collect();
                PackageImport { globals, functions }
            })
            .collect();
        let mut linked_package = Box::new(Package {
            name: package.name,
            globals,
            global_index,
            functions,
            function_index,
            strings,
            line_map: package.line_map,
            imports,
        });
        let pp = &mut *linked_package as *mut Package;
        for f in &mut linked_package.functions {
            f.package = pp;
        }
        linked_package
    }
}

/// Finds packages by name. This is dynamic, since it's likely to be highly
/// language-specific. For example, a language might have a list of directories
/// that could contain packages, specified with an environment variable.
pub trait PackageSearcher {
    fn search(&mut self, name: &str) -> Result<package::Package, Error>;
}

/// ProvidedPackageSearcher is a trivial implementation of PackageSearcher;
/// packages are added to it explicitly.
pub struct ProvidedPackageSearcher {
    packages: HashMap<String, package::Package>,
}

impl ProvidedPackageSearcher {
    pub fn new() -> ProvidedPackageSearcher {
        ProvidedPackageSearcher {
            packages: HashMap::new(),
        }
    }

    pub fn add(&mut self, package: package::Package) {
        let old = self.packages.insert(package.name.clone(), package);
        assert!(old.is_none());
    }
}

impl PackageSearcher for ProvidedPackageSearcher {
    fn search(&mut self, name: &str) -> Result<package::Package, Error> {
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
