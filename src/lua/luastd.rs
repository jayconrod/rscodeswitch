use crate::data::{self, List, Slice};
use crate::heap::Handle;
use crate::inst::{self, Assembler};
use crate::package::{Function, Global, Object, Package, Type};
use crate::pos::PackageLineMap;

use std::collections::HashMap;
use std::mem;

pub fn build_std_package() -> Box<Package> {
    let mut b = Builder::new();

    // print
    b.asm.mode(inst::MODE_LUA);
    b.asm.loadvarargs();
    b.asm.mode(inst::MODE_LUA);
    b.asm.sys(inst::SYS_PRINT);
    b.asm.mode(inst::MODE_LUA);
    b.asm.setv(0);
    b.asm.retv();
    b.finish_function("print", 0, true);

    // init - allocates and populates the _ENV table.
    let gi = b.add_global("_ENV");
    b.asm.alloc(mem::size_of::<Object>() as u32);
    b.asm.mode(inst::MODE_OBJECT);
    b.asm.nanbox();
    for i in 0..b.package.functions.len() {
        b.asm.dup();
        b.asm.newclosure(i as u32, 0, 0);
        b.asm.mode(inst::MODE_CLOSURE);
        b.asm.nanbox();
        b.asm.mode(inst::MODE_LUA);
        b.asm.storenamedprop(b.function_name_index[i]);
    }
    b.asm.storeglobal(gi);
    b.asm.mode(inst::MODE_LUA);
    b.asm.setv(0);
    b.asm.mode(inst::MODE_LUA);
    b.asm.retv();
    b.finish_function("·init", 0, false);

    b.build()
}

struct Builder {
    strings: Handle<List<data::String>>,
    string_index: HashMap<&'static str, u32>,
    asm: Assembler,
    package: Box<Package>,
    function_name_index: Vec<u32>,
}

impl Builder {
    fn new() -> Builder {
        Builder {
            strings: Handle::new(List::alloc()),
            string_index: HashMap::new(),
            asm: Assembler::new(),
            package: Box::new(Package {
                name: String::from("luastd"),
                globals: Vec::new(),
                functions: Vec::new(),
                strings: Handle::new(Slice::alloc()),
                line_map: PackageLineMap { files: Vec::new() },
                imports: Vec::new(),
            }),
            function_name_index: Vec::new(),
        }
    }

    fn build(mut self) -> Box<Package> {
        self.package.strings = Handle::new(Slice::alloc());
        self.package.strings.init_from_list(&*self.strings);
        self.package
    }

    fn finish_function(&mut self, name: &'static str, param_count: usize, is_variadic: bool) {
        let mut asm = Assembler::new();
        mem::swap(&mut self.asm, &mut asm);
        let (insts, flmap) = asm.finish().unwrap();
        let var_param_type = if is_variadic {
            Some(Type::NanBox)
        } else {
            None
        };
        self.package.functions.push(Function {
            name: String::from(name),
            insts,
            package: 0 as *mut Package,
            param_types: vec![Type::NanBox; param_count],
            var_param_type,
            cell_types: Vec::new(),
            line_map: flmap,
        });
        let si = self.ensure_string(name);
        self.function_name_index.push(si);
    }

    fn add_global(&mut self, s: &'static str) -> u32 {
        let i = self.package.globals.len() as u32;
        self.package.globals.push(Global {
            name: String::from(s),
            value: 0,
        });
        i
    }

    fn ensure_string(&mut self, s: &'static str) -> u32 {
        if let Some(&i) = self.string_index.get(s) {
            i
        } else {
            let i = self.strings.len().try_into().unwrap();
            let sh = Handle::new(data::String::from_bytes(s.as_bytes()));
            self.strings.push(&*sh);
            self.string_index.insert(s, i);
            i
        }
    }
}
