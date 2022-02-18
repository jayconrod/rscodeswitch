use crate::inst::{self, Assembler, Label};
use crate::package::{Function, Global, Package, Type};
use crate::pos::PackageLineMap;
use crate::runtime::Object;

use std::collections::HashMap;
use std::mem;

pub fn build_std_package() -> Package {
    let mut b = Builder::new();

    // assert(v, message)
    {
        let mut ok_label = Label::new();
        let mut panic_label = Label::new();
        b.asm.loadarg(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.bif(&mut ok_label);
        b.asm.loadarg(1);
        b.asm.dup();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.mode(inst::MODE_LUA);
        b.asm.ne();
        b.asm.mode(inst::MODE_LUA);
        b.asm.bif(&mut panic_label);
        b.asm.pop();
        let si = b.ensure_string("assertion failed!");
        b.asm.string(si);
        b.asm.mode(inst::MODE_STRING);
        b.asm.nanbox();
        b.asm.bind(&mut panic_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.panic(1);
        b.asm.bind(&mut ok_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("assert", 2, false);
    }

    // collectgarbage(opt, arg)
    // TODO: implement garbage collection.
    b.asm.mode(inst::MODE_LUA);
    b.asm.setv(0);
    b.asm.mode(inst::MODE_LUA);
    b.asm.retv();
    b.finish_function("collectgarbage", 2, false);

    // dofile
    // TODO: implement. This needs to hook into native code.
    {
        let si = b.ensure_string("unimplemented");
        b.asm.string(si);
        b.asm.mode(inst::MODE_STRING);
        b.asm.panic(0);
        b.finish_function("dofile", 1, false);
    }

    // error(message, level)
    {
        let mut panic_label = Label::new();
        b.asm.loadarg(0);
        b.asm.loadarg(1);
        b.asm.dup();
        b.asm.mode(inst::MODE_LUA);
        b.asm.bif(&mut panic_label);
        b.asm.pop();
        b.asm.const_(1);
        b.asm.nanbox();
        b.asm.bind(&mut panic_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.paniclevel();
        b.finish_function("error", 2, false);
    }

    // TODO: getmetatable
    // TODO: ipairs
    // TODO: load
    // TODO: loadfile
    // TODO: next
    // TODO: pairs
    // TODO: pcall

    // print
    b.asm.mode(inst::MODE_LUA);
    b.asm.loadvarargs();
    b.asm.mode(inst::MODE_LUA);
    b.asm.sys(inst::SYS_PRINT);
    b.asm.mode(inst::MODE_LUA);
    b.asm.setv(0);
    b.asm.mode(inst::MODE_LUA);
    b.asm.retv();
    b.finish_function("print", 0, true);

    // TODO: rawequal
    // TODO: rawget
    // TODO: rawlen
    // TODO: rawset
    // TODO: select
    // TODO: setmetatable
    // TODO: tonumber
    // TODO: tostring
    // TODO: type
    // TODO: _VERSION
    // TODO: warn
    // TODO: xpcall

    // TODO: coroutine

    // TODO: require
    // TODO: package

    // TODO: string

    // TODO: utf8

    // TODO: table

    // TODO: math

    // TODO: io

    // TODO: os

    // TODO: debug

    // init - allocates and populates the _ENV table.
    let env_index = b.add_global("_ENV");
    let g_index = b.add_global("_G");
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
    b.asm.dup();
    b.asm.storeglobal(env_index);
    b.asm.storeglobal(g_index);
    b.asm.mode(inst::MODE_LUA);
    b.asm.setv(0);
    b.asm.mode(inst::MODE_LUA);
    b.asm.retv();
    b.finish_function("·init", 0, false);

    b.build()
}

struct Builder {
    string_index: HashMap<&'static str, u32>,
    asm: Assembler,
    package: Package,
    function_name_index: Vec<u32>,
}

impl Builder {
    fn new() -> Builder {
        Builder {
            string_index: HashMap::new(),
            asm: Assembler::new(),
            package: Package {
                name: String::from("luastd"),
                globals: Vec::new(),
                functions: Vec::new(),
                strings: Vec::new(),
                line_map: PackageLineMap { files: Vec::new() },
                imports: Vec::new(),
            },
            function_name_index: Vec::new(),
        }
    }

    fn build(self) -> Package {
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
        });
        i
    }

    fn ensure_string(&mut self, s: &'static str) -> u32 {
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
}
