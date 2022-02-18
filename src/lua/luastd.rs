use crate::inst::{self, Assembler, Label};
use crate::nanbox;
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

    // type
    {
        b.asm.loadarg(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.typeof_();
        b.asm.dup();
        b.asm.constzero();
        b.asm.ne();
        let mut not_nil_label = Label::new();
        b.asm.bif(&mut not_nil_label);
        let nil_si = b.ensure_string("nil");
        b.asm.string(nil_si);
        let mut box_label = Label::new();
        b.asm.b(&mut box_label);
        b.asm.bind(&mut not_nil_label);
        b.asm.dup();
        b.asm.const_(nanbox::TAG_BOOL);
        b.asm.ne();
        let mut not_bool_label = Label::new();
        b.asm.bif(&mut not_bool_label);
        let bool_si = b.ensure_string("boolean");
        b.asm.string(bool_si);
        b.asm.b(&mut box_label);
        b.asm.bind(&mut not_bool_label);
        b.asm.dup();
        b.asm.const_(nanbox::TAG_SMALL_INT);
        b.asm.eq();
        let mut number_label = Label::new();
        b.asm.bif(&mut number_label);
        b.asm.dup();
        b.asm.const_(nanbox::TAG_BIG_INT);
        b.asm.eq();
        b.asm.bif(&mut number_label);
        b.asm.dup();
        b.asm.const_(nanbox::TAG_FLOAT);
        b.asm.ne();
        let mut not_number_label = Label::new();
        b.asm.bif(&mut not_number_label);
        b.asm.bind(&mut number_label);
        let number_si = b.ensure_string("number");
        b.asm.string(number_si);
        b.asm.b(&mut box_label);
        b.asm.bind(&mut not_number_label);
        b.asm.dup();
        b.asm.const_(nanbox::TAG_STRING);
        b.asm.ne();
        let mut not_string_label = Label::new();
        b.asm.bif(&mut not_string_label);
        let string_si = b.ensure_string("string");
        b.asm.string(string_si);
        b.asm.b(&mut box_label);
        b.asm.bind(&mut not_string_label);
        b.asm.dup();
        b.asm.const_(nanbox::TAG_CLOSURE);
        b.asm.ne();
        let mut not_function_label = Label::new();
        b.asm.bif(&mut not_function_label);
        let function_si = b.ensure_string("function");
        b.asm.string(function_si);
        b.asm.b(&mut box_label);
        b.asm.bind(&mut not_function_label);
        b.asm.dup();
        b.asm.const_(nanbox::TAG_OBJECT);
        b.asm.ne();
        let mut not_table_label = Label::new();
        b.asm.bif(&mut not_table_label);
        let table_si = b.ensure_string("table");
        b.asm.string(table_si);
        b.asm.b(&mut box_label);
        b.asm.bind(&mut not_table_label);
        // TODO: userdata, thread
        let unknown_si = b.ensure_string("unknown");
        b.asm.string(unknown_si);
        b.asm.bind(&mut box_label);
        b.asm.mode(inst::MODE_STRING);
        b.asm.nanbox();
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("type", 1, false);
    }

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
