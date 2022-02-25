use crate::inst::{self, Assembler, Label};
use crate::nanbox;
use crate::package::{Function, Global, Package, Type};
use crate::pos::PackageLineMap;
use crate::runtime::Object;

use std::collections::HashMap;
use std::mem;

pub fn build_std_package() -> Package {
    let mut b = Builder::new();
    let env_index = b.add_global("_ENV");
    let g_index = b.add_global("_G");
    let ipairs_iter_index = b.add_global("ipairs_iter");
    let next_index = b.add_global("pairs");

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
    {
        b.asm.loadarg(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.sys(inst::SYS_DOFILE);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
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

    // getmetatable(table)
    {
        // Check that the argument is a table.
        // Return nil for anything that's not a table.
        b.asm.loadarg(0);
        b.asm.dup();
        b.asm.mode(inst::MODE_LUA);
        b.asm.typeof_();
        b.asm.const_(nanbox::TAG_OBJECT);
        b.asm.eq();
        let mut is_table_label = Label::new();
        b.asm.bif(&mut is_table_label);
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();

        // Load the prototype.
        // If it's non-nil, check if it has a non-nil "__metatable" field.
        // Return that if it exists.
        b.asm.bind(&mut is_table_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadprototype();
        b.asm.dup();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.eq();
        let mut return_label = Label::new();
        b.asm.bif(&mut return_label);
        b.asm.dup();
        let si = b.ensure_string("__metatable");
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadnamedpropornil(si);
        b.asm.dup();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.ne();
        b.asm.bif(&mut return_label);
        b.asm.pop();
        b.asm.bind(&mut return_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("getmetatable", 1, false);
    }

    // ipairs(table)
    let ipairs_iter_func_index: u32;
    {
        // ipairs_iter(table, index): the iterator function that ipairs returns.
        // Returns index + 1, table[index + 1] if the property is non-nil.
        // Otherwise, returns nil.
        b.asm.loadarg(1);
        b.asm.const_(1);
        b.asm.nanbox();
        b.asm.mode(inst::MODE_LUA);
        b.asm.add();
        b.asm.loadarg(0);
        b.asm.loadlocal(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadindexpropornil();
        b.asm.dup();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.eq();
        let mut end_label = Label::new();
        b.asm.bif(&mut end_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(2);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.asm.bind(&mut end_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        ipairs_iter_func_index = b.finish_function("ipairs_iter", 2, false);

        // ipairs(table): returns ipairs_iter, table, 0, nil
        b.asm.loadglobal(ipairs_iter_index);
        b.asm.loadarg(0);
        b.asm.constzero();
        b.asm.nanbox();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(4);
        b.asm.nop(); // DEBUG
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("ipairs", 1, false);
    }

    // load(chunk, chunkname, mode, env)
    {
        b.asm.loadarg(0);
        b.asm.loadarg(1);
        b.asm.loadarg(2);
        b.asm.loadarg(3);
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(4);
        b.asm.mode(inst::MODE_LUA);
        b.asm.sys(inst::SYS_LOAD);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("load", 4, false);
    }

    // loadfile(filename, mode, env)
    {
        b.asm.loadarg(0);
        b.asm.loadarg(1);
        b.asm.loadarg(2);
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(3);
        b.asm.mode(inst::MODE_LUA);
        b.asm.sys(inst::SYS_LOADFILE);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("loadfile", 3, false);
    }

    // next(table, index)
    {
        b.asm.loadarg(0);
        b.asm.loadarg(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadnextindexpropornil();
        b.asm.loadlocal(0);
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.eq();
        let mut last_label = Label::new();
        b.asm.bif(&mut last_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(2);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.asm.bind(&mut last_label);
        b.asm.pop();
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("next", 2, false);
    }

    // pairs(table)
    {
        // If table has a metamethod __pairs, call that and return results.
        b.asm.loadarg(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadprototype();
        b.asm.dup();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.eq();
        let mut not_meta_label = Label::new();
        b.asm.bif(&mut not_meta_label);
        let si = b.ensure_string("__pairs");
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadnamedpropornil(si);
        b.asm.dup();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.eq();
        b.asm.bif(&mut not_meta_label);
        b.asm.loadarg(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.callvalue(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.adjustv(3);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();

        // Otherwise, return next, table, nil.
        b.asm.bind(&mut not_meta_label);
        b.asm.pop();
        b.asm.loadglobal(next_index);
        b.asm.loadarg(0);
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(3);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();

        b.finish_function("pairs", 1, false);
    }

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

    // setmetatable(table, metatable)
    {
        // The first argument must be a table. Load its previous metatable
        // and check that it isn't protected with a non-nil __metatable
        // property.
        b.asm.loadarg(0);
        b.asm.dup();
        b.asm.mode(inst::MODE_LUA);
        b.asm.typeof_();
        b.asm.const_(nanbox::TAG_OBJECT);
        b.asm.eq();
        let mut table_is_table_label = Label::new();
        b.asm.bif(&mut table_is_table_label);
        let si = b.ensure_string("first argument must be table");
        b.asm.string(si);
        b.asm.panic(0);
        b.asm.bind(&mut table_is_table_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadprototype();
        b.asm.dup();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.eq();
        let mut check_metatable_label = Label::new();
        b.asm.bif(&mut check_metatable_label);
        b.asm.dup();
        let si = b.ensure_string("__metatable");
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadnamedpropornil(si);
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.eq();
        b.asm.bif(&mut check_metatable_label);
        let si = b.ensure_string("cannot change a protected metatable");
        b.asm.string(si);
        b.asm.panic(0);

        // The second argument must be a table or nil.
        // stack: oldtable
        b.asm.bind(&mut check_metatable_label);
        b.asm.loadarg(1);
        b.asm.dup();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.eq();
        let mut store_metatable_label = Label::new();
        b.asm.bif(&mut store_metatable_label);
        b.asm.dup();
        b.asm.mode(inst::MODE_LUA);
        b.asm.typeof_();
        b.asm.const_(nanbox::TAG_OBJECT);
        b.asm.eq();
        b.asm.bif(&mut store_metatable_label);
        let si = b.ensure_string("metatable must be table or nil");
        b.asm.string(si);
        b.asm.panic(0);

        // Store the metatable into the table, then return the old one.
        // stack: oldtable newtable
        b.asm.bind(&mut store_metatable_label);
        b.asm.loadarg(0);
        b.asm.swap();
        b.asm.mode(inst::MODE_LUA);
        b.asm.storeprototype();
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("setmetatable", 2, false);
    }

    // tonumber
    {
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadvarargs();
        b.asm.mode(inst::MODE_LUA);
        b.asm.sys(inst::SYS_TONUMBER);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("tonumber", 0, true);
    }

    // tostring
    {
        b.asm.loadarg(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.setv(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.sys(inst::SYS_TOSTRING);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("tostring", 1, false);
    }

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
    b.asm.alloc(mem::size_of::<Object>() as u32);
    b.asm.mode(inst::MODE_OBJECT);
    b.asm.nanbox();
    for i in 0..b.package.functions.len() {
        if b.package.functions[i].name == "ipairs_iter" {
            continue;
        }
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
    b.asm.newclosure(ipairs_iter_func_index, 0, 0);
    b.asm.mode(inst::MODE_CLOSURE);
    b.asm.nanbox();
    b.asm.storeglobal(ipairs_iter_index);
    b.asm.loadglobal(env_index);
    let next_si = b.ensure_string("next");
    b.asm.mode(inst::MODE_LUA);
    b.asm.loadnamedprop(next_si);
    b.asm.storeglobal(next_index);
    b.asm.mode(inst::MODE_LUA);
    b.asm.setv(0);
    b.asm.mode(inst::MODE_LUA);
    b.asm.retv();
    b.finish_function("", 0, false);

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
                init_index: None,
                strings: Vec::new(),
                line_map: PackageLineMap { files: Vec::new() },
                imports: Vec::new(),
            },
            function_name_index: Vec::new(),
        }
    }

    fn build(mut self) -> Package {
        let init_index = (self.package.functions.len() - 1) as u32;
        self.package.init_index = Some(init_index);
        self.package
    }

    fn finish_function(
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
        let fi: u32 = self.package.functions.len().try_into().unwrap();
        self.package.functions.push(Function {
            name: String::from(name),
            insts,
            param_types: vec![Type::NanBox; param_count],
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
