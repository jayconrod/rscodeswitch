use codeswitch::inst::{self, Label};
use codeswitch::nanbox;
use codeswitch::package::{Builder, Package, Type};

pub fn build_std_package() -> Package {
    let mut b = Builder::new(String::from("luastd"));
    let env_index = b.add_global("_ENV", Type::NanBox);
    let g_index = b.add_global("_G", Type::NanBox);
    let ipairs_iter_index = b.add_global("ipairs_iter", Type::NanBox);
    let next_index = b.add_global("pairs", Type::NanBox);

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
        b.asm.ne();
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
        b.asm.setvi(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("assert", 2, false);
    }

    // collectgarbage(opt, arg)
    // TODO: implement garbage collection.
    b.asm.setvi(0);
    b.asm.mode(inst::MODE_LUA);
    b.asm.retv();
    b.finish_function("collectgarbage", 2, false);

    // dofile
    {
        b.asm.loadarg(0);
        b.asm.setvi(1);
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
        b.asm.setvi(1);
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
        b.asm.setvi(1);
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
        b.asm.setvi(2);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.asm.bind(&mut end_label);
        b.asm.setvi(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        ipairs_iter_func_index = b.finish_function("_ipairs_iter", 2, false);

        // ipairs(table): returns ipairs_iter, table, 0, nil
        b.asm.loadglobal(ipairs_iter_index);
        b.asm.loadarg(0);
        b.asm.constzero();
        b.asm.nanbox();
        b.asm.constzero();
        b.asm.mode(inst::MODE_PTR);
        b.asm.nanbox();
        b.asm.setvi(4);
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
        b.asm.setvi(4);
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
        b.asm.setvi(3);
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
        b.asm.setvi(2);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.asm.bind(&mut last_label);
        b.asm.pop();
        b.asm.setvi(1);
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
        b.asm.setvi(3);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();

        b.finish_function("pairs", 1, false);
    }

    // pcall(f, ...)
    {
        // Reserve two stack slots to be written by the error handler.
        b.asm.constzero();
        b.asm.mode(inst::MODE_BOOL);
        b.asm.nanbox();
        b.asm.dup();

        // Push the error handler. This uses 2 more slots.
        let mut handler_label = Label::new();
        b.asm.pushhandler(&mut handler_label);

        // Call the function.
        b.asm.loadarg(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadvarargs();
        b.asm.mode(inst::MODE_LUA);
        b.asm.callvaluev();

        // Function returned normally. Pop the handler. This does not release
        // those stack slots. We'll overwrite slot 3 with true and return that
        // with the other returned values.
        b.asm.pophandler();
        b.asm.const_(1);
        b.asm.mode(inst::MODE_BOOL);
        b.asm.nanbox();
        b.asm.storelocal(3);
        b.asm.mode(inst::MODE_LUA);
        b.asm.appendv(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();

        // An error was raised, and we've reached the error handler in a new
        // frame immediately below pcall. Store the error in pcall's frame.
        b.asm.bind(&mut handler_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.geterror();
        b.asm.storelocalparent(1);

        // Return from the error handler. sp will be the same as before
        // pushhandler. The local slots contain (false, error).
        b.asm.stoperror();
        b.asm.setvi(2);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("pcall", 1, true);
    }

    // print
    b.asm.mode(inst::MODE_LUA);
    b.asm.loadvarargs();
    b.asm.mode(inst::MODE_LUA);
    b.asm.sys(inst::SYS_PRINT);
    b.asm.setvi(0);
    b.asm.mode(inst::MODE_LUA);
    b.asm.retv();
    b.finish_function("print", 0, true);

    // rawequal
    {
        b.asm.loadarg(0);
        b.asm.loadarg(1);
        b.asm.mode(inst::MODE_BOX);
        b.asm.eq();
        b.asm.setvi(1);
        b.asm.ret();
        b.finish_function("rawequal", 2, false);
    }

    // rawget
    {
        b.asm.loadarg(0);
        b.asm.loadarg(1);
        b.asm.mode(inst::MODE_BOX);
        b.asm.loadindexpropornil();
        b.asm.setvi(1);
        b.asm.ret();
        b.finish_function("rawget", 2, false);
    }

    // rawlen
    {
        b.asm.loadarg(0);
        b.asm.mode(inst::MODE_BOX);
        b.asm.len();
        b.asm.setvi(1);
        b.asm.ret();
        b.finish_function("rawlen", 1, false);
    }

    // rawset
    {
        b.asm.loadarg(0);
        b.asm.loadarg(1);
        b.asm.loadarg(2);
        b.asm.mode(inst::MODE_BOX);
        b.asm.storeindexprop();
        b.asm.setvi(0);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("rawset", 3, false);
    }

    // select(index, ...)
    {
        // Decide what to do based on the type of index.
        b.asm.loadarg(0);
        b.asm.dup();
        b.asm.mode(inst::MODE_LUA);
        b.asm.typeof_();
        b.asm.dup();
        b.asm.const_(nanbox::TAG_SMALL_INT);
        b.asm.eq();
        let mut is_number_label = Label::new();
        b.asm.bif(&mut is_number_label);
        b.asm.dup();
        b.asm.const_(nanbox::TAG_BIG_INT);
        b.asm.eq();
        b.asm.bif(&mut is_number_label);
        b.asm.dup();
        b.asm.const_(nanbox::TAG_FLOAT);
        b.asm.eq();
        b.asm.bif(&mut is_number_label);
        b.asm.pop();
        let len_si = b.ensure_string("#");
        b.asm.string(len_si);
        b.asm.mode(inst::MODE_STRING);
        b.asm.nanbox();
        b.asm.mode(inst::MODE_LUA);
        b.asm.eq();
        let mut is_len_label = Label::new();
        b.asm.mode(inst::MODE_LUA);
        b.asm.bif(&mut is_len_label);
        let error_si = b.ensure_string("index argument must be \"#\" or integer");
        b.asm.string(error_si);
        b.asm.mode(inst::MODE_STRING);
        b.asm.panic(0);

        // If index is "#", return the number of variadic arguments.
        b.asm.bind(&mut is_len_label);
        b.asm.getv();
        b.asm.nanbox();
        b.asm.setvi(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();

        // If index is a number, try to convert to an integer.
        b.asm.bind(&mut is_number_label);
        b.asm.pop(); // type tag
        b.asm.unbox();
        b.asm.dup();
        b.asm.constzero();
        b.asm.lt();
        let mut is_negative_label = Label::new();
        b.asm.bif(&mut is_negative_label);
        b.asm.dup();
        b.asm.constzero();
        b.asm.gt();
        let mut is_positive_label = Label::new();
        b.asm.bif(&mut is_positive_label);
        let zero_error_si = b.ensure_string("index argument may not be zero");
        b.asm.string(zero_error_si);
        b.asm.mode(inst::MODE_STRING);
        b.asm.panic(0);

        // If index is positive, return the last max(0, vc - index + 1) values.
        b.asm.bind(&mut is_positive_label);
        b.asm.getv();
        b.asm.swap();
        b.asm.sub();
        b.asm.const_(1);
        b.asm.add();
        b.asm.dup();
        b.asm.constzero();
        b.asm.gt();
        let mut return_label = Label::new();
        b.asm.bif(&mut return_label);
        b.asm.pop();
        b.asm.constzero();
        b.asm.b(&mut return_label);

        // If index is negative, return the last min(vc, -index) values.
        b.asm.bind(&mut is_negative_label);
        b.asm.neg();
        b.asm.dup();
        b.asm.getv();
        b.asm.le();
        b.asm.bif(&mut return_label);
        b.asm.pop();
        b.asm.getv();

        // Return the last N values, where N is in local slot 0.
        b.asm.bind(&mut return_label);
        b.asm.mode(inst::MODE_LUA);
        b.asm.loadvarargs();
        b.asm.loadlocal(0);
        b.asm.setv();
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("select", 1, true);
    }

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
        b.asm.mode(inst::MODE_STRING);
        b.asm.panic(0);

        // Store the metatable into the table, then return the old one.
        // stack: oldtable newtable
        b.asm.bind(&mut store_metatable_label);
        b.asm.loadarg(0);
        b.asm.swap();
        b.asm.mode(inst::MODE_LUA);
        b.asm.storeprototype();
        b.asm.setvi(1);
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
        b.asm.setvi(1);
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
        b.asm.setvi(1);
        b.asm.mode(inst::MODE_LUA);
        b.asm.retv();
        b.finish_function("type", 1, false);
    }

    // TODO: warn
    // TODO: xpcall: this is difficult to support without a more invasive
    // interpreter change. The handler given to xpcall runs before the stack
    // is unwound.

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
    let ti = b.ensure_type(Type::Object);
    b.asm.alloc(ti);
    b.asm.mode(inst::MODE_OBJECT);
    b.asm.nanbox();
    for i in 0..b.package.functions.len() {
        if b.package.functions[i].name.starts_with("_") {
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
    b.asm.loadglobal(env_index);
    let version_si = b.ensure_string("Lua 5.4");
    b.asm.string(version_si);
    b.asm.mode(inst::MODE_STRING);
    b.asm.nanbox();
    b.asm.mode(inst::MODE_LUA);
    let version_name_si = b.ensure_string("_VERSION");
    b.asm.storenamedprop(version_name_si);
    b.asm.setvi(0);
    b.asm.mode(inst::MODE_LUA);
    b.asm.retv();
    b.finish_function("", 0, false);

    b.build()
}
