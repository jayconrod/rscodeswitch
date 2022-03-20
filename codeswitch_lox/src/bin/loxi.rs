use codeswitch::interpret::{Env, InterpreterFactory};
use codeswitch::runtime::{LuaRuntimeUnimplemented, PackageLoader, ProvidedPackageSearcher};
use codeswitch_lox::compile;

use std::cell::RefCell;
use std::env;
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::path::PathBuf;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();
    if let Err(err) = run(&args[1..]) {
        eprintln!("{}", err);
        process::exit(1);
    }
}

fn run(args: &[String]) -> Result<(), Box<dyn Error>> {
    if args.len() != 1 {
        return Err(Box::new(StringError("expected exactly one argument")));
    }
    fn err_to_string<T: fmt::Display>(err: T) -> String {
        format!("{}", err)
    }

    let path = PathBuf::from(&args[0]);
    let package = compile::compile_file(&path).map_err(err_to_string)?;
    eprintln!("{}", package);
    let mut searcher = Box::new(ProvidedPackageSearcher::new());
    searcher.add(package);
    let loader_cell = RefCell::new(PackageLoader::new(searcher));
    let mut input = io::stdin();
    let mut output = io::stdout();
    let env_cell = RefCell::new(Env {
        r: &mut input,
        w: &mut output,
    });
    let lua_runtime = LuaRuntimeUnimplemented {};
    let interp_fac = InterpreterFactory::new(&env_cell, &loader_cell, &lua_runtime);
    let res = unsafe { PackageLoader::load_package(&loader_cell, interp_fac, "main") };
    match res {
        Ok(_) => Ok(()),
        Err(err) => Err(Box::new(err)),
    }
}

#[derive(Debug)]
struct StringError(&'static str);

impl Display for StringError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl Error for StringError {}
