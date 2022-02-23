use codeswitch::interpret::{Env, InterpreterFactory};
use codeswitch::lua::compile;
use codeswitch::lua::luastd;
use codeswitch::runtime::{PackageLoader, ProvidedPackageSearcher};

use std::cell::RefCell;
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::path::PathBuf;
use std::process;

use clap::Parser;

#[derive(Parser, Debug)]
struct Args {
    #[clap(short, long, help = "Disassemble and print the compiled package")]
    disassemble: bool,

    path: String,
}

fn main() {
    let args = Args::parse();
    if let Err(err) = run(&args) {
        eprintln!("{}", err);
        process::exit(1);
    }
}

fn run(args: &Args) -> Result<(), Box<dyn Error>> {
    let mut searcher = Box::new(ProvidedPackageSearcher::new());
    let std_package = luastd::build_std_package();
    if args.disassemble {
        print!(
            "-- begin disassembly: {} --\n{}\n-- end disassembly --\n",
            std_package.name, std_package
        );
    }
    searcher.add(std_package);

    let path = PathBuf::from(&args.path);
    let package = compile::compile_file(&path)?;
    if args.disassemble {
        print!(
            "-- begin disassembly: {} --\n{}\n-- end disassembly --\n",
            package.name, package
        );
    }

    let loader_cell = RefCell::new(PackageLoader::new(searcher));
    let mut input = io::stdin();
    let mut output = io::stdout();
    let env_cell = RefCell::new(Env {
        r: &mut input,
        w: &mut output,
    });
    let interp_fac = InterpreterFactory::new(&env_cell);
    let res = unsafe { PackageLoader::load_given_package(&loader_cell, interp_fac, package) };
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
