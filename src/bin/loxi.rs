use codeswitch::interpret::Interpreter;
use codeswitch::lox::compile;
use codeswitch::runtime::{PackageLoader, ProvidedPackageSearcher};

use std::env;
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io::stdout;
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
    let mut loader = PackageLoader::new(searcher);

    let mut w = stdout();
    let mut interp = Interpreter::new(&mut w);
    let res = unsafe { loader.load_package("main", &mut interp) };
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
