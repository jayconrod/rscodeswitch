use codeswitch::interpret::Interpreter;
use codeswitch::lua::compile;

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

    let path = PathBuf::from(&args[0]);
    let package = compile::compile_file(&path)?;

    let mut w = stdout();
    let mut interp = Interpreter::new(&mut w);
    let f = package
        .function_by_name("·init")
        .ok_or_else(|| Box::new(StringError("·init function not found")))?;
    interp.interpret(f)?;
    Ok(())
}

#[derive(Debug)]
struct StringError(&'static str);

impl Display for StringError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl Error for StringError {}
