use codeswitch::interpret::Interpreter;
use codeswitch::lua::compile;

use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io::stdout;
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
    let path = PathBuf::from(&args.path);
    let package = compile::compile_file(&path)?;
    if args.disassemble {
        print!(
            "-- begin disassembly --\n{}\n-- end disassembly --\n",
            package
        );
    }

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
