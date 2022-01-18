use codeswitch::interpret::Interpreter;
use codeswitch::lox::compile;

use std::env;
use std::fmt;
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

fn run(args: &[String]) -> Result<(), String> {
    if args.len() != 1 {
        return Err(String::from("expected exactly one argument"));
    }
    fn err_to_string<T: fmt::Display>(err: T) -> String {
        format!("{}", err)
    }

    let path = PathBuf::from(&args[0]);
    let package = compile::compile_file(&path).map_err(err_to_string)?;
    eprintln!("{}", package);

    let mut w = stdout();
    let mut interp = Interpreter::new(&mut w);
    let f = package
        .function_by_name("·init")
        .ok_or_else(|| String::from("·init function not found"))?;
    interp.interpret(f).map_err(err_to_string)?;
    Ok(())
}
