use codeswitch::interpret::interpret;
use codeswitch::lox::compile;
use codeswitch::lox::syntax;
use codeswitch::lox::token;
use codeswitch::pos::LineMap;

use std::env;
use std::fmt;
use std::fs;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();
    if let Err(err) = run(&args[1..]) {
        eprintln!("{}", err);
        process::exit(1);
    }
}

fn run(args: &[String]) -> Result<(), String> {
    if args.is_empty() {
        return Err(String::from("expected at least one argument"));
    }
    fn err_to_string<T: fmt::Display>(err: T) -> String {
        format!("{}", err)
    }

    let mut lmap = LineMap::new();
    for filename in args {
        let data = fs::read(&filename).map_err(err_to_string)?;
        let tokens = token::lex(&filename, &data, &mut lmap).map_err(err_to_string)?;
        let ast = syntax::parse(&tokens, &lmap).map_err(err_to_string)?;
        let pkg = compile::compile(&ast, &lmap).map_err(err_to_string)?;
        let f = pkg
            .function_by_name("main")
            .ok_or(String::from("main function not found"))?;
        interpret(f)
    }
    Ok(())
}
