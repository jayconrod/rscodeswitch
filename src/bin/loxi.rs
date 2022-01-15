use codeswitch::interpret::Interpreter;
use codeswitch::lox::compile;
use codeswitch::lox::scope;
use codeswitch::lox::syntax;
use codeswitch::lox::token;
use codeswitch::pos::LineMap;

use std::env;
use std::fmt;
use std::fs;
use std::io::stdout;
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
        let scopes = scope::resolve(&ast, &lmap).map_err(err_to_string)?;
        let pkg = compile::compile(&ast, &scopes, &lmap).map_err(err_to_string)?;
        eprintln!("{}", pkg);

        let mut w = stdout();
        let mut interp = Interpreter::new(&mut w);
        let f = pkg
            .function_by_name("·init")
            .ok_or_else(|| String::from("·init function not found"))?;
        interp.interpret(f).map_err(err_to_string)?;
    }
    Ok(())
}
