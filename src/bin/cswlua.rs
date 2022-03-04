use codeswitch::interpret::{Env, InterpreterFactory};
use codeswitch::lua::compile;
use codeswitch::lua::luastd;
use codeswitch::lua::scope;
use codeswitch::lua::syntax;
use codeswitch::lua::token;
use codeswitch::pos::{Error, LineMap};
use codeswitch::runtime::{PackageLoader, ProvidedPackageSearcher};

use std::cell::RefCell;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::path::PathBuf;
use std::process;

use clap::Parser;
use rustyline::error::ReadlineError;
use rustyline::Editor;

#[derive(Parser, Debug)]
struct Args {
    #[clap(short, long, help = "Disassemble and print the compiled package")]
    disassemble: bool,

    #[clap(short, long, help = "Run interactively.")]
    interactive: bool,

    paths: Vec<String>,
}

fn main() {
    let args = Args::parse();
    if let Err(err) = run(&args) {
        eprintln!("cswlua: {}", err);
        process::exit(1);
    }
}

fn run(args: &Args) -> Result<(), Box<dyn std::error::Error>> {
    if !args.interactive && args.paths.is_empty() {
        return Err(Box::new(StringError("at least one argument is required")));
    }

    let mut searcher = Box::new(ProvidedPackageSearcher::new());
    let std_package = luastd::build_std_package();
    if args.disassemble {
        print!(
            "-- begin disassembly: {} --\n{}\n-- end disassembly --\n",
            std_package.name, std_package
        );
    }
    searcher.add(std_package);

    let loader_cell = RefCell::new(PackageLoader::new(searcher));
    let mut input = io::stdin();
    let mut output = io::stdout();
    let env_cell = RefCell::new(Env {
        r: &mut input,
        w: &mut output,
    });
    let interp_fac = InterpreterFactory::new(&env_cell);

    for path_arg in &args.paths {
        let path = PathBuf::from(&path_arg);
        let package = compile::compile_file(&path)?;
        if args.disassemble {
            print!(
                "-- begin disassembly: {} --\n{}\n-- end disassembly --\n",
                package.name, package
            );
        }
        let res = unsafe { PackageLoader::load_given_package(&loader_cell, interp_fac, package) };
        if let Err(err) = res {
            return Err(Box::new(err));
        }
    }

    if args.interactive {
        let mut buf = Vec::new();
        let mut rl = Editor::<()>::new();
        let path = PathBuf::from("<stdin>");
        let name = String::from("<stdin>");

        let is_incomplete = |errors: &[Error]| {
            if errors.len() != 1 {
                return false;
            }
            let err = &errors[0];
            // TODO: figure out some other way to indicate an early EOF.
            // Depending on the error message is too brittle.
            err.message.ends_with(", but found end of file")
        };

        loop {
            // Read the next line from the user.
            let prompt = if buf.is_empty() { "> " } else { ">> " };
            let line = match rl.readline(prompt) {
                Ok(line) => line,
                Err(ReadlineError::Eof) => break,
                Err(ReadlineError::Interrupted) => continue,
                Err(err) => {
                    eprintln!("{}", err);
                    continue;
                }
            };
            buf.extend_from_slice(line.as_bytes());

            // Attempt to parse.
            let mut lmap = LineMap::new();
            let mut errors = Vec::new();
            let tokens = token::lex(&path, &buf, &mut lmap, &mut errors);
            let chunk = syntax::parse(&tokens, &lmap, &mut errors);
            if is_incomplete(&errors) {
                continue;
            }

            // Resolve symbols, compile.
            let scope_set = scope::resolve(&chunk, &lmap, &mut errors);
            let package_opt =
                compile::compile_chunk(name.clone(), &chunk, &scope_set, &lmap, &mut errors);
            if !errors.is_empty() {
                for err in &errors {
                    eprintln!("{}", err);
                }
                errors.drain(..);
                buf.drain(..);
                continue;
            }
            let package = package_opt.unwrap();
            if args.disassemble {
                print!(
                    "-- begin disassembly: {}\n{}\n-- end disassembly --\n",
                    &package.name, package
                );
            }

            // Link and load the package. This will run its initializer, which
            // is the top-level code.
            let res =
                unsafe { PackageLoader::load_given_package(&loader_cell, interp_fac, package) };
            if let Err(err) = res {
                eprintln!("{}", err);
            }
            buf.drain(..);
        }
    }

    Ok(())
}

#[derive(Debug)]
struct StringError(&'static str);

impl Display for StringError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl std::error::Error for StringError {}
