use crate::interpret::Interpreter;
use crate::lox::compile;
use crate::lox::scope;
use crate::lox::syntax;
use crate::lox::token;
use crate::pos::LineMap;

use std::env;
use std::error;
use std::fmt::{self, Debug, Display, Formatter};
use std::fs;
use std::str;

use regex::Regex;

// TODO: also need a convenient way to test for errors.

#[test]
fn interpret_test() -> Result<(), Box<dyn std::error::Error>> {
    let filter_re_opt = match env::var("CODESWITCH_TEST_FILTER") {
        Ok(s) => Some(Regex::new(&s)?),
        _ => None,
    };

    let mut did_match = false;
    for fi in fs::read_dir("testdata/lox").map_err(|err| Box::new(err))? {
        let fi = fi.map_err(|err| Box::new(err))?;
        let path_buf = fi.path();
        let path = match path_buf.to_str() {
            Some(path) if path.ends_with(".lox") => path,
            _ => continue,
        };
        if let Some(ref filter_re) = filter_re_opt {
            if !filter_re.is_match(path) {
                continue;
            }
        }
        did_match = true;

        let data = fs::read(&path).map_err(|err| Error::wrap(path, &err))?;
        let res = try_interpret(path, &data);
        check_result(path, &data, res)?;
    }
    if !did_match {
        Err(Box::new(Error::with_message(
            "",
            String::from("no tests matched pattern"),
        )))
    } else {
        Ok(())
    }
}

fn try_interpret(path: &str, data: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut lmap = LineMap::new();
    let tokens = token::lex(path, data, &mut lmap)?;
    let ast = syntax::parse(&tokens, &lmap)?;
    let scopes = scope::resolve(&ast, &lmap)?;
    let pkg = compile::compile(&ast, &scopes, &lmap)?;

    let mut output = Vec::new();
    let mut interp = Interpreter::new(&mut output);
    let f = pkg
        .function_by_name("·init")
        .ok_or_else(|| Error::with_message(path, String::from("·init function not found")))?;
    interp.interpret(f)?;
    Ok(output)
}

fn check_result(
    filename: &str,
    data: &[u8],
    res: Result<Vec<u8>, Box<dyn std::error::Error>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let data_str = str::from_utf8(data)?;
    let error_re = Regex::new(r"(?m)// Error:\s*(.*)$").unwrap();
    if let Some(m) = error_re.captures(data_str) {
        let begin = m.get(0).unwrap().start();
        let line = data[..begin]
            .iter()
            .fold(1, |c, &b| c + (b == b'\n') as usize);
        let message = m.get(1).unwrap().as_str();
        let want_re_src = format!(
            r"^{}:{}[.-][^:]*:.*({}).*$",
            regex::escape(filename),
            line,
            regex::escape(message)
        );
        let want_re = Regex::new(&want_re_src).unwrap();
        return match res {
            Ok(_) => Err(Box::new(Error::with_message(
                filename,
                String::from("unexpected success"),
            ))),
            Err(err) => {
                let got = format!("{}", err);
                if want_re.is_match(&got) {
                    Ok(())
                } else {
                    Err(Box::new(Error::with_message(
                        filename,
                        format!(
                            "got error '{}'; want error on line {} containing '{}'",
                            got, line, message
                        ),
                    )))
                }
            }
        };
    }

    let got = match res {
        Ok(ref output) => str::from_utf8(output)?.trim(),
        Err(_) => {
            return res.map(|_| ());
        }
    };

    let want_re = Regex::new(r"(?m)// Output:\s*(.*)\s*$").unwrap();
    let mut want = String::new();
    let mut sep = "";
    for m in want_re.captures_iter(data_str) {
        want += sep;
        sep = "\n";
        want += m.get(1).unwrap().as_str();
    }
    if got == want {
        Ok(())
    } else {
        Err(Box::new(Error::with_message(
            filename,
            format!("got:\n{}\n\nwant:\n{}", got, want),
        )))
    }
}

struct Error {
    path: String,
    message: String,
}

impl Error {
    fn with_message(path: &str, message: String) -> Error {
        Error {
            path: String::from(path),
            message: message,
        }
    }
    fn wrap(path: &str, err: &dyn fmt::Display) -> Error {
        Error {
            path: String::from(path),
            message: format!("{}", err),
        }
    }
}

impl Debug for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Error{{ {} }}", self)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut sep = "";
        if !self.path.is_empty() {
            f.write_str(&self.path)?;
            sep = ": ";
        }
        write!(f, "{}{}", sep, self.message)
    }
}

impl error::Error for Error {}
