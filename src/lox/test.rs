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

        let mut lmap = LineMap::new();
        let data = fs::read(&path).map_err(|err| Error::wrap(path, &err))?;
        let tokens = token::lex(&path, &data, &mut lmap).map_err(|err| Error::wrap(path, &err))?;
        let ast = syntax::parse(&tokens, &lmap).map_err(|err| Error::wrap(path, &err))?;
        let scopes = scope::resolve(&ast, &lmap).map_err(|err| Error::wrap(path, &err))?;
        let pkg = compile::compile(&ast, &scopes, &lmap).map_err(|err| Error::wrap(path, &err))?;

        let mut got = Vec::new();
        let mut interp = Interpreter::new(&mut got);
        let f = pkg
            .function_by_name("·init")
            .ok_or_else(|| Error::with_message(path, String::from("·init function not found")))?;
        interp.interpret(f).map_err(|err| Error::wrap(path, &err))?;
        let got_str = str::from_utf8(&got)
            .map_err(|err| Error::wrap(path, &err))?
            .trim();
        let want_str =
            expected_output(str::from_utf8(&data).map_err(|err| Error::wrap(path, &err))?);
        if got_str != want_str {
            return Err(Box::new(Error::with_message(
                path,
                format!("got:\n{}\n\nwant:\n{}", got_str, want_str),
            )));
        }
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

fn expected_output(mut data: &str) -> String {
    const MARKER: &'static str = "// Output:";
    let mut buf = String::new();
    let mut sep = "";
    loop {
        match data.find(MARKER) {
            None => return buf,
            Some(com_idx) => {
                let begin_idx = com_idx + MARKER.len();
                let end_idx = match data[begin_idx..].find('\n') {
                    None => data.len(),
                    Some(i) => begin_idx + i,
                };
                buf.push_str(sep);
                sep = "\n";
                buf.push_str(data[begin_idx..end_idx].trim());
                data = &data[end_idx..];
            }
        }
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
