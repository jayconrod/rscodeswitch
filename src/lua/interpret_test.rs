use crate::interpret::Interpreter;
use crate::lua::compile;
use crate::pos::{ErrorList, Position};

use std::env;
use std::fmt::Display;
use std::fs;
use std::path::Path;
use std::str;

use lazy_regex::regex;
use regex::Regex;

// TODO: also need a convenient way to test for errors.

#[test]
fn interpret_test() {
    fn print_error<T: Display>(err: T) -> ! {
        eprintln!("{}", err);
        panic!("unexpected error")
    }
    let filter_re_opt = match env::var("CODESWITCH_TEST_FILTER") {
        Ok(s) => Some(Regex::new(&s).unwrap()),
        _ => None,
    };

    let mut did_match = false;
    for fi in fs::read_dir("testdata/lua").map_err(print_error).unwrap() {
        let fi = fi.map_err(print_error).unwrap();
        let path = fi.path();
        let path_str = match path.to_str() {
            Some(s) => s,
            None => continue,
        };
        if let Some(ref filter_re) = filter_re_opt {
            if !filter_re.is_match(path_str) {
                continue;
            }
        }
        did_match = true;

        let res = try_compile_and_interpret(&path);
        let data = fs::read(&path).map_err(print_error).unwrap();
        check_result(&path, &data, res)
            .map_err(print_error)
            .unwrap();
    }
    if !did_match {
        panic!("no tests matched pattern");
    }
}

fn try_compile_and_interpret(path: &Path) -> Result<Vec<u8>, ErrorList> {
    let package = compile::compile_file(path)?;
    let mut output = Vec::new();
    let mut interp = Interpreter::new(&mut output);
    let f = package.function_by_name("·init").ok_or_else(|| {
        let position = Position::from(path);
        ErrorList::new(position, "·init function not found")
    })?;
    match interp.interpret(f) {
        Ok(_) => Ok(output),
        Err(err) => Err(ErrorList::from(err)),
    }
}

fn check_result(
    path: &Path,
    data: &[u8],
    res: Result<Vec<u8>, ErrorList>,
) -> Result<(), ErrorList> {
    let want = parse_want(path, data)?;
    match (res, want) {
        (Ok(_), Want::Error(want_text)) => Err(ErrorList::new(
            Position::from(path),
            &format!(
                "unexpected success; expected error containing '{}'",
                want_text
            ),
        )),
        (Err(errs), Want::Output(_)) => Err(ErrorList::new(
            Position::from(path),
            &format!("unexpected error: {}", errs),
        )),
        (Err(errs), Want::Error(want_text)) => {
            let pos_re_src = format!(r"(?m)^{}:[^:]*:\s*", regex::escape(path.to_str().unwrap()));
            let pos_re = Regex::new(&pos_re_src).unwrap();
            let got_text_raw = errs.to_string();
            let got_text = pos_re.replace_all(&got_text_raw, "");
            if got_text == want_text {
                Ok(())
            } else {
                Err(ErrorList::new(
                    Position::from(path),
                    &format!("got errors:\n{}\n\nwant errors:\n{}", got_text, want_text),
                ))
            }
        }
        (Ok(got), Want::Output(want_text)) => {
            let got_text = str::from_utf8(&got)
                .map_err(|err| ErrorList::wrap(Position::from(path), &err))
                .map(|s| s.trim())?;
            if got_text == want_text {
                Ok(())
            } else {
                Err(ErrorList::new(
                    Position::from(path),
                    &format!("got output:\n{}\n\nwant:\n{}", got_text, want_text),
                ))
            }
        }
    }
}

enum Want {
    Output(String),
    Error(String),
}

fn parse_want(path: &Path, data: &[u8]) -> Result<Want, ErrorList> {
    let re = regex!(r"(?m)-- (Output|Error): *(.*)$");
    let data_str =
        str::from_utf8(data).map_err(|err| ErrorList::wrap(Position::from(path), &err))?;
    let mut first_label: Option<String> = None;
    let mut text = String::new();
    let mut sep = "";
    for m in re.captures_iter(data_str) {
        if let Some(first_label) = &first_label {
            if first_label != m.get(1).unwrap().as_str() {
                return Err(ErrorList::wrap(
                    Position::from(path),
                    &String::from("test may check 'Output' or 'Error', not both"),
                ));
            }
        } else {
            first_label = Some(String::from(m.get(1).unwrap().as_str()))
        }
        text.push_str(sep);
        sep = "\n";
        text.push_str(m.get(2).unwrap().as_str());
    }
    match first_label {
        Some(s) if s == "Error" => Ok(Want::Error(text)),
        _ => Ok(Want::Output(text)),
    }
}
