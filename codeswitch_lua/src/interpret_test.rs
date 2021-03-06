use crate::compile;
use crate::luastd;
use crate::runtime::LuaRuntimeImpl;
use crate::scope;
use crate::syntax;
use crate::token;
use codeswitch::interpret::{Env, InterpreterFactory};
use codeswitch::package;
use codeswitch::pos::{Error, ErrorList, LineMap, Position};
use codeswitch::runtime::{PackageLoader, ProvidedPackageSearcher};

use std::cell::RefCell;
use std::env;
use std::fmt::Display;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::str;
use std::sync::Arc;

use lazy_regex::regex;
use regex::Regex;
use unified_diff;

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
    for fi in fs::read_dir("testdata").map_err(print_error).unwrap() {
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

        try_compile_and_interpret(&path)
            .map_err(print_error)
            .unwrap();
    }
    if !did_match {
        panic!("no tests matched pattern");
    }
}

fn try_compile_and_interpret(path: &Path) -> Result<(), ErrorList> {
    let searcher = Box::new(ProvidedPackageSearcher::new());
    let std_package = luastd::build_std_package();
    searcher.add(std_package);

    struct Chunk<'d> {
        path: PathBuf,
        data: &'d [u8],
        package: package::Package,
    }
    let mut chunks = Vec::new();
    let data = fs::read(path).map_err(|err| {
        let position = Position::from(path);
        let wrapped = Error::wrap(position, &err);
        ErrorList(vec![wrapped])
    })?;
    let chunk_sep = b"\n---\n";
    let mut begin = 0;
    let mut i = 0;
    while begin < data.len() {
        let end = match &data[begin..]
            .windows(chunk_sep.len())
            .position(|w| w == chunk_sep)
        {
            Some(i) => begin + i,
            None => data.len(),
        };
        let chunk_data = &data[begin..end];
        let chunk_path = if i == 0 {
            PathBuf::from(path)
        } else {
            PathBuf::from(format!("{}#{}", path.to_string_lossy(), i))
        };

        let mut lmap = LineMap::new();
        let mut errors = Vec::new();
        let tokens = token::lex(&chunk_path, chunk_data, &mut lmap, &mut errors);
        let ast = syntax::parse(&tokens, &lmap, &mut errors);
        let scope_set = scope::resolve(&ast, &lmap, &mut errors);
        match compile::compile_chunk(
            chunk_path.to_string_lossy().into(),
            &ast,
            &scope_set,
            &lmap,
            &mut errors,
        ) {
            Some(package) => {
                chunks.push(Chunk {
                    path: chunk_path,
                    data: chunk_data,
                    package,
                });
            }
            None => {
                check_result(&chunk_path, chunk_data, Err(ErrorList::from(errors)))?;
            }
        };

        begin = end + chunk_sep.len();
        i += 1;
    }

    let loader = Arc::new(PackageLoader::new(searcher));
    for chunk in chunks {
        let mut input = io::empty();
        let mut output = Vec::new();
        let env_cell = RefCell::new(Env {
            r: &mut input,
            w: &mut output,
        });
        let lua_runtime = LuaRuntimeImpl {};
        let interp_fac = InterpreterFactory::new(&env_cell, loader.clone(), &lua_runtime);
        let load_res = unsafe { loader.load_given_package(&interp_fac, chunk.package) };
        let check_res = match load_res {
            Ok(_) => Ok(output),
            Err(err) => Err(ErrorList::from(err)),
        };
        check_result(&chunk.path, chunk.data, check_res)?;
    }
    Ok(())
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
                let diff =
                    unified_diff::diff(got_text.as_bytes(), "got", want_text.as_bytes(), "want", 3);
                let diff_text = str::from_utf8(&diff).unwrap();
                Err(ErrorList::new(
                    Position::from(path),
                    &format!(
                        "got errors:\n{}\n\nwant errors:\n{}\n\n{}",
                        got_text, want_text, &diff_text
                    ),
                ))
            }
        }
        (Ok(got), Want::Output(want_text)) => {
            let got_text = str::from_utf8(&got)
                .map_err(|err| ErrorList::wrap(Position::from(path), &err))
                .map(|s| s.trim_end())?;
            if got_text == want_text {
                Ok(())
            } else {
                let diff =
                    unified_diff::diff(got_text.as_bytes(), "got", want_text.as_bytes(), "want", 3);
                let diff_text = str::from_utf8(&diff).unwrap();
                Err(ErrorList::new(
                    Position::from(path),
                    &format!(
                        "got output:\n{}\n\nwant:\n{}\n\n{}",
                        got_text, want_text, &diff_text
                    ),
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
