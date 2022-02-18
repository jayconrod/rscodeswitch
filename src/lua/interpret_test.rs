use crate::interpret::Interpreter;
use crate::lua::compile;
use crate::lua::luastd;
use crate::lua::scope;
use crate::lua::syntax;
use crate::lua::token;
use crate::pos::{Error, ErrorList, LineMap, Position};
use crate::runtime::{PackageLoader, ProvidedPackageSearcher};

use std::env;
use std::fmt::Display;
use std::fs;
use std::path::{Path, PathBuf};
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

        try_compile_and_interpret(&path)
            .map_err(print_error)
            .unwrap();
    }
    if !did_match {
        panic!("no tests matched pattern");
    }
}

fn try_compile_and_interpret(path: &Path) -> Result<(), ErrorList> {
    let mut searcher = Box::new(ProvidedPackageSearcher::new());
    let std_package = luastd::build_std_package();
    searcher.add(std_package);

    let mut chunk_paths = Vec::new();
    let mut chunk_datas = Vec::new();
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
                chunk_paths.push(chunk_path);
                chunk_datas.push(chunk_data);
                searcher.add(package);
            }
            None => {
                check_result(&path, chunk_data, Err(ErrorList::from(errors)))?;
            }
        };

        begin = end + chunk_sep.len();
        i += 1;
    }

    let mut loader = PackageLoader::new(searcher);
    for i in 0..chunk_paths.len() {
        let chunk_path = &chunk_paths[i];
        let chunk_data = &chunk_datas[i];
        let mut output = Vec::new();
        let mut interp = Interpreter::new(&mut output);
        let load_res =
            unsafe { loader.load_package(chunk_path.to_string_lossy().as_ref(), &mut interp) };
        let check_res = match load_res {
            Ok(_) => Ok(output),
            Err(err) => Err(ErrorList::from(err)),
        };
        check_result(chunk_path, chunk_data, check_res)?;
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
