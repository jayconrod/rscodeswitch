use crate::interpret::Interpreter;
use crate::lox::compile;
use crate::lox::syntax;
use crate::lox::token;
use crate::pos::LineMap;

use std::fmt;
use std::fs;
use std::str;

#[test]
fn interpret_test() -> Result<(), String> {
  fn err_to_string<T: fmt::Display>(err: T) -> String {
    format!("{}", err)
  }

  for fi in fs::read_dir("testdata/lox").map_err(err_to_string)? {
    let fi = fi.map_err(err_to_string)?;
    let path_buf = fi.path();
    let path = match path_buf.to_str() {
      Some(path) if path.ends_with(".lox") => path,
      _ => continue,
    };

    let mut lmap = LineMap::new();
    let data = fs::read(&path).map_err(err_to_string)?;
    let tokens = token::lex(&path, &data, &mut lmap).map_err(err_to_string)?;
    let ast = syntax::parse(&tokens, &lmap).map_err(err_to_string)?;
    let pkg = compile::compile(&ast, &lmap).map_err(err_to_string)?;
    eprintln!("{}", pkg);

    let mut got = Vec::new();
    let mut interp = Interpreter::new(&mut got, pkg);
    interp.interpret("init").map_err(err_to_string)?;
    interp.interpret("main").map_err(err_to_string)?;
    let got_str = str::from_utf8(&got).map_err(err_to_string)?.trim();
    let want_str = expected_output(str::from_utf8(&data).map_err(err_to_string)?);
    assert_eq!(got_str, want_str);
  }
  Ok(())
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
