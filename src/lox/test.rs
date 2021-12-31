use crate::interpret::interpret;
use crate::lox::compile;
use crate::lox::syntax;
use crate::lox::token;
use crate::pos::LineMap;

use std::fs;
use std::str;

#[test]
fn interpret_test() {
  for fi in fs::read_dir("testdata/lox").unwrap() {
    let path = String::from(fi.unwrap().path().to_str().unwrap());
    if !path.ends_with(".lox") {
      continue;
    }

    let mut lmap = LineMap::new();
    let data = fs::read(&path).unwrap();
    let tokens = token::lex(&path, &data, &mut lmap).unwrap();
    let ast = syntax::parse(&tokens, &lmap).unwrap();
    let pkg = compile::compile(&ast, &lmap).unwrap();
    let f = pkg.function_by_name("main").unwrap();

    let mut got = Vec::new();
    interpret(&mut got, f).unwrap();
    let got_str = str::from_utf8(&got).unwrap().trim();
    let want_str = expected_output(str::from_utf8(&data).unwrap());
    assert_eq!(got_str, want_str);
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
