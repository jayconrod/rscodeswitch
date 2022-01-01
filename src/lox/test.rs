use crate::interpret::Interpreter;
use crate::lox::compile;
use crate::lox::syntax;
use crate::lox::token;
use crate::pos::LineMap;

use std::error::Error;
use std::fs;
use std::str;

#[test]
fn interpret_test() -> Result<(), Box<dyn Error>> {
  for fi in fs::read_dir("testdata/lox").map_err(|err| Box::new(err))? {
    let fi = fi.map_err(|err| Box::new(err))?;
    let path_buf = fi.path();
    let path = match path_buf.to_str() {
      Some(path) if path.ends_with(".lox") => path,
      _ => continue,
    };

    let wrap_err =
      |err: Box<dyn Error>| -> Box<dyn Error> { format!("in file {}: {}", path, err).into() };

    let mut lmap = LineMap::new();
    let data = fs::read(&path)
      .map_err(|err| err.into())
      .map_err(wrap_err)?;
    let tokens = token::lex(&path, &data, &mut lmap)
      .map_err(|err| err.into())
      .map_err(wrap_err)?;
    let ast = syntax::parse(&tokens, &lmap)
      .map_err(|err| err.into())
      .map_err(wrap_err)?;
    let pkg = compile::compile(&ast, &lmap)
      .map_err(|err| err.into())
      .map_err(wrap_err)?;

    let mut got = Vec::new();
    let mut interp = Interpreter::new(&mut got, pkg);
    interp
      .interpret("init")
      .map_err(|err| err.into())
      .map_err(wrap_err)?;
    interp
      .interpret("main")
      .map_err(|err| err.into())
      .map_err(wrap_err)?;
    let got_str = str::from_utf8(&got)
      .map_err(|err| err.into())
      .map_err(wrap_err)?
      .trim();
    let want_str = expected_output(
      str::from_utf8(&data)
        .map_err(|err| err.into())
        .map_err(wrap_err)?,
    );
    if got_str != want_str {
      return Err(wrap_err(
        format!("got:\n{}\n\nwant:\n{}", got_str, want_str).into(),
      ));
    }
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
