use crate::lua::token::{self, Kind};
use crate::pos::LineMap;

use std::path::PathBuf;

#[test]
fn test_numbers() {
  let src = b"
  0
  01
  12
  1.2
  12.34
  12e34
  12E34
  12e+34
  12e-34
  12.34e+56
  0x1
  0X1
  0x89
  0xAB
  0xeF
  0xAb
  0xAB.CD
  0xABPCD
  0xABpCD
  0xABp+CD
  0xABp-CD
  0xAB.CDP+EF
  ";
  let path = PathBuf::from("test");
  let mut lmap = LineMap::new();
  token::lex(&path, src, &mut lmap).unwrap();
}

#[test]
fn test_bad_numbers() {
  let srcs = b".1 e1 .1e1 0x.1 0xp1";
  let path = PathBuf::from("test");
  for src in srcs.split(|&b| b == b' ') {
    let mut lmap = LineMap::new();
    match token::lex(&path, src, &mut lmap) {
      Ok(tokens) => assert!(tokens.len() == 1 || tokens[0].kind != Kind::Number),
      _ => (),
    }
  }
}

#[test]
fn test_strings() {
  let src = b"
  ''
  \"\"
  'f'
  \"f\"
  'foo'
  \"foo\"
  'foo\\d'
  '\\food'
  'fo\\
od'
  'fo\\'od'
  'fo\\\\'
  [[foo]]
  [=[foo]=]
  [==[foo]==]
  ";
  let path = PathBuf::from("test");
  let mut lmap = LineMap::new();
  token::lex(&path, src, &mut lmap).unwrap();
}

#[test]
fn test_bad_strings() {
  let srcs = b"'|\"|[[foo]|[=[foo]]";
  let path = PathBuf::from("test");
  for src in srcs.split(|&b| b == b'|') {
    let mut lmap = LineMap::new();
    match token::lex(&path, src, &mut lmap) {
      Ok(tokens) => assert!(tokens.len() == 1 || tokens[0].kind != Kind::String),
      _ => (),
    }
  }
}
