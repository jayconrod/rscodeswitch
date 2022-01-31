use crate::lua::token::{self, Kind, Number};
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
    let mut errors = Vec::new();
    token::lex(&path, src, &mut lmap, &mut errors);
    assert!(errors.is_empty());
}

#[test]
fn test_bad_numbers() {
    let srcs = b".1 e1 .1e1 0x.1 0xp1";
    let path = PathBuf::from("test");
    for src in srcs.split(|&b| b == b' ') {
        let mut lmap = LineMap::new();
        let mut errors = Vec::new();
        let tokens = token::lex(&path, src, &mut lmap, &mut errors);
        assert!(tokens.len() == 1 || tokens[0].kind != Kind::Number);
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
    let mut errors = Vec::new();
    token::lex(&path, src, &mut lmap, &mut errors);
    assert!(errors.is_empty());
}

#[test]
fn test_bad_strings() {
    let srcs = b"'|\"|[[foo]|[=[foo]]";
    let path = PathBuf::from("test");
    for src in srcs.split(|&b| b == b'|') {
        let mut lmap = LineMap::new();
        let mut errors = Vec::new();
        let tokens = token::lex(&path, src, &mut lmap, &mut errors);
        assert!(tokens.len() == 1 || tokens[0].kind != Kind::String);
    }
}

#[test]
fn test_unquote_string() {
    let cases: Vec<(&str, &str)> = vec![
        // Empty strings
        ("''", ""),
        ("\"\"", ""),
        ("[[]]", ""),
        ("[=[]=]", ""),
        // Trivial non-empty string
        ("'foo'", "foo"),
        // One-character escape sequences
        ("'\\a'", "\x07"),
        ("'\\b'", "\x08"),
        ("'\\f'", "\x0c"),
        ("'\\n'", "\n"),
        ("'\\r'", "\r"),
        ("'\\t'", "\t"),
        ("'\\v'", "\x0b"),
        ("'\\\\'", "\\"),
        ("'\\''", "'"),
        ("'\\\"'", "\""),
        ("'\\\n'", "\n"),
        // Skip whitespace
        ("'a\\zb'", "ab"),
        ("'a\\z b'", "ab"),
        ("'a\\z \n\t\x0b b'", "ab"),
        // Hexadecimal bytes
        ("'\\x41'", "A"),
        ("'\\xE2\\x98\\x83'", "☃"),
        ("'\\xe2\\x98\\x83'", "☃"),
        // Decimal bytes
        ("'\\0'", "\0"),
        ("'\\65'", "A"),
        ("'\\226\\152\\1312'", "☃2"),
        // Unicode
        ("'\\u{2603}'", "☃"),
        // Whitespace in long string
        ("[[\na]]", "a"),
        ("[[\r\na]]", "a"),
        ("[[a\r]]", "a\n"),
        ("[[a\r\n]]", "a\n"),
        ("[[a\n\r]]", "a\n"),
        ("[[a\r]]", "a\n"),
        ("[[a\n\n]]", "a\n\n"),
        ("[[a\r\n\n]]", "a\n\n"),
    ];
    for (src, want) in cases {
        let got = token::unquote_string(src).unwrap();
        assert_eq!(&got, want.as_bytes());
    }
}

#[test]
fn test_unquote_string_bad() {
    let cases = vec![
        "'\\'", // unterminated escape
        "unquoted",
        "'unterminated",
        "''garbage",
        "[[unterminated]=]",
        "[=[unterminated]]",
        "[[]]garbage",
        "'\\?'",               // invalid escape
        "'\n'",                // unescaped newline
        "'\\x'",               // unterminated hex byte
        "'\\x1'",              // hex byte too short
        "'\\xGG'",             // invalid hex byte
        "'\\256'",             // invalid decimal byte
        "'\\u2603'",           // unicode without braces
        "'\\u{}'",             // unicode with empty braces
        "'\\u{999999999999}'", // unicode out of range
        "'\\u{garbage}'",      // unicode with invalid digits
    ];
    for src in cases {
        assert!(token::unquote_string(src).is_none());
    }
}

#[test]
fn test_convert_number() {
    let cases = vec![
        ("", Number::Malformed),
        ("-1", Number::Malformed),
        ("+1", Number::Malformed),
        ("1a", Number::Malformed),
        ("0", Number::Int(0)),
        ("01", Number::Int(1)),
        ("09", Number::Int(9)),
        ("9223372036854775807", Number::Int(9223372036854775807)),
        ("9223372036854775808", Number::Float(9223372036854776000.0)),
        ("1.", Number::Float(1.)),
        ("1.0", Number::Float(1.0)),
        ("1.5", Number::Float(1.5)),
        ("1.00000000000000001", Number::Float(1.0)),
        ("1e1", Number::Float(1e1)),
        ("1e1024", Number::Float(f64::INFINITY)),
        ("1e+1", Number::Float(1e+1)),
        ("1e-1", Number::Float(1e-1)),
        ("1E1", Number::Float(1E1)),
        ("1.e1", Number::Float(1.0e1)),
        ("1.5e1", Number::Float(1.5e1)),
        ("0x", Number::Malformed),
        ("0x0", Number::Int(0)),
        ("0X0", Number::Int(0)),
        ("0xab", Number::Int(0xab)),
        ("0xAB", Number::Int(0xAB)),
        ("0x7FFFFFFFFFFFFFFF", Number::Int(0x7FFFFFFFFFFFFFFF)),
    ];
    for (src, want) in cases {
        let got = token::convert_number(src);
        assert_eq!(got, want);
    }
}
