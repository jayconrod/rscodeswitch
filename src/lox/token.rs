use crate::pos::{Error, LineMap, Pos};
use std::fmt;
use std::str::from_utf8_unchecked;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Type {
    EOF,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Semi,
    Assign,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Bang,
    Fun,
    Print,
    Var,
    Bool,
    Number,
    String,
    Ident,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Type::EOF => "end of file",
            Type::LParen => "(",
            Type::RParen => ")",
            Type::LBrace => "{",
            Type::RBrace => "}",
            Type::Comma => ",",
            Type::Semi => ";",
            Type::Assign => "=",
            Type::Eq => "==",
            Type::Ne => "!=",
            Type::Lt => "<",
            Type::Le => "<=",
            Type::Gt => ">",
            Type::Ge => ">=",
            Type::Plus => "+",
            Type::Minus => "-",
            Type::Star => "*",
            Type::Slash => "/",
            Type::Bang => "!",
            Type::Fun => "'fun'",
            Type::Print => "'print'",
            Type::Var => "'var'",
            Type::Bool => "bool",
            Type::Number => "number",
            Type::String => "string",
            Type::Ident => "identifier",
        };
        f.write_str(s)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Token<'a> {
    pub type_: Type,
    pub text: &'a str,
    pub from: Pos,
    pub to: Pos,
}

pub fn lex<'a>(
    filename: &str,
    data: &'a [u8],
    lmap: &mut LineMap,
) -> Result<Vec<Token<'a>>, Error> {
    let mut l = Lexer::new(filename, data, lmap);
    l.lex()?;
    Ok(l.tokens)
}

struct Lexer<'a, 'b> {
    data: &'a [u8],
    tset: &'b mut LineMap,
    base: usize,
    tokens: Vec<Token<'a>>,
    p: usize,
}

impl<'a, 'b> Lexer<'a, 'b> {
    fn new(filename: &str, data: &'a [u8], tset: &'b mut LineMap) -> Lexer<'a, 'b> {
        let base = tset.add_file(filename, data.len());
        Lexer {
            data: data,
            tset: tset,
            base: base,
            tokens: Vec::new(),
            p: 0,
        }
    }

    fn lex(&mut self) -> Result<(), Error> {
        while self.p < self.data.len() {
            let b = self.data[self.p];
            let bnext = if self.p + 1 < self.data.len() {
                self.data[self.p + 1]
            } else {
                0
            };

            // Skip whitespace and comments.
            if b == b' ' || b == b'\t' {
                self.p += 1;
                continue;
            } else if b == b'\n' {
                self.tset.add_line(self.p);
                self.p += 1;
                continue;
            } else if b == b'/' && bnext == b'/' {
                let mut end = self.p + 2;
                while end < self.data.len() && self.data[end] != b'\n' {
                    end += 1;
                }
                self.p = end;
                continue;
            }

            // One-character tokens.
            let type_ = match b {
                b'(' => Type::LParen,
                b')' => Type::RParen,
                b'{' => Type::LBrace,
                b'}' => Type::RBrace,
                b',' => Type::Comma,
                b';' => Type::Semi,
                b'=' if bnext != b'=' => Type::Assign,
                b'<' if bnext != b'=' => Type::Lt,
                b'>' if bnext != b'=' => Type::Gt,
                b'+' => Type::Plus,
                b'-' => Type::Minus,
                b'*' => Type::Star,
                b'/' => Type::Slash,
                b'!' if bnext != b'=' => Type::Bang,
                _ => Type::EOF,
            };
            if type_ != Type::EOF {
                self.add_token(self.p + 1, type_);
                continue;
            }

            // Two-character tokens.
            let type_ = match (b, bnext) {
                (b'=', b'=') => Type::Eq,
                (b'<', b'=') => Type::Le,
                (b'>', b'=') => Type::Ge,
                (b'!', b'=') => Type::Ne,
                _ => Type::EOF,
            };
            if type_ != Type::EOF {
                self.add_token(self.p + 2, type_);
                continue;
            }

            // Everything else.
            if self.is_ident_first(b) {
                // Identifier or keyword.
                let mut end = self.p + 1;
                while end < self.data.len() && self.is_ident(self.data[end]) {
                    end += 1;
                }
                let text = unsafe { from_utf8_unchecked(&self.data[self.p..end]) };
                let type_ = match text {
                    "false" => Type::Bool,
                    "fun" => Type::Fun,
                    "print" => Type::Print,
                    "true" => Type::Bool,
                    "var" => Type::Var,
                    _ => Type::Ident,
                };
                self.add_token(end, type_);
                continue;
            }

            if b.is_ascii_digit() {
                // Number.
                let mut end = self.p + 1;
                while end < self.data.len() && self.data[end].is_ascii_digit() {
                    end += 1;
                }
                let text = unsafe { from_utf8_unchecked(&self.data[self.p..end]) };
                if text.parse::<f64>().is_err() {
                    return self.error_end(end, format!("could not parse number: {}", text));
                }
                self.add_token(end, Type::Number);
                continue;
            }

            if b == b'"' {
                // String.
                let mut end = self.p + 1;
                while end < self.data.len() && self.data[end] != b'"' {
                    end += 1;
                }
                if end == self.data.len() {
                    return self.error_end(end, format!("unterminated string literal"));
                }
                end += 1;
                self.add_token(end, Type::String);
                continue;
            }

            // Unrecognized character or non-UTF-8 byte.
            if b.is_ascii() {
                return self.error(format!("unexpected character: '{}'", b));
            } else {
                return self.error(format!("unexpected non-ascii character: {}", b));
            }
        }

        self.add_token(self.p, Type::EOF);
        Ok(())
    }

    fn add_token(&mut self, end: usize, type_: Type) {
        self.tokens.push(Token {
            type_: type_,
            text: unsafe { from_utf8_unchecked(&self.data[self.p..end]) },
            from: Pos {
                offset: self.base + self.p,
            },
            to: Pos {
                offset: self.base + end,
            },
        });
        self.p = end
    }

    fn is_ident_first(&self, b: u8) -> bool {
        b.is_ascii_alphabetic() || b == b'_'
    }

    fn is_ident(&self, b: u8) -> bool {
        b.is_ascii_alphanumeric() || b == b'_'
    }

    fn error(&self, message: String) -> Result<(), Error> {
        self.error_end(self.p + 1, message)
    }

    fn error_end(&self, end: usize, message: String) -> Result<(), Error> {
        let from = Pos {
            offset: self.base + self.p,
        };
        let to = Pos {
            offset: self.base + end,
        };
        let position = self.tset.position(from, to);
        Err(Error { position, message })
    }
}
