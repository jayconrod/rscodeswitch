use crate::pos::{Error, LineMap, Pos};
use std::fmt;
use std::str::from_utf8_unchecked;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind {
    EOF,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Semi,
    Dot,
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
    And,
    Class,
    Else,
    For,
    Fun,
    If,
    Or,
    Print,
    Return,
    Super,
    This,
    Var,
    While,
    Nil,
    Bool,
    Number,
    String,
    Ident,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Kind::EOF => "end of file",
            Kind::LParen => "(",
            Kind::RParen => ")",
            Kind::LBrace => "{",
            Kind::RBrace => "}",
            Kind::Comma => ",",
            Kind::Semi => ";",
            Kind::Dot => ".",
            Kind::Assign => "=",
            Kind::Eq => "==",
            Kind::Ne => "!=",
            Kind::Lt => "<",
            Kind::Le => "<=",
            Kind::Gt => ">",
            Kind::Ge => ">=",
            Kind::Plus => "+",
            Kind::Minus => "-",
            Kind::Star => "*",
            Kind::Slash => "/",
            Kind::Bang => "!",
            Kind::And => "'and'",
            Kind::Class => "'class'",
            Kind::Else => "'else'",
            Kind::For => "'for'",
            Kind::Fun => "'fun'",
            Kind::If => "'if'",
            Kind::Or => "'or'",
            Kind::Print => "'print'",
            Kind::Return => "'return'",
            Kind::Super => "'super'",
            Kind::This => "'this'",
            Kind::Var => "'var'",
            Kind::While => "'while'",
            Kind::Nil => "'nil'",
            Kind::Bool => "bool",
            Kind::Number => "number",
            Kind::String => "string",
            Kind::Ident => "identifier",
        };
        f.write_str(s)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Token<'a> {
    pub type_: Kind,
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
                b'(' => Kind::LParen,
                b')' => Kind::RParen,
                b'{' => Kind::LBrace,
                b'}' => Kind::RBrace,
                b',' => Kind::Comma,
                b';' => Kind::Semi,
                b'.' => Kind::Dot, // TODO: fix conflict with floating point
                b'=' if bnext != b'=' => Kind::Assign,
                b'<' if bnext != b'=' => Kind::Lt,
                b'>' if bnext != b'=' => Kind::Gt,
                b'+' => Kind::Plus,
                b'-' => Kind::Minus,
                b'*' => Kind::Star,
                b'/' => Kind::Slash,
                b'!' if bnext != b'=' => Kind::Bang,
                _ => Kind::EOF,
            };
            if type_ != Kind::EOF {
                self.add_token(self.p + 1, type_);
                continue;
            }

            // Two-character tokens.
            let type_ = match (b, bnext) {
                (b'=', b'=') => Kind::Eq,
                (b'<', b'=') => Kind::Le,
                (b'>', b'=') => Kind::Ge,
                (b'!', b'=') => Kind::Ne,
                _ => Kind::EOF,
            };
            if type_ != Kind::EOF {
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
                    "and" => Kind::And,
                    "class" => Kind::Class,
                    "else" => Kind::Else,
                    "false" => Kind::Bool,
                    "for" => Kind::For,
                    "fun" => Kind::Fun,
                    "if" => Kind::If,
                    "or" => Kind::Or,
                    "nil" => Kind::Nil,
                    "print" => Kind::Print,
                    "return" => Kind::Return,
                    "super" => Kind::Super,
                    "this" => Kind::This,
                    "true" => Kind::Bool,
                    "var" => Kind::Var,
                    "while" => Kind::While,
                    _ => Kind::Ident,
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
                self.add_token(end, Kind::Number);
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
                self.add_token(end, Kind::String);
                continue;
            }

            // Unrecognized character or non-UTF-8 byte.
            if b.is_ascii() {
                return self.error(format!("unexpected character: '{}'", b));
            } else {
                return self.error(format!("unexpected non-ascii character: {}", b));
            }
        }

        self.add_token(self.p, Kind::EOF);
        Ok(())
    }

    fn add_token(&mut self, end: usize, type_: Kind) {
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
