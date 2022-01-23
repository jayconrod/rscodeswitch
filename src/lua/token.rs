use crate::pos::{Error, ErrorList, LineMap, Pos};
use std::fmt::{self, Display, Formatter};
use std::path::Path;
use std::str;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind {
    EOF,

    // Punctuation and operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Caret,
    Hash,
    Amp,
    Tilde,
    Pipe,
    LtLt,
    GtGt,
    SlashSlash,
    EqEq,
    TildeEq,
    LtEq,
    GtEq,
    Lt,
    Gt,
    Eq,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBrack,
    RBrack,
    ColonColon,
    Semi,
    Colon,
    Comma,
    Dot,
    DotDot,
    DotDotDot,

    // Keywords
    And,
    Break,
    Do,
    Else,
    Elseif,
    End,
    False,
    For,
    Function,
    Goto,
    If,
    In,
    Local,
    Nil,
    Not,
    Or,
    Repeat,
    Return,
    Then,
    True,
    Until,
    While,

    // Literals
    Ident,
    String,
    Number,
}

impl Display for Kind {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let s = match self {
            Kind::EOF => "end of file",
            Kind::Plus => "+",
            Kind::Minus => "-",
            Kind::Star => "*",
            Kind::Slash => "/",
            Kind::Percent => "%",
            Kind::Caret => "^",
            Kind::Hash => "#",
            Kind::Amp => "&",
            Kind::Tilde => "~",
            Kind::Pipe => "|",
            Kind::LtLt => "<<",
            Kind::GtGt => ">>",
            Kind::SlashSlash => "//",
            Kind::EqEq => "==",
            Kind::TildeEq => "~=",
            Kind::LtEq => "<=",
            Kind::GtEq => ">=",
            Kind::Lt => "<",
            Kind::Gt => ">",
            Kind::Eq => "=",
            Kind::LParen => "(",
            Kind::RParen => ")",
            Kind::LBrace => "{",
            Kind::RBrace => "}",
            Kind::LBrack => "[",
            Kind::RBrack => "]",
            Kind::ColonColon => "::",
            Kind::Semi => ";",
            Kind::Colon => ":",
            Kind::Comma => ",",
            Kind::Dot => ".",
            Kind::DotDot => "..",
            Kind::DotDotDot => "...",
            Kind::And => "'and'",
            Kind::Break => "'break'",
            Kind::Do => "'do'",
            Kind::Else => "'else'",
            Kind::Elseif => "'elseif'",
            Kind::End => "'end'",
            Kind::False => "'false'",
            Kind::For => "'for'",
            Kind::Function => "'function'",
            Kind::Goto => "'goto'",
            Kind::If => "'if'",
            Kind::In => "'in'",
            Kind::Local => "'local'",
            Kind::Nil => "'nil'",
            Kind::Not => "'not'",
            Kind::Or => "'or'",
            Kind::Repeat => "'repeat'",
            Kind::Return => "'return'",
            Kind::Then => "'then'",
            Kind::True => "'true'",
            Kind::Until => "'until'",
            Kind::While => "'while'",
            Kind::Ident => "identifier",
            Kind::String => "string",
            Kind::Number => "number",
        };
        f.write_str(s)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Token<'src> {
    pub kind: Kind,
    pub text: &'src str,
    pub offset: usize,
}

impl<'src> Token<'src> {
    pub fn pos(&self) -> Pos {
        Pos {
            begin: self.offset,
            end: self.offset + self.text.len(),
        }
    }
}

/// Splits a source file into Lua tokens that can be consumed by the parser.
/// Tokens reference text in the source file, so the source bytes must outlive
/// the token list.
///
/// lex adds a file to lmap and adds a line for each newline character it finds.
///
/// If the file contains errors, lex returns them instead of tokens. lex
/// attempts to recover after an error by skipping characters until after
/// whitespace.
pub fn lex<'src>(
    path: &Path,
    data: &'src [u8],
    lmap: &mut LineMap,
) -> Result<Vec<Token<'src>>, ErrorList> {
    let mut l = Lexer::new(path, data, lmap);
    l.lex();
    if l.errors.is_empty() {
        Ok(l.tokens)
    } else {
        Err(ErrorList(l.errors))
    }
}

struct Lexer<'src, 'lm> {
    data: &'src [u8],
    lmap: &'lm mut LineMap,
    base: usize,
    tokens: Vec<Token<'src>>,
    errors: Vec<Error>,
    p: usize,
}

impl<'src, 'lm> Lexer<'src, 'lm> {
    fn new(path: &Path, data: &'src [u8], lmap: &'lm mut LineMap) -> Lexer<'src, 'lm> {
        let base = lmap.add_file(path, data.len());
        Lexer {
            data,
            lmap,
            base,
            tokens: Vec::new(),
            errors: Vec::new(),
            p: 0,
        }
    }

    fn lex(&mut self) {
        while self.p < self.data.len() {
            let b = self.data[self.p];
            let bnext = if self.p + 1 < self.data.len() {
                self.data[self.p + 1]
            } else {
                0
            };

            // Skip whitespace and comments.
            if is_space(b) {
                self.p += 1;
                continue;
            }
            if b == b'\n' {
                self.p += 1;
                self.lmap.add_line(self.base + self.p);
                continue;
            }
            if b == b'-' && bnext == b'-' {
                let mut end = self.p + 2;
                while end < self.data.len() && self.data[end] != b'\n' {
                    end += 1;
                }
                self.p = end;
                continue;
            }

            // Two-character operators.
            let kind = match (b, bnext) {
                (b'<', b'<') => Kind::LtLt,
                (b'>', b'>') => Kind::GtGt,
                (b'/', b'/') => Kind::SlashSlash,
                (b'=', b'=') => Kind::EqEq,
                (b'~', b'=') => Kind::TildeEq,
                (b'<', b'=') => Kind::LtEq,
                (b'>', b'=') => Kind::GtEq,
                (b':', b':') => Kind::ColonColon,
                _ => Kind::EOF,
            };
            if kind != Kind::EOF {
                self.token(kind, self.p + 2);
                continue;
            }

            // One-character operators and punctuation.
            let kind = match b {
                b'+' => Kind::Plus,
                b'-' => Kind::Minus,
                b'*' => Kind::Star,
                b'/' => Kind::Slash,
                b'%' => Kind::Percent,
                b'^' => Kind::Caret,
                b'#' => Kind::Hash,
                b'&' => Kind::Amp,
                b'~' => Kind::Tilde,
                b'|' => Kind::Pipe,
                b'<' => Kind::Lt,
                b'>' => Kind::Gt,
                b'=' => Kind::Eq,
                b'(' => Kind::LParen,
                b')' => Kind::RParen,
                b'{' => Kind::LBrace,
                b'}' => Kind::RBrace,
                b']' => Kind::RBrack,
                b':' => Kind::Colon,
                b';' => Kind::Semi,
                b',' => Kind::Comma,
                _ => Kind::EOF,
            };
            if kind != Kind::EOF {
                self.token(kind, self.p + 1);
                continue;
            }

            // Dots.
            if b == b'.' {
                if bnext == b'.' {
                    if self.p + 2 < self.data.len() && self.data[self.p + 2] == b'.' {
                        self.token(kind, self.p + 3);
                        continue;
                    }
                    self.token(Kind::DotDot, self.p + 2);
                    continue;
                }
                self.token(Kind::Dot, self.p + 1);
                continue;
            }

            // Identifiers and keywords.
            if is_ident_first(b) {
                let mut end = self.p + 1;
                while end < self.data.len() && is_ident(self.data[end]) {
                    end += 1;
                }
                let text = unsafe { str::from_utf8_unchecked(&self.data[self.p..end]) };
                let kind = match text {
                    "and" => Kind::And,
                    "break" => Kind::Break,
                    "do" => Kind::Do,
                    "else" => Kind::Else,
                    "elseif" => Kind::Elseif,
                    "end" => Kind::End,
                    "false" => Kind::False,
                    "for" => Kind::For,
                    "function" => Kind::Function,
                    "goto" => Kind::Goto,
                    "if" => Kind::If,
                    "in" => Kind::In,
                    "local" => Kind::Local,
                    "nil" => Kind::Nil,
                    "not" => Kind::Not,
                    "or" => Kind::Or,
                    "repeat" => Kind::Repeat,
                    "then" => Kind::Then,
                    "true" => Kind::True,
                    "until" => Kind::Until,
                    "while" => Kind::While,
                    _ => Kind::Ident,
                };
                self.token(kind, end);
                continue;
            }

            // Numbers and related punctuation.
            if b == b'0' && (bnext == b'x' || bnext == b'X') {
                let mut end = self.p + 2;
                let mut have_int = false;
                while end < self.data.len() && is_hex_digit(self.data[end]) {
                    end += 1;
                    have_int = true;
                }
                if !have_int {
                    self.error_end(
                        end,
                        format!(
                            "unrecognized token, possibly the beginning of a hexidecimal number"
                        ),
                    );
                    continue;
                }

                if end < self.data.len() && self.data[end] == b'.' {
                    end += 1;
                    let mut have_fract = false;
                    while end < self.data.len() && is_hex_digit(self.data[end]) {
                        end += 1;
                        have_fract = true;
                    }
                    if !have_fract {
                        self.error_end(
                            end,
                            format!("hexadecimal floating-point literal has empty fraction"),
                        );
                        continue;
                    }
                }

                if end < self.data.len() && self.data[end] == b'P' || self.data[end] == b'p' {
                    end += 1;
                    let mut have_exp = false;
                    if end < self.data.len() && self.data[end] == b'+' || self.data[end] == b'-' {
                        end += 1;
                    }
                    while end < self.data.len() && is_hex_digit(self.data[end]) {
                        end += 1;
                        have_exp = true;
                    }
                    if !have_exp {
                        self.error_end(
                            end,
                            format!("hexadecimal floating-point literal has empty exponent"),
                        );
                        continue;
                    }
                }
                self.token(Kind::Number, end);
                continue;
            }

            if is_digit(b) {
                let mut end = self.p + 1;
                while end < self.data.len() && is_digit(self.data[end]) {
                    end += 1;
                }
                if end < self.data.len() && self.data[end] == b'.' {
                    end += 1;
                    let mut have_fract = false;
                    while end < self.data.len() && is_digit(self.data[end]) {
                        end += 1;
                        have_fract = true;
                    }
                    if !have_fract {
                        self.error_end(end, format!("floating-point literal has empty fraction"));
                        continue;
                    }
                }
                if end < self.data.len() && (self.data[end] == b'E' || self.data[end] == b'e') {
                    end += 1;
                    if end < self.data.len() && (self.data[end] == b'+' || self.data[end] == b'-') {
                        end += 1;
                    }
                    let mut have_exp = false;
                    while end < self.data.len() && is_digit(self.data[end]) {
                        end += 1;
                        have_exp = true;
                    }
                    if !have_exp {
                        self.error_end(end, format!("floating-point literal has empty exponent"));
                        continue;
                    }
                }
                self.token(Kind::Number, end);
                continue;
            }

            if b == b'"' || b == b'\'' {
                let mut end = self.p + 1;
                let mut escape = false;
                let mut terminated = false;
                while end < self.data.len() && !terminated {
                    let sb = self.data[end];
                    end += 1;
                    if sb == b'\n' {
                        self.lmap.add_line(end);
                    }
                    if escape == true {
                        escape = false;
                    } else if sb == b'\\' {
                        escape = true;
                    } else if sb == b {
                        terminated = true;
                    }
                }
                if !terminated {
                    self.error_end(end, format!("unterminated string constant"));
                    continue;
                }
                self.token(Kind::String, end);
                continue;
            }

            if b == b'[' {
                let mut level = 0;
                let mut end = self.p + 1;
                while end < self.data.len() && self.data[end] == b'=' {
                    end += 1;
                    level += 1;
                }
                if end < self.data.len() && self.data[end] == b'[' {
                    end += 1;
                    let mut terminated = false;
                    let mut maybe_terminating = false;
                    let mut term_level = 0;
                    while end < self.data.len() && !terminated {
                        let sb = self.data[end];
                        end += 1;
                        if sb == b'\n' {
                            self.lmap.add_line(end);
                        }
                        if !maybe_terminating && sb == b']' {
                            maybe_terminating = true;
                            term_level = 0;
                        } else if maybe_terminating {
                            if sb == b'=' {
                                term_level += 1;
                            } else if sb == b']' {
                                if term_level == level {
                                    terminated = true;
                                } else {
                                    maybe_terminating = false;
                                }
                            }
                        }
                    }
                    if !terminated {
                        self.error_end(end, format!("unterminated string constant"));
                        continue;
                    }
                    self.token(Kind::String, end);
                    continue;
                }
                self.token(Kind::LBrack, self.p + 1);
                while level > 1 {
                    self.token(Kind::EqEq, self.p + 2);
                }
                if level > 0 {
                    self.token(Kind::Eq, self.p + 1);
                }
                continue;
            }

            self.error(format!("unrecognized character: '{}'", b as char));
        }
    }

    fn token(&mut self, kind: Kind, end: usize) {
        self.tokens.push(Token {
            kind,
            text: unsafe { str::from_utf8_unchecked(&self.data[self.p..end]) },
            offset: self.base + self.p,
        });
        self.p = end;
    }

    fn error(&mut self, message: String) {
        self.error_end(self.base + self.p + 1, message);
    }

    fn error_end(&mut self, end: usize, message: String) {
        let begin = self.base + self.p;
        let pos = Pos {
            begin,
            end: self.base + end,
        };
        let position = self.lmap.position(pos);
        self.errors.push(Error { position, message });
        while self.p < self.data.len() && !is_space(self.data[self.p]) && self.data[self.p] != b'\n'
        {
            self.p += 1;
        }
    }
}

fn is_space(b: u8) -> bool {
    const VTAB: u8 = 11;
    const FORMFEED: u8 = 12;
    b == b' ' || b == VTAB || b == FORMFEED || b == b'\r' || b == b'\t'
}

fn is_ident_first(b: u8) -> bool {
    b'A' <= b && b <= b'Z' || b'a' <= b && b <= b'z' || b == b'_'
}

fn is_ident(b: u8) -> bool {
    is_ident_first(b) || is_digit(b)
}

fn is_digit(b: u8) -> bool {
    b'0' <= b && b <= b'9'
}

fn is_hex_digit(b: u8) -> bool {
    is_digit(b) || b'A' <= b && b <= b'F' || b'a' <= b && b <= b'f'
}
