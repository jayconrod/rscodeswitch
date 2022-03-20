use codeswitch::pos::{Error, LineMap, Pos};
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
/// lex appends any errors it finds to the given list and returns the tokens it
/// was able to read. lex attempts to recover after an error by skipping
/// characters until after whitespace.
pub fn lex<'src>(
    path: &Path,
    data: &'src [u8],
    lmap: &mut LineMap,
    errors: &mut Vec<Error>,
) -> Vec<Token<'src>> {
    let mut l = Lexer::new(path, data, lmap);
    l.lex();
    errors.extend(l.errors);
    l.tokens
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
            if b == b'\n' {
                self.p += 1;
                self.lmap.add_line(self.base + self.p);
                continue;
            }
            if is_space(b) {
                self.p += 1;
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

            // "..." operator.
            if b == b'.'
                && bnext == b'.'
                && self.p + 2 < self.data.len()
                && self.data[self.p + 2] == b'.'
            {
                self.token(Kind::DotDotDot, self.p + 3);
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
                    "return" => Kind::Return,
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
                while end < self.data.len() && self.data[end].is_ascii_hexdigit() {
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
                    while end < self.data.len() && self.data[end].is_ascii_hexdigit() {
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
                    while end < self.data.len() && self.data[end].is_ascii_hexdigit() {
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

            if b.is_ascii_digit() {
                let mut end = self.p + 1;
                while end < self.data.len() && self.data[end].is_ascii_digit() {
                    end += 1;
                }
                if end < self.data.len() && self.data[end] == b'.' {
                    end += 1;
                    let mut have_fract = false;
                    while end < self.data.len() && self.data[end].is_ascii_digit() {
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
                    while end < self.data.len() && self.data[end].is_ascii_digit() {
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

        self.token(Kind::EOF, self.p);
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
    b == b' ' || b == VTAB || b == FORMFEED || b == b'\r' || b == b'\t' || b == b'\n'
}

fn is_ident_first(b: u8) -> bool {
    b'A' <= b && b <= b'Z' || b'a' <= b && b <= b'z' || b == b'_'
}

fn is_ident(b: u8) -> bool {
    is_ident_first(b) || b.is_ascii_digit()
}

fn decode_hex_digit(b: u8) -> u8 {
    if b'0' <= b && b <= b'9' {
        b - b'0'
    } else if b'A' <= b && b <= b'F' {
        b - b'A' + 10
    } else if b'a' <= b && b <= b'f' {
        b - b'a' + 10
    } else {
        panic!("not a hex digit")
    }
}

/// Decodes a Lua string into a sequence of bytes, translating any escape
/// sequences and applying other lexical rules. The string may be a short
/// string (delimited by quotes) or a long string (delimited by brackets and
/// equal signs). Returns None if the string is malformed.
pub fn unquote_string(s: &str) -> Option<Vec<u8>> {
    if s.starts_with('[') {
        unquote_long_string(s)
    } else {
        unquote_short_string(s)
    }
}

fn unquote_short_string(s: &str) -> Option<Vec<u8>> {
    let sb = s.as_bytes();
    let mut buf = Vec::new();
    buf.reserve(sb.len());

    // Check quotes: short strings must begin and end with the same character,
    // either ' or ".
    if sb.len() < 2 || sb[0] != sb[sb.len() - 1] {
        return None;
    }
    let q = sb[0];
    if q != b'\'' && q != b'"' {
        return None;
    }

    let eos = sb.len() - 1;
    let mut p = 1;
    while p < eos {
        let mut bs = p;
        while bs < eos {
            if sb[bs] == b'\n' || sb[bs] == b'\r' {
                // Unescaped newline.
                return None;
            }
            if sb[bs] == b'\\' {
                break;
            }
            bs += 1;
        }
        buf.extend_from_slice(&sb[p..bs]);
        p = bs;
        if bs == eos {
            break;
        }

        // Escape
        p += 1;
        if p == eos {
            return None;
        }

        // Single-character escapes
        let c = match sb[p] {
            b'a' => b'\x07', // BEL
            b'b' => b'\x08', // backspace
            b'f' => b'\x0c', // formfeed
            b'n' => b'\n',   // newline
            b'r' => b'\r',   // carriage return
            b't' => b'\t',   // tab
            b'v' => b'\x0b', // vertical tab
            b'\\' => b'\\',
            b'\'' => b'\'',
            b'"' => b'"',
            b'\n' => b'\n',
            _ => 0,
        };
        if c != 0 {
            buf.push(c);
            p += 1;
            continue;
        }

        // Skip whitespace
        if sb[p] == b'z' {
            p += 1;
            while p < eos && is_space(sb[p]) {
                p += 1;
            }
            continue;
        }

        // Hexadecimal byte: exactly two digits.
        if sb[p] == b'x' {
            p += 1;
            if p + 1 >= eos || !sb[p].is_ascii_hexdigit() || !sb[p + 1].is_ascii_hexdigit() {
                return None;
            }
            let h = (decode_hex_digit(sb[p]) << 4) | decode_hex_digit(sb[p + 1]);
            buf.push(h);
            p += 2;
            continue;
        }

        // Decimal byte: up to three digits.
        if b'0' <= sb[p] && sb[p] <= b'9' {
            let mut end = p + 1;
            let mut n = (sb[p] - b'0') as u16;
            while end < eos && end < p + 3 && sb[end].is_ascii_digit() {
                n = n * 10 + (sb[end] - b'0') as u16;
                end += 1;
            }
            if n >= 256 {
                return None;
            }
            buf.push(n as u8);
            p = end;
            continue;
        }

        // Unicode character: Lua uses an older UTF-8 encoding that allows
        // code points up to 2^31. Rust doesn't support code points beyond
        // U+10FFFF, so we need to encode them here manually.
        if sb[p] == b'u' {
            if p + 3 >= eos || sb[p + 1] != b'{' {
                return None;
            }
            let mut end = p + 2;
            let mut n: u32 = 0;
            while end < sb.len() - 2 && end < p + 10 && sb[end].is_ascii_hexdigit() {
                n = (n << 4) | decode_hex_digit(sb[end]) as u32;
                end += 1;
            }
            if end == p + 2 || sb[end] != b'}' || n >= (1 << 31) {
                return None;
            }
            p = end + 1;

            let (first, count) = if n < 0x80 {
                (n as u8, 1)
            } else if n < 0x800 {
                (0xC0 | ((n >> 6) & 0x1F) as u8, 2)
            } else if n < 0x10000 {
                (0xE0 | ((n >> 12) & 0xF) as u8, 3)
            } else if n < 0x200000 {
                (0xF0 | ((n >> 18) & 0x7) as u8, 4)
            } else if n < 0x4000000 {
                (0xF8 | ((n >> 24) & 0x3) as u8, 5)
            } else {
                (0xFC | ((n >> 30) & 0x1) as u8, 6)
            };
            buf.push(first);
            for i in 1..count {
                let shift = 6 * (count - i - 1);
                let mask = (1 << 6) - 1;
                let b = 0x80 | ((n >> shift) & mask) as u8;
                buf.push(b);
            }
            continue;
        }

        // Invalid escape.
        return None;
    }
    Some(buf)
}

fn unquote_long_string(s: &str) -> Option<Vec<u8>> {
    let sb = s.as_bytes();
    let mut buf = Vec::new();

    // Check delimiters. A long string begins with "[[", "[=[", "[==[", or so on
    // (with any number of equal signs) and ends with "]]", "]=]", "]==]" or so
    // on, with a matching number of equal signs.
    if sb.len() < 4 || sb[0] != b'[' {
        return None;
    }
    let mut level = 0;
    while 1 + level < sb.len() && sb[1 + level] == b'=' {
        level += 1;
    }
    if sb.len() < 4 + 2 * level
        || sb[1 + level] != b'['
        || sb[sb.len() - 1] != b']'
        || sb[sb.len() - level - 2] != b']'
    {
        return None;
    }
    for p in sb.len() - level - 1..sb.len() - 1 {
        if sb[p] != b'=' {
            return None;
        }
    }

    // Process characters inside the string.
    // A newline immediately after the opening delimiter is ignored.
    // The sequences CR, CR LF, and LF CR are translated to LF.
    // All other characters are interpreted literally.
    let delim = sb.len() - 2 - level;
    let mut p = 2 + level;
    if sb[p] == b'\n' {
        p += 1;
    } else if sb[p] == b'\r' && sb[p + 1] == b'\n' {
        p += 2;
    }
    while p < delim {
        let (b1, b2) = (sb[p], sb[p + 1]);
        if (b1 == b'\r' && b2 == b'\n') || (b1 == b'\n' && b2 == b'\r') {
            buf.push(b'\n');
            p += 2;
        } else if b1 == b'\r' {
            buf.push(b'\n');
            p += 1;
        } else {
            buf.push(b1);
            p += 1;
        }
    }
    Some(buf)
}

#[derive(Debug, PartialEq)]
pub enum Number {
    Malformed,
    Int(i64),
    Float(f64),
}

/// Converts a string representing an integer or floating-point number to a
/// Lua number. Lua supports 64-bit signed integers and 64-bit floating point
/// numbers. If an integer literal can't be represented in 64 bits, it's
/// interpreted as a floating point number instead.
///
/// convert_number supports leading signs to help with the implementation of
/// tonumber. However, the lexer treats a leading sign as a separate token,
/// so that functionality isn't needed for numbers in source code.
pub fn convert_number(s: &str) -> Number {
    let sb = s.as_bytes();
    let mut p = 0;
    let mut sign: &[u8] = &sb[0..0];
    let whole: &[u8];
    let mut frac = &sb[0..0];
    let mut is_float = false;
    let mut exp_neg = false;
    let mut exp = &sb[0..0];
    let mut radix = 10;

    if sb.len() > 0 && (sb[0] == b'-' || sb[0] == b'+') {
        sign = &sb[0..1];
        p += 1;
    }

    if sb.len() >= p + 2 && sb[p] == b'0' && (sb[p + 1] == b'x' || sb[p + 1] == b'X') {
        radix = 16;
        p += 2;

        let mut end = p;
        while end < sb.len() && sb[end].is_ascii_hexdigit() {
            end += 1;
        }
        whole = &sb[p..end];
        p = end;

        if p < sb.len() && sb[p] == b'.' {
            is_float = true;
            end = p + 1;
            while end < sb.len() && sb[end].is_ascii_hexdigit() {
                end += 1;
            }
            frac = &sb[p + 1..end];
            p = end;
        }

        if p < sb.len() && (sb[p] == b'P' || sb[p] == b'p') {
            is_float = true;
            p += 1;
            if p == sb.len() {
                return Number::Malformed;
            }
            if sb[p] == b'-' {
                exp_neg = true;
                p += 1;
            } else if sb[p] == b'+' {
                p += 1;
            }
            if p == sb.len() {
                return Number::Malformed;
            }
            for b in &sb[p..] {
                if !b.is_ascii_hexdigit() {
                    return Number::Malformed;
                }
            }
            exp = &sb[p..];
            p = sb.len();
        }
    } else {
        let mut end = p;
        while end < sb.len() && sb[end].is_ascii_digit() {
            end += 1;
        }
        whole = &sb[p..end];
        p = end;

        if p < sb.len() && sb[p] == b'.' {
            is_float = true;
            end = p + 1;
            while end < sb.len() && sb[end].is_ascii_digit() {
                end += 1;
            }
            frac = &sb[p + 1..end];
            p = end;
        }

        if p < sb.len() && (sb[p] == b'E' || sb[p] == b'e') {
            is_float = true;
            p += 1;
            if p == sb.len() {
                return Number::Malformed;
            }
            if sb[p] == b'-' {
                exp_neg = true;
                p += 1;
            } else if sb[p] == b'+' {
                p += 1;
            }
            if p == sb.len() {
                return Number::Malformed;
            }
            for b in &sb[p..] {
                if !b.is_ascii_digit() {
                    return Number::Malformed;
                }
            }
            exp = &sb[p..];
            p = sb.len();
        }
    }

    if p < sb.len() {
        return Number::Malformed;
    }

    let sign = unsafe { str::from_utf8_unchecked(sign) };
    let whole = unsafe { str::from_utf8_unchecked(whole) };
    let frac = unsafe { str::from_utf8_unchecked(frac) };
    let exp = unsafe { str::from_utf8_unchecked(exp) };
    if !is_float {
        let res = if radix == 10 {
            i64::from_str_radix(str::from_utf8(sb).unwrap(), radix)
        } else {
            let without_0x = format!("{}{}", sign, whole);
            i64::from_str_radix(&without_0x, radix)
        };
        if let Ok(n) = res {
            return Number::Int(n);
        }
        // If the number doesn't fit in i64, fall through and treat it as
        // a floating point number.
    }

    // Ideally, we'd build the bits for f64 here, but that's really
    // complicated, and I don't want to. "How to Read Floating Point Numbers
    // Accurately" by Clinger seems to be the correct reference.
    if radix == 16 {
        // TODO: parse this properly. The hack below does not work for
        // hexadecimal numbers.
        return Number::Malformed;
    }
    let fs = if exp.is_empty() {
        format!("{}{}.{}", sign, whole, frac)
    } else {
        format!(
            "{}{}.{}e{}{}",
            sign,
            whole,
            frac,
            if exp_neg { "-" } else { "" },
            exp
        )
    };
    match fs.parse::<f64>() {
        Ok(n) => Number::Float(n),
        _ => Number::Malformed,
    }
}
