use crate::lua::token::{Kind, Token};
use crate::pos::{Error, LineMap, Pos};

use std::fmt::{self, Display, Formatter};

trait DisplayIndent {
    fn fmt_indent(&self, f: &mut Formatter, level: usize) -> fmt::Result;

    fn write_indent(&self, f: &mut Formatter, level: usize) -> fmt::Result {
        for _ in 0..level {
            f.write_str("  ")?;
        }
        Ok(())
    }
}

pub struct Chunk<'src> {
    pub stmts: Vec<Stmt<'src>>,
    pub scope: ScopeID,
    pub env_var: VarID,
}

impl<'src> Chunk<'src> {
    pub fn pos(&self) -> Pos {
        if self.stmts.is_empty() {
            Pos::default()
        } else {
            self.stmts[0]
                .pos()
                .combine(self.stmts[self.stmts.len() - 1].pos())
        }
    }
}

impl<'src> DisplayIndent for Chunk<'src> {
    fn fmt_indent(&self, f: &mut Formatter, level: usize) -> fmt::Result {
        for stmt in &self.stmts {
            stmt.fmt_indent(f, level)?;
        }
        Ok(())
    }
}

impl<'src> Display for Chunk<'src> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt_indent(f, 0)
    }
}

pub enum Stmt<'src> {
    Empty(Pos),
    Assign {
        left: Vec<LValue<'src>>,
        right: Vec<Expr<'src>>,
    },
    Local {
        left: Vec<NameAttr<'src>>,
        right: Vec<Expr<'src>>,
        pos: Pos,
    },
    // TODO: Remove this construct after standard library calls are supported.
    // This is a hack to enable debugging and testing.
    Print {
        expr: Expr<'src>,
    },
}

impl<'src> Stmt<'src> {
    pub fn pos(&self) -> Pos {
        match self {
            Stmt::Empty(pos) => *pos,
            Stmt::Assign { left, right } => {
                let begin = left.first().unwrap().pos();
                let end = right.last().unwrap().pos();
                begin.combine(end)
            }
            Stmt::Local { pos, .. } => *pos,
            Stmt::Print { expr, .. } => expr.pos(),
        }
    }
}

impl<'src> DisplayIndent for Stmt<'src> {
    fn fmt_indent(&self, f: &mut Formatter, level: usize) -> fmt::Result {
        self.write_indent(f, level)?;
        match self {
            Stmt::Empty(_) => write!(f, ";"),
            Stmt::Assign { left, right, .. } => {
                let mut sep = "";
                for lval in left {
                    write!(f, "{}{}", sep, lval)?;
                    sep = ", ";
                }
                write!(f, " = ")?;
                sep = "";
                for expr in right {
                    write!(f, "{}{}", sep, expr)?;
                    sep = ", ";
                }
                Ok(())
            }
            Stmt::Local { left, right, .. } => {
                write!(f, "local ")?;
                let mut sep = "";
                for l in left {
                    write!(f, "{}{}", sep, l)?;
                    sep = ", ";
                }
                write!(f, " = ")?;
                sep = "";
                for r in right {
                    write!(f, "{}{}", sep, r)?;
                    sep = ", ";
                }
                Ok(())
            }
            Stmt::Print { expr, .. } => write!(f, "print({})", expr),
        }
    }
}

impl<'src> Display for Stmt<'src> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt_indent(f, 0)
    }
}

pub struct NameAttr<'src> {
    pub name: Token<'src>,
    pub attr: Option<Token<'src>>,
    pub var: VarID,
    pub pos: Pos,
}

impl<'src> Display for NameAttr<'src> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.name.text)?;
        if let Some(a) = self.attr {
            write!(f, "<{}>", a.text)?;
        }
        Ok(())
    }
}

pub enum Expr<'src> {
    Literal(Token<'src>),
    Var {
        name: Token<'src>,
        var_use: VarUseID,
    },
}

impl<'src> Expr<'src> {
    pub fn pos(&self) -> Pos {
        match self {
            Expr::Literal(t) => t.pos(),
            Expr::Var { name, .. } => name.pos(),
        }
    }
}

impl<'src> Display for Expr<'src> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Expr::Literal(t) => write!(f, "{}", t.text),
            Expr::Var { name, .. } => write!(f, "{}", name.text),
        }
    }
}

pub enum LValue<'src> {
    Var {
        name: Token<'src>,
        var_use: VarUseID,
    },
}

impl<'src> LValue<'src> {
    pub fn pos(&self) -> Pos {
        match self {
            LValue::Var { name, .. } => name.pos(),
        }
    }
}

impl<'src> Display for LValue<'src> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            LValue::Var { name, .. } => write!(f, "{}", name.text),
        }
    }
}

#[derive(Clone, Copy)]
pub struct ScopeID(pub usize);

#[derive(Clone, Copy)]
pub struct VarID(pub usize);

#[derive(Clone, Copy)]
pub struct VarUseID(pub usize);

pub fn parse<'src>(tokens: &[Token<'src>], lmap: &LineMap, errors: &mut Vec<Error>) -> Chunk<'src> {
    let mut parser = Parser::new(tokens, lmap);
    let chunk = parser.parse_chunk();
    errors.extend(parser.errors);
    chunk
}

struct Parser<'src, 'tok, 'lm> {
    tokens: &'tok [Token<'src>],
    lmap: &'lm LineMap,
    next: usize,
    next_scope: usize,
    next_var: usize,
    next_var_use: usize,
    errors: Vec<Error>,
}

impl<'src, 'tok, 'lm> Parser<'src, 'tok, 'lm> {
    fn new(tokens: &'tok [Token<'src>], lmap: &'lm LineMap) -> Parser<'src, 'tok, 'lm> {
        Parser {
            tokens,
            lmap,
            next: 0,
            next_scope: 0,
            next_var: 0,
            next_var_use: 0,
            errors: Vec::new(),
        }
    }

    fn parse_chunk(&mut self) -> Chunk<'src> {
        let scope = self.next_scope();
        let env_var = self.next_var();
        let stmts = self.parse_block_stmts(Kind::EOF);
        Chunk {
            stmts,
            scope,
            env_var,
        }
    }

    fn parse_block_stmts(&mut self, end: Kind) -> Vec<Stmt<'src>> {
        let mut stmts = Vec::new();
        while self.peek() != end {
            match self.parse_stmt() {
                Ok(stmt) => stmts.push(stmt),
                Err(err) => {
                    self.errors.push(err);
                    if !self.synchronize() {
                        break;
                    }
                }
            }
        }
        stmts
    }

    fn parse_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        match self.peek() {
            Kind::Semi => self.parse_empty_stmt(),
            Kind::Local => self.parse_local_stmt(),
            Kind::Ident => {
                if self.tokens[self.next].text == "print" {
                    self.take();
                    self.expect(Kind::LParen)?;
                    let expr = self.parse_expr()?;
                    self.expect(Kind::RParen)?;
                    return Ok(Stmt::Print { expr });
                }

                let e = self.parse_expr()?;
                match self.peek() {
                    Kind::Comma | Kind::Eq => {
                        let mut left_exprs = Vec::new();
                        left_exprs.push(e);
                        while self.peek() == Kind::Comma {
                            self.take();
                            left_exprs.push(self.parse_expr()?);
                        }
                        self.expect(Kind::Eq)?;
                        let mut right_exprs = Vec::new();
                        right_exprs.push(self.parse_expr()?);
                        while self.peek() == Kind::Comma {
                            self.take();
                            right_exprs.push(self.parse_expr()?);
                        }
                        let mut left_lvals = Vec::new();
                        for l in left_exprs {
                            match self.expr_to_lvalue(l) {
                                Ok(l) => {
                                    left_lvals.push(l);
                                }
                                Err(err) => {
                                    self.errors.push(err);
                                }
                            }
                        }
                        Ok(Stmt::Assign {
                            left: left_lvals,
                            right: right_exprs,
                        })
                    }
                    _ => Err(self.expect_error("',' or '='")),
                }
            }
            _ => Err(self.expect_error("statement")),
        }
    }

    fn parse_empty_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let t = self.expect(Kind::Semi)?;
        Ok(Stmt::Empty(t.pos()))
    }

    fn parse_local_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let begin = self.expect(Kind::Local)?.pos();
        let mut left = Vec::new();
        left.push(self.parse_name_attr()?);
        while self.peek() == Kind::Comma {
            self.take();
            left.push(self.parse_name_attr()?);
        }
        let mut right = Vec::new();
        let end = if self.peek() == Kind::Eq {
            self.take();
            right.push(self.parse_expr()?);
            while self.peek() == Kind::Comma {
                self.take();
                right.push(self.parse_expr()?);
            }
            right.last().unwrap().pos()
        } else {
            left.last().unwrap().pos
        };
        let pos = begin.combine(end);
        Ok(Stmt::Local { left, right, pos })
    }

    fn parse_name_attr(&mut self) -> Result<NameAttr<'src>, Error> {
        let var = self.next_var();
        let name = self.expect(Kind::Ident)?;
        let (attr, pos) = if self.peek() == Kind::Lt {
            self.take();
            let a = self.expect(Kind::Ident)?;
            let end = self.expect(Kind::Gt)?.pos();
            (Some(a), name.pos().combine(end))
        } else {
            (None, name.pos())
        };
        Ok(NameAttr {
            name,
            attr,
            var,
            pos,
        })
    }

    fn parse_expr(&mut self) -> Result<Expr<'src>, Error> {
        self.parse_precedence(Precedence::Primary)
    }

    fn parse_precedence(&mut self, prec: Precedence) -> Result<Expr<'src>, Error> {
        let rule = self.get_rule(self.peek());
        let mut e = match rule.prefix {
            Some(prefix) => prefix(self),
            None => Err(self.expect_error("expression")),
        }?;

        loop {
            let rule = self.get_rule(self.peek());
            if prec > rule.precedence {
                break;
            }
            e = rule.infix.unwrap()(self, e)?;
        }
        Ok(e)
    }

    fn parse_literal_expr(&mut self) -> Result<Expr<'src>, Error> {
        let kind = self.peek();
        match kind {
            Kind::Nil | Kind::True | Kind::False | Kind::Number | Kind::String => {
                Ok(Expr::Literal(self.take()))
            }
            _ => Err(self.expect_error("literal")),
        }
    }

    fn parse_var_expr(&mut self) -> Result<Expr<'src>, Error> {
        let var_use = self.next_var_use();
        let name = self.expect(Kind::Ident)?;
        Ok(Expr::Var { name, var_use })
    }

    fn expr_to_lvalue(&self, e: Expr<'src>) -> Result<LValue<'src>, Error> {
        match e {
            Expr::Var { name, var_use, .. } => Ok(LValue::Var { name, var_use }),
            _ => Err(self.error(format!(
                "expected variable or table field expression on left side of assignment"
            ))),
        }
    }

    fn get_rule<'p>(&self, kind: Kind) -> ParseRule<'src, 'tok, 'lm, 'p> {
        match kind {
            Kind::Nil | Kind::True | Kind::False | Kind::Number | Kind::String => ParseRule {
                prefix: Some(&Parser::parse_literal_expr),
                infix: None,
                precedence: Precedence::None,
            },
            Kind::Ident => ParseRule {
                prefix: Some(&Parser::parse_var_expr),
                infix: None,
                precedence: Precedence::None,
            },
            _ => ParseRule {
                prefix: None,
                infix: None,
                precedence: Precedence::None,
            },
        }
    }

    fn peek(&self) -> Kind {
        self.tokens[self.next].kind
    }

    fn expect(&mut self, want: Kind) -> Result<Token<'src>, Error> {
        if self.tokens[self.next].kind != want {
            return Err(self.error(format!(
                "expected {}, but found {}",
                want, self.tokens[self.next].kind
            )));
        }
        Ok(self.take())
    }

    fn take(&mut self) -> Token<'src> {
        let t = self.tokens[self.next];
        self.next += 1;
        t
    }

    fn expect_error(&self, want: &str) -> Error {
        self.error(format!(
            "expected {}, but found {}",
            want, self.tokens[self.next].kind
        ))
    }

    fn error(&self, message: String) -> Error {
        Error {
            position: self.lmap.position(self.tokens[self.next].pos()),
            message,
        }
    }

    /// Attempts to advance the parser past a syntax error, hopefully
    /// returning to a state in which the rest of the syntax tree
    /// can be parsed. synchronize reads and discards tokens until it
    /// finds a token on a new line or a token that could begin a statement.
    /// synchronize returns true if it succeeds, or false if it reaches
    /// the end of the file.
    fn synchronize(&mut self) -> bool {
        let error_line = self.lmap.position(self.tokens[self.next].pos()).end_line;
        while self.peek() != Kind::EOF {
            let t = self.take();
            let line = self.lmap.position(t.pos()).begin_line;
            if line != error_line {
                return true;
            }
        }
        return false;
    }

    fn next_scope(&mut self) -> ScopeID {
        let id = self.next_scope;
        self.next_scope += 1;
        ScopeID(id)
    }

    fn next_var(&mut self) -> VarID {
        let id = self.next_var;
        self.next_var += 1;
        VarID(id)
    }

    fn next_var_use(&mut self) -> VarUseID {
        let id = self.next_var_use;
        self.next_var_use += 1;
        VarUseID(id)
    }
}

#[derive(Clone, Copy)]
struct ParseRule<'src, 'tok, 'lm, 'p> {
    prefix: Option<&'p dyn Fn(&'p mut Parser<'src, 'tok, 'lm>) -> Result<Expr<'src>, Error>>,
    infix: Option<
        &'p dyn Fn(&'p mut Parser<'src, 'tok, 'lm>, Expr<'src>) -> Result<Expr<'src>, Error>,
    >,
    precedence: Precedence,
}

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
enum Precedence {
    None,
    Primary,
}
