use crate::lox::token::{Token, Type};
use crate::pos::{Error, LineMap, Pos};
use std::boxed::Box;
use std::fmt;
use std::fmt::Display;

pub struct File<'a> {
    pub decls: Vec<Decl<'a>>,
}

impl<'a> Display for File<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut sep = "";
        for decl in &self.decls {
            decl.fmt(f)?;
            f.write_str(sep)?;
            sep = "\n\n";
        }
        Ok(())
    }
}

pub enum Decl<'a> {
    Var {
        name: Token<'a>,
        init: Option<Expr<'a>>,
        begin_pos: Pos,
        end_pos: Pos,
    },
    Function {
        name: Token<'a>,
        param_names: Vec<Token<'a>>,
        body: Block<'a>,
        begin_pos: Pos,
        end_pos: Pos,
    },
    Stmt(Stmt<'a>),
}

impl<'a> Decl<'a> {
    pub fn name(&self) -> Option<Token<'a>> {
        match self {
            Decl::Var { name, .. } => Some(*name),
            Decl::Function { name, .. } => Some(*name),
            Decl::Stmt(_) => None,
        }
    }

    pub fn pos(&self) -> (Pos, Pos) {
        match self {
            Decl::Var {
                begin_pos, end_pos, ..
            } => (*begin_pos, *end_pos),
            Decl::Function {
                begin_pos, end_pos, ..
            } => (*begin_pos, *end_pos),
            Decl::Stmt(stmt) => stmt.pos(),
        }
    }
}

impl<'a> Decl<'a> {
    fn fmt_indent(&self, f: &mut fmt::Formatter<'_>, level: usize) -> fmt::Result {
        for _ in 0..level {
            f.write_str("  ")?;
        }
        match self {
            Decl::Var { name, init, .. } => {
                f.write_str("var ")?;
                f.write_str(name.text)?;
                if let Some(e) = init {
                    f.write_str(" = ")?;
                    e.fmt(f)?;
                }
                f.write_str(";")
            }
            Decl::Function {
                name,
                param_names,
                body,
                ..
            } => {
                f.write_str("function ")?;
                f.write_str(name.text)?;
                f.write_str("(")?;
                let mut sep = "";
                for param_name in param_names {
                    f.write_str(sep)?;
                    sep = ", ";
                    f.write_str(param_name.text)?;
                }
                f.write_str(") ")?;
                body.fmt(f)
            }
            Decl::Stmt(stmt) => stmt.fmt(f),
        }
    }
}

impl<'a> Display for Decl<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_indent(f, 0)
    }
}

pub struct Block<'a> {
    pub decls: Vec<Decl<'a>>,
    pub begin_pos: Pos,
    pub end_pos: Pos,
}

impl<'a> Block<'a> {
    fn pos(&self) -> (Pos, Pos) {
        (self.begin_pos, self.end_pos)
    }

    fn fmt_indent(&self, f: &mut fmt::Formatter<'_>, level: usize) -> fmt::Result {
        f.write_str("{\n")?;
        for decl in &self.decls {
            decl.fmt_indent(f, level + 1)?;
        }
        for _ in 0..level {
            f.write_str("  ")?;
        }
        f.write_str("}")
    }
}

impl<'a> Display for Block<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_indent(f, 0)
    }
}

pub enum Stmt<'a> {
    Expr(Box<Expr<'a>>),
    Block(Box<Block<'a>>),
    Print {
        expr: Box<Expr<'a>>,
        begin_pos: Pos,
        end_pos: Pos,
    },
}

impl<'a> Stmt<'a> {
    fn pos(&self) -> (Pos, Pos) {
        match self {
            Stmt::Expr(e) => e.pos(),
            Stmt::Block(b) => b.pos(),
            Stmt::Print {
                begin_pos, end_pos, ..
            } => (*begin_pos, *end_pos),
        }
    }
}

impl<'a> Stmt<'a> {
    fn fmt_indent(&self, f: &mut fmt::Formatter<'_>, level: usize) -> fmt::Result {
        for _ in 0..level {
            f.write_str("  ")?;
        }
        match self {
            Stmt::Expr(e) => e.fmt(f),
            Stmt::Block(b) => b.fmt_indent(f, level),
            Stmt::Print { expr, .. } => {
                f.write_str("print ")?;
                expr.fmt(f)
            }
        }
    }
}

impl<'a> Display for Stmt<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_indent(f, 0)
    }
}

pub enum Expr<'a> {
    Bool(Token<'a>),
    Number(Token<'a>),
    Var(Token<'a>),
    Assign(LValue<'a>, Box<Expr<'a>>),
}

impl<'a> Expr<'a> {
    fn pos(&self) -> (Pos, Pos) {
        match self {
            Expr::Bool(t) => (t.from, t.to),
            Expr::Number(t) => (t.from, t.to),
            Expr::Var(t) => (t.from, t.to),
            Expr::Assign(l, r) => (l.pos().0, r.pos().1),
        }
    }
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Bool(t) => f.write_str(t.text),
            Expr::Number(t) => f.write_str(t.text),
            Expr::Var(t) => f.write_str(t.text),
            Expr::Assign(l, r) => write!(f, "{} = {}", l, r),
        }
    }
}

pub enum LValue<'a> {
    Var(Token<'a>),
}

impl<'a> LValue<'a> {
    fn pos(&self) -> (Pos, Pos) {
        match self {
            LValue::Var(t) => (t.from, t.to),
        }
    }
}

impl<'a> Display for LValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LValue::Var(t) => f.write_str(t.text),
        }
    }
}

pub fn parse<'a>(tokens: &[Token<'a>], lmap: &LineMap) -> Result<File<'a>, Error> {
    let mut p = Parser {
        tokens: tokens,
        lmap: lmap,
        next: 0,
    };
    p.parse_file()
}

struct Parser<'a, 'b, 'c> {
    tokens: &'b [Token<'a>],
    lmap: &'c LineMap,
    next: usize,
}

impl<'a, 'b, 'c> Parser<'a, 'b, 'c> {
    fn parse_file(&mut self) -> Result<File<'a>, Error> {
        let mut decls = Vec::new();
        loop {
            match self.peek() {
                Type::EOF => break,
                _ => decls.push(self.parse_decl()?),
            }
        }
        Ok(File { decls: decls })
    }

    fn parse_decl(&mut self) -> Result<Decl<'a>, Error> {
        let type_ = self.peek();
        match type_ {
            Type::Var => self.parse_var_decl(),
            Type::Function => self.parse_function_decl(),
            _ => self.parse_stmt().map(|stmt| Decl::Stmt(stmt)),
        }
    }

    fn parse_var_decl(&mut self) -> Result<Decl<'a>, Error> {
        let begin_pos = self.expect(Type::Var)?.from;
        let name = self.expect(Type::Ident)?;
        let type_ = self.peek();
        let init = match type_ {
            Type::Assign => {
                self.take();
                let init = self.parse_expr()?;
                Some(init)
            }
            Type::Semi => None,
            _ => return Err(self.error(format!("expected '=' or ';', found {}", type_))),
        };
        let end_pos = self.expect(Type::Semi)?.to;
        Ok(Decl::Var {
            name,
            init,
            begin_pos,
            end_pos,
        })
    }

    fn parse_function_decl(&mut self) -> Result<Decl<'a>, Error> {
        let begin_pos = self.expect(Type::Function)?.from;
        let name = self.expect(Type::Ident)?;
        let param_names = self.parse_params()?;
        let body = self.parse_block()?;
        let end_pos = body.pos().1;
        Ok(Decl::Function {
            name,
            param_names,
            body,
            begin_pos,
            end_pos,
        })
    }

    fn parse_params(&mut self) -> Result<Vec<Token<'a>>, Error> {
        self.expect(Type::LParen)?;
        let mut param_names = Vec::new();
        let mut first = true;
        while self.peek() != Type::RParen {
            if first {
                first = false;
            } else {
                self.expect(Type::Comma)?;
            }
            param_names.push(self.expect(Type::Ident)?);
        }
        self.expect(Type::RParen)?;
        Ok(param_names)
    }

    fn parse_block(&mut self) -> Result<Block<'a>, Error> {
        let begin_pos = self.expect(Type::LBrace)?.from;
        let mut decls = Vec::new();
        while self.peek() != Type::RBrace {
            decls.push(self.parse_decl()?);
        }
        let end_pos = self.expect(Type::RBrace)?.to;
        Ok(Block {
            decls,
            begin_pos,
            end_pos,
        })
    }

    fn parse_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        match self.peek() {
            Type::Print => self.parse_print_stmt(),
            Type::LBrace => Ok(Stmt::Block(Box::new(self.parse_block()?))),
            _ => self.parse_expr_stmt(),
        }
    }

    fn parse_expr_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        let e = self.parse_expr()?;
        self.expect(Type::Semi)?;
        Ok(Stmt::Expr(Box::new(e)))
    }

    fn parse_print_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        let begin_pos = self.expect(Type::Print)?.from;
        let expr = Box::new(self.parse_expr()?);
        let end_pos = self.expect(Type::Semi)?.to;
        Ok(Stmt::Print {
            expr,
            begin_pos,
            end_pos,
        })
    }

    fn parse_expr(&mut self) -> Result<Expr<'a>, Error> {
        self.parse_precedence(Precedence::Assignment)
    }

    fn parse_precedence(&mut self, prec: Precedence) -> Result<Expr<'a>, Error> {
        let can_assign = prec <= Precedence::Assignment;
        let t = self.tokens[self.next];
        let rule = self.get_rule(t.type_);
        let mut e = match rule.prefix {
            Some(prefix) => prefix(self, can_assign),
            None => Err(self.error(format!("expected expression, found {}", t.type_))),
        }?;

        loop {
            let rule = self.get_rule(self.peek());
            if prec > rule.precedence {
                break;
            }
            e = rule.infix.unwrap()(self, e, can_assign)?;
        }
        if can_assign && self.peek() == Type::Assign {
            return Err(self.error(format!("invalid assignment")));
        }

        Ok(e)
    }

    fn parse_var_expr(&mut self, can_assign: bool) -> Result<Expr<'a>, Error> {
        let t = self.expect(Type::Ident)?;
        if can_assign && self.peek() == Type::Assign {
            let l = LValue::Var(t);
            self.take();
            let r = self.parse_expr()?;
            Ok(Expr::Assign(l, Box::new(r)))
        } else {
            Ok(Expr::Var(t))
        }
    }

    fn parse_bool_expr(&mut self, _: bool) -> Result<Expr<'a>, Error> {
        Ok(Expr::Bool(self.expect(Type::Bool)?))
    }

    fn parse_num_expr(&mut self, _: bool) -> Result<Expr<'a>, Error> {
        Ok(Expr::Number(self.expect(Type::Number)?))
    }

    fn get_rule<'d>(&self, type_: Type) -> ParseRule<'a, 'b, 'c, 'd> {
        match type_ {
            Type::Bool => ParseRule {
                prefix: Some(&Parser::parse_bool_expr),
                infix: None,
                precedence: Precedence::None,
            },
            Type::Number => ParseRule {
                prefix: Some(&Parser::parse_num_expr),
                infix: None,
                precedence: Precedence::None,
            },
            Type::Ident => ParseRule {
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

    fn expect(&mut self, want: Type) -> Result<Token<'a>, Error> {
        let got = self.tokens[self.next];
        if got.type_ != want {
            return Err(self.error(format!("expected {}, found {}", want, got.type_)));
        }
        self.next += 1;
        Ok(got)
    }

    fn take(&mut self) -> Token<'a> {
        let t = self.tokens[self.next];
        self.next += 1;
        t
    }

    fn peek(&self) -> Type {
        self.tokens[self.next].type_
    }

    fn error(&self, message: String) -> Error {
        let t = &self.tokens[self.next];
        let position = self.lmap.position(t.from, t.to);
        Error { position, message }
    }
}

#[derive(Clone, Copy)]
struct ParseRule<'a, 'b, 'c, 'd> {
    prefix: Option<&'d dyn Fn(&'d mut Parser<'a, 'b, 'c>, bool) -> Result<Expr<'a>, Error>>,
    infix:
        Option<&'d dyn Fn(&'d mut Parser<'a, 'b, 'c>, Expr<'a>, bool) -> Result<Expr<'a>, Error>>,
    precedence: Precedence,
}

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
enum Precedence {
    None,
    Assignment,
}
