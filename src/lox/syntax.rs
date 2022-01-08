use crate::lox::token::{Kind, Token};
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
    Expr(Expr<'a>),
    Block(Box<Block<'a>>),
    Print {
        expr: Expr<'a>,
        begin_pos: Pos,
        end_pos: Pos,
    },
    If {
        cond: Expr<'a>,
        true_stmt: Box<Stmt<'a>>,
        false_stmt: Option<Box<Stmt<'a>>>,
        begin_pos: Pos,
    },
    While {
        cond: Expr<'a>,
        body: Box<Stmt<'a>>,
        begin_pos: Pos,
    },
    For {
        init: ForInit<'a>,
        cond: Option<Expr<'a>>,
        incr: Option<Expr<'a>>,
        body: Box<Stmt<'a>>,
        begin_pos: Pos,
    },
    Return {
        expr: Option<Expr<'a>>,
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
            Stmt::If {
                begin_pos,
                true_stmt,
                false_stmt,
                ..
            } => match false_stmt {
                Some(b) => (*begin_pos, b.pos().1),
                None => (*begin_pos, true_stmt.pos().1),
            },
            Stmt::While {
                begin_pos, body, ..
            } => (*begin_pos, body.pos().1),
            Stmt::For {
                begin_pos, body, ..
            } => (*begin_pos, body.pos().1),
            Stmt::Return {
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
            Stmt::If {
                cond,
                true_stmt,
                false_stmt,
                ..
            } => {
                f.write_str("if (")?;
                cond.fmt(f)?;
                f.write_str(") ")?;
                true_stmt.fmt_indent(f, level)?;
                if let Some(false_stmt) = false_stmt {
                    f.write_str(" else ")?;
                    false_stmt.fmt_indent(f, level)?;
                }
                Ok(())
            }
            Stmt::While { cond, body, .. } => {
                f.write_str("while (")?;
                cond.fmt(f)?;
                f.write_str("? ")?;
                body.fmt_indent(f, level)
            }
            Stmt::For {
                init,
                cond,
                incr,
                body,
                ..
            } => {
                f.write_str("for (")?;
                init.fmt(f)?;
                f.write_str("; ")?;
                if let Some(cond) = cond {
                    cond.fmt(f)?;
                }
                f.write_str("; ")?;
                if let Some(incr) = incr {
                    incr.fmt(f)?;
                }
                f.write_str(") ")?;
                body.fmt_indent(f, level)
            }
            Stmt::Return { expr, .. } => match expr {
                Some(expr) => {
                    write!(f, "return {};", expr)
                }
                None => f.write_str("return;"),
            },
        }
    }
}

impl<'a> Display for Stmt<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_indent(f, 0)
    }
}

pub enum ForInit<'a> {
    Var(Box<Decl<'a>>),
    Expr(Expr<'a>),
    None,
}

impl<'a> Display for ForInit<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ForInit::Var(decl) => decl.fmt(f),
            ForInit::Expr(expr) => expr.fmt(f),
            ForInit::None => Ok(()),
        }
    }
}

pub enum Expr<'a> {
    Nil(Token<'a>),
    Bool(Token<'a>),
    Number(Token<'a>),
    String(Token<'a>),
    Var(Token<'a>),
    Group {
        expr: Box<Expr<'a>>,
        begin_pos: Pos,
        end_pos: Pos,
    },
    Call {
        callee: Box<Expr<'a>>,
        arguments: Vec<Expr<'a>>,
        end_pos: Pos,
    },
    Unary(Token<'a>, Box<Expr<'a>>),
    Binary(Box<Expr<'a>>, Token<'a>, Box<Expr<'a>>),
    Assign(LValue<'a>, Box<Expr<'a>>),
}

impl<'a> Expr<'a> {
    pub fn pos(&self) -> (Pos, Pos) {
        match self {
            Expr::Nil(t) => (t.from, t.to),
            Expr::Bool(t) => (t.from, t.to),
            Expr::Number(t) => (t.from, t.to),
            Expr::String(t) => (t.from, t.to),
            Expr::Var(t) => (t.from, t.to),
            Expr::Group {
                begin_pos, end_pos, ..
            } => (*begin_pos, *end_pos),
            Expr::Call {
                callee, end_pos, ..
            } => (callee.pos().0, *end_pos),
            Expr::Unary(op, e) => (op.from, e.pos().1),
            Expr::Binary(l, _, r) => (l.pos().0, r.pos().0),
            Expr::Assign(l, r) => (l.pos().0, r.pos().1),
        }
    }
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Nil(_) => f.write_str("nil"),
            Expr::Bool(t) => f.write_str(t.text),
            Expr::Number(t) => f.write_str(t.text),
            Expr::String(t) => f.write_str(t.text),
            Expr::Var(t) => f.write_str(t.text),
            Expr::Group { expr, .. } => write!(f, "({})", expr),
            Expr::Call {
                callee, arguments, ..
            } => {
                callee.fmt(f)?;
                f.write_str("(")?;
                let mut sep = "";
                for arg in arguments {
                    f.write_str(sep)?;
                    sep = ", ";
                    arg.fmt(f)?;
                }
                f.write_str(")")
            }
            Expr::Unary(op, e) => write!(f, "{}{}", op.text, e),
            Expr::Binary(l, op, r) => write!(f, "{} {} {}", l, op.text, r),
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
        tokens,
        lmap,
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
                Kind::EOF => break,
                _ => decls.push(self.parse_decl()?),
            }
        }
        Ok(File { decls: decls })
    }

    fn parse_decl(&mut self) -> Result<Decl<'a>, Error> {
        let type_ = self.peek();
        match type_ {
            Kind::Var => self.parse_var_decl(),
            Kind::Fun => self.parse_function_decl(),
            _ => self.parse_stmt().map(|stmt| Decl::Stmt(stmt)),
        }
    }

    fn parse_var_decl(&mut self) -> Result<Decl<'a>, Error> {
        let begin_pos = self.expect(Kind::Var)?.from;
        let name = self.expect(Kind::Ident)?;
        let type_ = self.peek();
        let init = match type_ {
            Kind::Assign => {
                self.take();
                let init = self.parse_expr()?;
                Some(init)
            }
            Kind::Semi => None,
            _ => return Err(self.error(format!("expected '=' or ';', found {}", type_))),
        };
        let end_pos = self.expect(Kind::Semi)?.to;
        Ok(Decl::Var {
            name,
            init,
            begin_pos,
            end_pos,
        })
    }

    fn parse_function_decl(&mut self) -> Result<Decl<'a>, Error> {
        let begin_pos = self.expect(Kind::Fun)?.from;
        let name = self.expect(Kind::Ident)?;
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
        self.expect(Kind::LParen)?;
        let mut param_names = Vec::new();
        let mut first = true;
        while self.peek() != Kind::RParen {
            if first {
                first = false;
            } else {
                self.expect(Kind::Comma)?;
            }
            param_names.push(self.expect(Kind::Ident)?);
        }
        self.expect(Kind::RParen)?;
        Ok(param_names)
    }

    fn parse_block(&mut self) -> Result<Block<'a>, Error> {
        let begin_pos = self.expect(Kind::LBrace)?.from;
        let mut decls = Vec::new();
        while self.peek() != Kind::RBrace {
            decls.push(self.parse_decl()?);
        }
        let end_pos = self.expect(Kind::RBrace)?.to;
        Ok(Block {
            decls,
            begin_pos,
            end_pos,
        })
    }

    fn parse_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        match self.peek() {
            Kind::Print => self.parse_print_stmt(),
            Kind::LBrace => Ok(Stmt::Block(Box::new(self.parse_block()?))),
            Kind::If => self.parse_if_stmt(),
            Kind::While => self.parse_while_stmt(),
            Kind::For => self.parse_for_stmt(),
            Kind::Return => self.parse_return_stmt(),
            _ => self.parse_expr_stmt(),
        }
    }

    fn parse_expr_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        let e = self.parse_expr()?;
        self.expect(Kind::Semi)?;
        Ok(Stmt::Expr(e))
    }

    fn parse_print_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        let begin_pos = self.expect(Kind::Print)?.from;
        let expr = self.parse_expr()?;
        let end_pos = self.expect(Kind::Semi)?.to;
        Ok(Stmt::Print {
            expr,
            begin_pos,
            end_pos,
        })
    }

    fn parse_if_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        let begin_pos = self.expect(Kind::If)?.from;
        self.expect(Kind::LParen)?;
        let cond = self.parse_expr()?;
        self.expect(Kind::RParen)?;
        let true_stmt = Box::new(self.parse_stmt()?);
        let false_stmt = if self.peek() == Kind::Else {
            self.take();
            Some(Box::new(self.parse_stmt()?))
        } else {
            None
        };
        Ok(Stmt::If {
            cond,
            true_stmt,
            false_stmt,
            begin_pos,
        })
    }

    fn parse_while_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        let begin_pos = self.expect(Kind::While)?.from;
        self.expect(Kind::LParen)?;
        let cond = self.parse_expr()?;
        self.expect(Kind::RParen)?;
        let body = Box::new(self.parse_stmt()?);
        Ok(Stmt::While {
            cond,
            body,
            begin_pos,
        })
    }

    fn parse_for_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        let begin_pos = self.expect(Kind::For)?.from;
        self.expect(Kind::LParen)?;
        let init = match self.peek() {
            Kind::Var => ForInit::Var(Box::new(self.parse_var_decl()?)),
            Kind::Semi => {
                self.take();
                ForInit::None
            }
            _ => {
                let init = ForInit::Expr(self.parse_expr()?);
                self.expect(Kind::Semi)?;
                init
            }
        };
        let cond = match self.peek() {
            Kind::Semi => None,
            _ => Some(self.parse_expr()?),
        };
        self.expect(Kind::Semi)?;
        let incr = match self.peek() {
            Kind::RParen => None,
            _ => Some(self.parse_expr()?),
        };
        self.expect(Kind::RParen)?;
        let body = Box::new(self.parse_stmt()?);
        Ok(Stmt::For {
            init,
            cond,
            incr,
            body,
            begin_pos,
        })
    }

    fn parse_return_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        let begin_pos = self.expect(Kind::Return)?.from;
        let expr = if self.peek() == Kind::Semi {
            None
        } else {
            Some(self.parse_expr()?)
        };
        let end_pos = self.expect(Kind::Semi)?.to;
        Ok(Stmt::Return {
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
        if can_assign && self.peek() == Kind::Assign {
            return Err(self.error(format!("invalid assignment")));
        }

        Ok(e)
    }

    fn parse_group_expr(&mut self, _: bool) -> Result<Expr<'a>, Error> {
        let begin_pos = self.expect(Kind::LParen)?.from;
        let expr = Box::new(self.parse_expr()?);
        let end_pos = self.expect(Kind::RParen)?.to;
        Ok(Expr::Group {
            expr,
            begin_pos,
            end_pos,
        })
    }

    fn parse_call_expr(&mut self, callee: Expr<'a>, _: bool) -> Result<Expr<'a>, Error> {
        self.expect(Kind::LParen)?;
        let mut arguments = Vec::new();
        if self.peek() != Kind::RParen {
            loop {
                arguments.push(self.parse_expr()?);
                if self.peek() != Kind::Comma {
                    break;
                }
                self.take();
            }
        }
        let end_pos = self.expect(Kind::RParen)?.to;
        Ok(Expr::Call {
            callee: Box::new(callee),
            arguments,
            end_pos,
        })
    }

    fn parse_unary_expr(&mut self, _: bool) -> Result<Expr<'a>, Error> {
        let op = self.tokens[self.next];
        match op.type_ {
            Kind::Minus | Kind::Bang => (),
            _ => return Err(self.error(format!("expected expression, found {}", op.type_))),
        };
        self.take();
        let e = Box::new(self.parse_precedence(Precedence::Unary)?);
        Ok(Expr::Unary(op, e))
    }

    fn parse_binary_expr(&mut self, l: Expr<'a>, _: bool) -> Result<Expr<'a>, Error> {
        let rule = self.get_rule(self.peek());
        if rule.precedence == Precedence::None {
            return Err(self.error(format!(
                "expected binary operator, '.', or '(', but found {}",
                self.peek()
            )));
        }
        let op = self.take();
        let r = self.parse_precedence(rule.precedence.next())?;
        Ok(Expr::Binary(Box::new(l), op, Box::new(r)))
    }

    fn parse_var_expr(&mut self, can_assign: bool) -> Result<Expr<'a>, Error> {
        let t = self.expect(Kind::Ident)?;
        if can_assign && self.peek() == Kind::Assign {
            let l = LValue::Var(t);
            self.take();
            let r = self.parse_expr()?;
            Ok(Expr::Assign(l, Box::new(r)))
        } else {
            Ok(Expr::Var(t))
        }
    }

    fn parse_nil_expr(&mut self, _: bool) -> Result<Expr<'a>, Error> {
        Ok(Expr::Nil(self.expect(Kind::Nil)?))
    }

    fn parse_bool_expr(&mut self, _: bool) -> Result<Expr<'a>, Error> {
        Ok(Expr::Bool(self.expect(Kind::Bool)?))
    }

    fn parse_num_expr(&mut self, _: bool) -> Result<Expr<'a>, Error> {
        Ok(Expr::Number(self.expect(Kind::Number)?))
    }

    fn parse_string_expr(&mut self, _: bool) -> Result<Expr<'a>, Error> {
        Ok(Expr::String(self.expect(Kind::String)?))
    }

    fn get_rule<'d>(&self, type_: Kind) -> ParseRule<'a, 'b, 'c, 'd> {
        match type_ {
            Kind::LParen => ParseRule {
                prefix: Some(&Parser::parse_group_expr),
                infix: Some(&Parser::parse_call_expr),
                precedence: Precedence::Call,
            },
            Kind::Eq | Kind::Ne => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binary_expr),
                precedence: Precedence::Equality,
            },
            Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binary_expr),
                precedence: Precedence::Comparison,
            },
            Kind::Plus => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binary_expr),
                precedence: Precedence::Term,
            },
            Kind::Minus => ParseRule {
                prefix: Some(&Parser::parse_unary_expr),
                infix: Some(&Parser::parse_binary_expr),
                precedence: Precedence::Term,
            },
            Kind::Star | Kind::Slash => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binary_expr),
                precedence: Precedence::Factor,
            },
            Kind::Bang => ParseRule {
                prefix: Some(&Parser::parse_unary_expr),
                infix: None,
                precedence: Precedence::None,
            },
            Kind::Nil => ParseRule {
                prefix: Some(&Parser::parse_nil_expr),
                infix: None,
                precedence: Precedence::None,
            },
            Kind::Bool => ParseRule {
                prefix: Some(&Parser::parse_bool_expr),
                infix: None,
                precedence: Precedence::None,
            },
            Kind::Number => ParseRule {
                prefix: Some(&Parser::parse_num_expr),
                infix: None,
                precedence: Precedence::None,
            },
            Kind::String => ParseRule {
                prefix: Some(&Parser::parse_string_expr),
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

    fn expect(&mut self, want: Kind) -> Result<Token<'a>, Error> {
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

    fn peek(&self) -> Kind {
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
    _Or,
    _And,
    Equality,
    Comparison,
    Term,
    Factor,
    Unary,
    Call,
    Primary,
}

impl Precedence {
    fn next(self) -> Precedence {
        match self {
            Precedence::_Or => Precedence::_And,
            Precedence::_And => Precedence::Equality,
            Precedence::Equality => Precedence::Comparison,
            Precedence::Comparison => Precedence::Term,
            Precedence::Term => Precedence::Factor,
            Precedence::Factor => Precedence::Unary,
            Precedence::Unary => Precedence::Call,
            Precedence::Call => Precedence::Primary,
            _ => unreachable!(),
        }
    }
}
