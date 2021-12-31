use crate::lox::token::{Token, Type};
use crate::pos::{Error, LineMap};
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
    Function {
        name: Token<'a>,
        param_names: Vec<Token<'a>>,
        body: Block<'a>,
    },
}

impl<'a> Display for Decl<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Decl::Function {
                name,
                param_names,
                body,
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
        }
    }
}

pub struct Block<'a> {
    pub stmts: Vec<Stmt<'a>>,
}

impl<'a> Block<'a> {
    fn fmt_indent(&self, f: &mut fmt::Formatter<'_>, level: usize) -> fmt::Result {
        f.write_str("{\n")?;
        for stmt in &self.stmts {
            stmt.fmt_indent(f, level + 1)?;
            f.write_str(";\n")?;
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
    Print(Box<Expr<'a>>),
}

impl<'a> Stmt<'a> {
    fn fmt_indent(&self, f: &mut fmt::Formatter<'_>, level: usize) -> fmt::Result {
        for _ in 0..level {
            f.write_str("  ")?;
        }
        match self {
            Stmt::Expr(e) => e.fmt(f),
            Stmt::Print(e) => {
                f.write_str("print ")?;
                e.fmt(f)
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
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Bool(t) => f.write_str(t.text),
            Expr::Number(t) => f.write_str(t.text),
        }
    }
}

pub fn parse<'a>(tokens: &[Token<'a>], lmap: &LineMap) -> Result<File<'a>, Error> {
    let mut p = Parser {
        tokens: tokens,
        tset: lmap,
        next: 0,
    };
    p.parse_file()
}

struct Parser<'a, 'b, 'c> {
    tokens: &'b [Token<'a>],
    tset: &'c LineMap,
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
            Type::Function => self.parse_function(),
            _ => Err(self.error(format!("expected declaration, found {}", type_))),
        }
    }

    fn parse_function(&mut self) -> Result<Decl<'a>, Error> {
        self.expect(Type::Function)?;
        let name = self.expect(Type::Ident)?;
        let param_names = self.parse_params()?;
        let body = self.parse_block()?;
        Ok(Decl::Function {
            name,
            param_names,
            body,
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
        self.expect(Type::LBrace)?;
        let mut stmts = Vec::new();
        while self.peek() != Type::RBrace {
            stmts.push(self.parse_stmt()?);
        }
        self.expect(Type::RBrace)?;
        Ok(Block { stmts })
    }

    fn parse_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        match self.peek() {
            Type::Print => self.parse_print_stmt(),
            _ => self.parse_expr_stmt(),
        }
    }

    fn parse_expr_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        let e = self.parse_expr()?;
        self.expect(Type::Semi)?;
        Ok(Stmt::Expr(Box::new(e)))
    }

    fn parse_print_stmt(&mut self) -> Result<Stmt<'a>, Error> {
        self.expect(Type::Print)?;
        let e = self.parse_expr()?;
        self.expect(Type::Semi)?;
        Ok(Stmt::Print(Box::new(e)))
    }

    fn parse_expr(&mut self) -> Result<Expr<'a>, Error> {
        let type_ = self.peek();
        match type_ {
            Type::Bool => Ok(Expr::Bool(self.take())),
            Type::Number => Ok(Expr::Number(self.take())),
            _ => Err(self.error(format!("expected expression, found {}", type_))),
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
        let position = self.tset.position(t.from, t.to);
        Error { position, message }
    }
}
