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
    Do {
        stmts: Vec<Stmt<'src>>,
        scope: ScopeID,
        pos: Pos,
    },
    If {
        cond_stmts: Vec<(Expr<'src>, Stmt<'src>)>,
        false_stmt: Option<Box<Stmt<'src>>>,
        pos: Pos,
    },
    While {
        cond: Expr<'src>,
        body: Vec<Stmt<'src>>,
        scope: ScopeID,
        break_label: LabelID,
        pos: Pos,
    },
    Repeat {
        body: Vec<Stmt<'src>>,
        cond: Expr<'src>,
        scope: ScopeID,
        break_label: LabelID,
        pos: Pos,
    },
    For {
        name: Token<'src>,
        init: Expr<'src>,
        limit: Expr<'src>,
        step: Option<Expr<'src>>,
        body: Vec<Stmt<'src>>,
        ind_scope: ScopeID,
        body_scope: ScopeID,
        ind_var: VarID,
        limit_var: VarID,
        step_var: VarID,
        body_var: VarID,
        break_label: LabelID,
        pos: Pos,
    },
    Break {
        label_use: LabelUseID,
        pos: Pos,
    },
    Label {
        name: Token<'src>,
        label: LabelID,
        pos: Pos,
    },
    Goto {
        name: Token<'src>,
        label_use: LabelUseID,
        pos: Pos,
    },
    Function {
        name: FunctionName<'src>,
        parameters: Vec<Param<'src>>,
        is_variadic: bool,
        body: Vec<Stmt<'src>>,
        param_scope: ScopeID,
        body_scope: ScopeID,
        pos: Pos,
    },
    LocalFunction {
        name: Token<'src>,
        parameters: Vec<Param<'src>>,
        is_variadic: bool,
        body: Vec<Stmt<'src>>,
        var: VarID,
        param_scope: ScopeID,
        body_scope: ScopeID,
        pos: Pos,
    },
    Call(Call<'src>),
    Return {
        exprs: Vec<Expr<'src>>,
        pos: Pos,
    },
    // TODO: Remove this construct after standard library calls are supported.
    // This is a hack to enable debugging and testing.
    Print {
        exprs: Vec<Expr<'src>>,
        pos: Pos,
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
            Stmt::Do { pos, .. } => *pos,
            Stmt::If { pos, .. } => *pos,
            Stmt::While { pos, .. } => *pos,
            Stmt::Repeat { pos, .. } => *pos,
            Stmt::For { pos, .. } => *pos,
            Stmt::Break { pos, .. } => *pos,
            Stmt::Label { pos, .. } => *pos,
            Stmt::Goto { pos, .. } => *pos,
            Stmt::Function { pos, .. } => *pos,
            Stmt::LocalFunction { pos, .. } => *pos,
            Stmt::Call(Call { pos, .. }) => *pos,
            Stmt::Return { pos, .. } => *pos,
            Stmt::Print { pos, .. } => *pos,
        }
    }

    fn fmt_function_parameters_and_body(
        &self,
        f: &mut Formatter,
        parameters: &[Param<'src>],
        is_variadic: bool,
        body: &[Stmt<'src>],
        level: usize,
    ) -> fmt::Result {
        let mut sep = "";
        for p in parameters {
            write!(f, "{}{}", sep, p.name.text)?;
            sep = ", ";
        }
        if is_variadic {
            write!(f, "{}...", sep)?;
        }
        write!(f, ")\n")?;
        for stmt in body {
            stmt.fmt_indent(f, level + 1)?;
            write!(f, "\n")?;
        }
        self.write_indent(f, level)?;
        write!(f, "end")
    }

    fn write_expr_list(
        &self,
        f: &mut Formatter,
        exprs: &[Expr<'src>],
        level: usize,
    ) -> fmt::Result {
        let mut sep = "";
        for expr in exprs {
            write!(f, "{}", sep)?;
            sep = ", ";
            expr.fmt_indent(f, level)?;
        }
        Ok(())
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
            Stmt::Do { stmts, .. } => {
                write!(f, "do\n")?;
                for stmt in stmts {
                    stmt.fmt_indent(f, level + 1)?;
                    write!(f, "\n")?;
                }
                self.write_indent(f, level)?;
                write!(f, "end")
            }
            Stmt::If {
                cond_stmts,
                false_stmt,
                ..
            } => {
                let mut sep = "if";
                for (cond, stmt) in cond_stmts {
                    write!(f, "{} {}", sep, cond)?;
                    sep = "\nelseif";
                    stmt.fmt_indent(f, level)?;
                }
                if let Some(false_stmt) = false_stmt {
                    write!(f, "\nelse ")?;
                    false_stmt.fmt_indent(f, level)?;
                }
                Ok(())
            }
            Stmt::While { cond, body, .. } => {
                write!(f, "while {} do\n", cond)?;
                for stmt in body {
                    stmt.fmt_indent(f, level + 1)?;
                    write!(f, "\n")?;
                }
                self.write_indent(f, level)?;
                write!(f, "end")
            }
            Stmt::Repeat { body, cond, .. } => {
                write!(f, "repeat\n")?;
                for stmt in body {
                    stmt.fmt_indent(f, level + 1)?;
                    write!(f, "\n")?;
                }
                self.write_indent(f, level)?;
                write!(f, "until {}", cond)
            }
            Stmt::For {
                name,
                init,
                limit,
                step,
                body,
                ..
            } => {
                write!(f, "for {} = {}, {}", name.text, init, limit)?;
                if let Some(step) = step {
                    write!(f, ", {}", step)?;
                }
                write!(f, " do\n")?;
                for stmt in body {
                    stmt.fmt_indent(f, level + 1)?;
                }
                self.write_indent(f, level)?;
                write!(f, "end")
            }
            Stmt::Break { .. } => write!(f, "break"),
            Stmt::Label { name, .. } => {
                write!(f, "::{}::", name.text)
            }
            Stmt::Goto { name, .. } => {
                write!(f, "goto {}", name.text)
            }
            Stmt::Function {
                name,
                parameters,
                is_variadic,
                body,
                ..
            } => {
                write!(f, "function {}(", name)?;
                self.fmt_function_parameters_and_body(f, parameters, *is_variadic, body, level)
            }
            Stmt::LocalFunction {
                name,
                parameters,
                is_variadic,
                body,
                ..
            } => {
                write!(f, "local function {}(", name.text)?;
                self.fmt_function_parameters_and_body(f, parameters, *is_variadic, body, level)
            }
            Stmt::Call(e) => e.fmt_indent(f, level),
            Stmt::Return { exprs, .. } => {
                write!(f, "return")?;
                let mut sep = " ";
                for expr in exprs {
                    write!(f, "{}{}", sep, expr)?;
                    sep = ", ";
                }
                Ok(())
            }
            Stmt::Print { exprs, .. } => {
                write!(f, "print(")?;
                self.write_expr_list(f, exprs, level)?;
                write!(f, ")")
            }
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

pub struct FunctionName<'src> {
    pub names: Vec<Token<'src>>,
    pub is_method: bool,
}

impl<'src> FunctionName<'src> {
    pub fn pos(&self) -> Pos {
        if self.names.len() == 1 {
            self.names[0].pos()
        } else {
            self.names
                .first()
                .unwrap()
                .pos()
                .combine(self.names.last().unwrap().pos())
        }
    }
}

impl<'src> Display for FunctionName<'src> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut sep = "";
        for (i, t) in self.names.iter().enumerate() {
            write!(f, "{}{}", sep, t.text)?;
            if i == self.names.len() - 2 && self.is_method {
                sep = ":";
            } else {
                sep = ".";
            }
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
    Unary(Token<'src>, Box<Expr<'src>>),
    Binary(Box<Expr<'src>>, Token<'src>, Box<Expr<'src>>),
    Group {
        expr: Box<Expr<'src>>,
        pos: Pos,
    },
    Function {
        parameters: Vec<Param<'src>>,
        is_variadic: bool,
        body: Vec<Stmt<'src>>,
        param_scope: ScopeID,
        body_scope: ScopeID,
        pos: Pos,
    },
    Call(Call<'src>),
    Table {
        fields: Vec<TableField<'src>>,
        pos: Pos,
    },
    Dot {
        expr: Box<Expr<'src>>,
        name: Token<'src>,
        pos: Pos,
    },
    Index {
        expr: Box<Expr<'src>>,
        index: Box<Expr<'src>>,
        pos: Pos,
    },
}

impl<'src> Expr<'src> {
    pub fn pos(&self) -> Pos {
        match self {
            Expr::Literal(t) => t.pos(),
            Expr::Var { name, .. } => name.pos(),
            Expr::Unary(op, expr) => op.pos().combine(expr.pos()),
            Expr::Binary(l, _, r) => l.pos().combine(r.pos()),
            Expr::Group { pos, .. } => *pos,
            Expr::Function { pos, .. } => *pos,
            Expr::Call(Call { pos, .. }) => *pos,
            Expr::Table { pos, .. } => *pos,
            Expr::Dot { pos, .. } => *pos,
            Expr::Index { pos, .. } => *pos,
        }
    }
}

impl<'src> Display for Expr<'src> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.fmt_indent(f, 0)
    }
}

impl<'src> DisplayIndent for Expr<'src> {
    fn fmt_indent(&self, f: &mut Formatter, level: usize) -> fmt::Result {
        match self {
            Expr::Literal(t) => write!(f, "{}", t.text),
            Expr::Var { name, .. } => write!(f, "{}", name.text),
            Expr::Unary(op, expr) => write!(f, "{}{}", op.text, expr),
            Expr::Binary(l, op, r) => write!(f, "{} {} {}", l, op.text, r),
            Expr::Group { expr, .. } => write!(f, "({})", expr),
            Expr::Function {
                parameters,
                is_variadic,
                body,
                ..
            } => {
                write!(f, "function(")?;
                let mut sep = "";
                for p in parameters {
                    write!(f, "{}{}", sep, p.name.text)?;
                    sep = ", ";
                }
                if *is_variadic {
                    write!(f, "{}...", sep)?;
                }
                write!(f, ")\n")?;
                self.write_indent(f, level + 1)?;
                for stmt in body {
                    stmt.fmt_indent(f, level + 1)?;
                    write!(f, "\n")?;
                }
                self.write_indent(f, level)?;
                write!(f, "end")
            }
            Expr::Call(call) => call.fmt_indent(f, level),
            Expr::Table { fields, .. } => {
                f.write_str("{")?;
                let mut sep = "";
                for field in fields {
                    write!(f, "{}", sep)?;
                    sep = ", ";
                    field.fmt_indent(f, level + 1)?;
                }
                f.write_str("}")
            }
            Expr::Dot { expr, name, .. } => {
                expr.fmt_indent(f, level)?;
                write!(f, ".{}", name.text)
            }
            Expr::Index { expr, index, .. } => {
                expr.fmt_indent(f, level)?;
                f.write_str("[")?;
                index.fmt_indent(f, level)?;
                f.write_str("]")
            }
        }
    }
}

pub struct Call<'src> {
    pub callee: Box<Expr<'src>>,
    pub method_name: Option<Token<'src>>,
    pub arguments: Vec<Expr<'src>>,
    pub pos: Pos,
}

impl<'src> DisplayIndent for Call<'src> {
    fn fmt_indent(&self, f: &mut Formatter, level: usize) -> fmt::Result {
        self.callee.fmt_indent(f, level)?;
        write!(f, "{}", self.callee)?;
        if let Some(method_name) = self.method_name {
            write!(f, ":{}", method_name.text)?;
        }
        match self.arguments[..] {
            [Expr::Literal(t)] if t.kind == Kind::String =>
                write!(f, "{}", t.text)
            ,
            // TODO: f {...} for single table constructor arg
            _ => {
                write!(f, "(")?;
                let mut sep = "";
                for a in &self.arguments {
                    write!(f, "{}", sep)?;
                    a.fmt_indent(f, level)?;
                    sep = ", ";
                }
                write!(f, ")")
            }
        }
    }
}

pub enum TableField<'src> {
    NameField(Token<'src>, Expr<'src>),
    ExprField(Expr<'src>, Expr<'src>),
    CountField(Expr<'src>),
}

impl<'src> DisplayIndent for TableField<'src> {
    fn fmt_indent(&self, f: &mut Formatter, level: usize) -> fmt::Result {
        match self {
            TableField::NameField(name, value) => {
                write!(f, "{} = ", name.text)?;
                value.fmt_indent(f, level)
            }
            TableField::ExprField(key, value) => {
                key.fmt_indent(f, level)?;
                f.write_str(" = ")?;
                value.fmt_indent(f, level)
            }
            TableField::CountField(value) => value.fmt_indent(f, level),
        }
    }
}

pub enum LValue<'src> {
    Var {
        name: Token<'src>,
        var_use: VarUseID,
    },
    Dot {
        expr: Expr<'src>,
        name: Token<'src>,
        pos: Pos,
    },
    Index {
        expr: Expr<'src>,
        index: Expr<'src>,
        pos: Pos,
    },
}

impl<'src> LValue<'src> {
    pub fn pos(&self) -> Pos {
        match self {
            LValue::Var { name, .. } => name.pos(),
            LValue::Dot { pos, .. } | LValue::Index { pos, .. } => *pos,
        }
    }
}

impl<'src> Display for LValue<'src> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            LValue::Var { name, .. } => write!(f, "{}", name.text),
            LValue::Dot { expr, name, .. } => write!(f, "{}.{}", expr, name.text),
            LValue::Index { expr, index, .. } => write!(f, "{}[{}]", expr, index),
        }
    }
}

pub struct Param<'src> {
    pub name: Token<'src>,
    pub var: VarID,
}

#[derive(Clone, Copy)]
pub struct ScopeID(pub usize);

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct VarID(pub usize);

#[derive(Clone, Copy)]
pub struct VarUseID(pub usize);

#[derive(Clone, Copy)]
pub struct LabelID(pub usize);

#[derive(Clone, Copy)]
pub struct LabelUseID(pub usize);

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
    next_label: usize,
    next_label_use: usize,
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
            next_label: 0,
            next_label_use: 0,
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
        let mut returned = false;
        for stmt in &stmts {
            if returned {
                self.errors.push(Error {
                    position: self.lmap.position(stmt.pos()),
                    message: String::from("statement not allowed in the same block after 'return'"),
                });
                break;
            }
            if let Stmt::Return { .. } = stmt {
                returned = true;
            }
        }
        stmts
    }

    fn parse_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        match self.peek() {
            Kind::Semi => self.parse_empty_stmt(),
            Kind::Local => self.parse_local_stmt(),
            Kind::Do => self.parse_do_stmt(),
            Kind::If => self.parse_if_stmt(),
            Kind::While => self.parse_while_stmt(),
            Kind::Repeat => self.parse_repeat_stmt(),
            Kind::For => self.parse_for_stmt(),
            Kind::Break => self.parse_break_stmt(),
            Kind::ColonColon => self.parse_label_stmt(),
            Kind::Goto => self.parse_goto_stmt(),
            Kind::Function => self.parse_function_stmt(),
            Kind::Return => self.parse_return_stmt(),
            Kind::Ident if self.tokens[self.next].text == "print" => {
                let begin = self.take().pos();
                self.expect(Kind::LParen)?;
                let exprs = self.parse_expr_list()?;
                let end = self.expect(Kind::RParen)?.pos();
                let pos = begin.combine(end);
                return Ok(Stmt::Print { exprs, pos });
            }
            _ => {
                let e = self.parse_expr()?;
                if self.peek() == Kind::Comma || self.peek() == Kind::Eq {
                    // Assignment
                    let mut left_exprs = Vec::new();
                    left_exprs.push(e);
                    while self.peek() == Kind::Comma {
                        self.take();
                        left_exprs.push(self.parse_expr()?);
                    }
                    self.expect(Kind::Eq)?;
                    let right_exprs = self.parse_non_empty_expr_list()?;
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
                } else if let Expr::Call(call) = e {
                    // Call statement
                    Ok(Stmt::Call(call))
                } else {
                    Err(self.expect_error("statement"))
                }
            }
        }
    }

    fn parse_empty_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let t = self.expect(Kind::Semi)?;
        Ok(Stmt::Empty(t.pos()))
    }

    fn parse_local_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let begin = self.expect(Kind::Local)?.pos();
        if self.peek() == Kind::Function {
            return self.parse_local_function_stmt(begin);
        }
        let mut left = Vec::new();
        left.push(self.parse_name_attr()?);
        while self.peek() == Kind::Comma {
            self.take();
            left.push(self.parse_name_attr()?);
        }
        let mut right = Vec::new();
        let end = if self.peek() == Kind::Eq {
            self.take();
            right = self.parse_non_empty_expr_list()?;
            right.last().unwrap().pos()
        } else {
            left.last().unwrap().pos
        };
        let pos = begin.combine(end);
        Ok(Stmt::Local { left, right, pos })
    }

    fn parse_local_function_stmt(&mut self, begin: Pos) -> Result<Stmt<'src>, Error> {
        let var = self.next_var();
        let param_scope = self.next_scope();
        let body_scope = self.next_scope();
        self.expect(Kind::Function)?;
        let name = self.expect(Kind::Ident)?;
        let (parameters, is_variadic, body, end) = self.parse_function_parameters_and_body()?;
        let pos = begin.combine(end);
        Ok(Stmt::LocalFunction {
            name,
            parameters,
            is_variadic,
            body,
            var,
            param_scope,
            body_scope,
            pos,
        })
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

    fn parse_do_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let scope = self.next_scope();
        let begin = self.expect(Kind::Do)?.pos();
        let stmts = self.parse_block_stmts(Kind::End);
        let end = self.expect(Kind::End)?.pos();
        let pos = begin.combine(end);
        Ok(Stmt::Do { stmts, scope, pos })
    }

    fn parse_if_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let begin = self.expect(Kind::If)?.pos();
        let mut cond_stmts = Vec::new();
        let true_cond = self.parse_expr()?;
        self.expect(Kind::Then)?;
        let true_stmt = self.parse_stmt()?;
        cond_stmts.push((true_cond, true_stmt));
        while self.peek() == Kind::Elseif {
            self.take();
            let cond = self.parse_expr()?;
            self.expect(Kind::Then)?;
            let stmt = self.parse_stmt()?;
            cond_stmts.push((cond, stmt));
        }
        let false_stmt = if self.peek() == Kind::Else {
            self.take();
            Some(Box::new(self.parse_stmt()?))
        } else {
            None
        };
        let end = self.expect(Kind::End)?.pos();
        let pos = begin.combine(end);
        Ok(Stmt::If {
            cond_stmts,
            false_stmt,
            pos,
        })
    }

    fn parse_while_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let scope = self.next_scope();
        let break_label = self.next_label();
        let begin = self.expect(Kind::While)?.pos();
        let cond = self.parse_expr()?;
        self.expect(Kind::Do)?;
        let body = self.parse_block_stmts(Kind::End);
        let end = self.expect(Kind::End)?.pos();
        let pos = begin.combine(end);
        Ok(Stmt::While {
            cond,
            body,
            scope,
            break_label,
            pos,
        })
    }

    fn parse_repeat_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let scope = self.next_scope();
        let break_label = self.next_label();
        let begin = self.expect(Kind::Repeat)?.pos();
        let body = self.parse_block_stmts(Kind::Until);
        self.expect(Kind::Until)?;
        let cond = self.parse_expr()?;
        let pos = begin.combine(cond.pos());
        Ok(Stmt::Repeat {
            body,
            cond,
            scope,
            break_label,
            pos,
        })
    }

    fn parse_for_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let ind_scope = self.next_scope();
        let body_scope = self.next_scope();
        let ind_var = self.next_var();
        let limit_var = self.next_var();
        let step_var = self.next_var();
        let body_var = self.next_var();
        let break_label = self.next_label();
        let begin = self.expect(Kind::For)?.pos();
        let name = self.expect(Kind::Ident)?;
        self.expect(Kind::Eq)?;
        let init = self.parse_expr()?;
        self.expect(Kind::Comma)?;
        let limit = self.parse_expr()?;
        let step = if self.peek() == Kind::Comma {
            self.take();
            Some(self.parse_expr()?)
        } else {
            None
        };
        self.expect(Kind::Do)?;
        let body = self.parse_block_stmts(Kind::End);
        let end = self.expect(Kind::End)?.pos();
        let pos = begin.combine(end);
        Ok(Stmt::For {
            name,
            init,
            limit,
            step,
            body,
            ind_scope,
            body_scope,
            ind_var,
            limit_var,
            step_var,
            body_var,
            break_label,
            pos,
        })
    }

    fn parse_break_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let label_use = self.next_label_use();
        let pos = self.expect(Kind::Break)?.pos();
        Ok(Stmt::Break { label_use, pos })
    }

    fn parse_label_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let label = self.next_label();
        let begin = self.expect(Kind::ColonColon)?.pos();
        let name = self.expect(Kind::Ident)?;
        let end = self.expect(Kind::ColonColon)?.pos();
        let pos = begin.combine(end);
        Ok(Stmt::Label { name, label, pos })
    }

    fn parse_goto_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let label_use = self.next_label_use();
        let begin = self.expect(Kind::Goto)?.pos();
        let name = self.expect(Kind::Ident)?;
        let pos = begin.combine(name.pos());
        Ok(Stmt::Goto {
            name,
            label_use,
            pos,
        })
    }

    fn parse_function_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let param_scope = self.next_scope();
        let body_scope = self.next_scope();
        let begin = self.expect(Kind::Function)?.pos();
        let name = self.parse_function_name()?;
        let (parameters, is_variadic, body, end) = self.parse_function_parameters_and_body()?;
        let pos = begin.combine(end);
        Ok(Stmt::Function {
            name,
            parameters,
            is_variadic,
            body,
            param_scope,
            body_scope,
            pos,
        })
    }

    fn parse_function_name(&mut self) -> Result<FunctionName<'src>, Error> {
        let mut names = Vec::new();
        names.push(self.expect(Kind::Ident)?);
        while self.peek() == Kind::Dot {
            self.take();
            names.push(self.expect(Kind::Ident)?);
        }
        let mut is_method = false;
        if self.peek() == Kind::Colon {
            is_method = true;
            self.take();
            names.push(self.expect(Kind::Ident)?);
        }
        Ok(FunctionName { names, is_method })
    }

    fn parse_return_stmt(&mut self) -> Result<Stmt<'src>, Error> {
        let begin = self.expect(Kind::Return)?.pos();
        let exprs = self.parse_expr_list()?;
        let end = if self.peek() == Kind::Semi {
            self.take().pos()
        } else if let Some(last) = exprs.last() {
            last.pos()
        } else {
            begin
        };
        let pos = begin.combine(end);
        Ok(Stmt::Return { exprs, pos })
    }

    fn parse_expr(&mut self) -> Result<Expr<'src>, Error> {
        self.parse_precedence(PREC_OR)
    }

    fn parse_expr_list(&mut self) -> Result<Vec<Expr<'src>>, Error> {
        let k = self.peek();
        if k == Kind::RParen || k == Kind::Semi || k == Kind::End || k == Kind::EOF {
            // In many contexts, the expression list may be empty, for example,
            // a function call with no arguments. Ideally, we'd match tokens
            // that can begin an expression, but there are a lot of them. None
            // of the above tokens can begin an expression, and one of them
            // should appear after an empty expression list, so we match them
            // instead.
            return Ok(Vec::new());
        }

        self.parse_non_empty_expr_list()
    }

    fn parse_non_empty_expr_list(&mut self) -> Result<Vec<Expr<'src>>, Error> {
        let mut exprs = Vec::new();
        exprs.push(self.parse_expr()?);
        while self.peek() == Kind::Comma {
            self.take();
            exprs.push(self.parse_expr()?);
        }
        Ok(exprs)
    }

    fn parse_precedence(&mut self, prec: Precedence) -> Result<Expr<'src>, Error> {
        // Use the next token to look up a prefix rule. A prefix rule is defined
        // for every token that can begin an expression, like identifiers,
        // literals, and unary operators.
        let rule = self.get_rule(self.peek());
        let mut e = match rule.prefix {
            Some(prefix) => prefix(self),
            None => Err(self.expect_error("expression")),
        }?;

        // Use the following token to look up an infix rule in order to parse
        // left-associative expressions. An infix rule is defined for every
        // token that can join expressions, like '(', '[', '.', and binary
        // operators.
        //
        // If the infix rule for the next token has lower precedence, return so
        // that a parse_precedence lower in the stack can parse the rest.
        // For example, in '2 * 3 + 4', with PREC_MUL, parse_precedence should
        // return '2 * 3', not reading past '+'.
        //
        // If there is no infix rule for the next token, get_rule returns a
        // dummy rule with PREC_NONE, which is the lowest precedence, so
        // we always stop there.
        loop {
            let rule = self.get_rule(self.peek());
            if prec > rule.precedence {
                break;
            }
            e = rule.infix.unwrap()(self, e)?;
        }
        Ok(e)
    }

    fn parse_table_expr(&mut self) -> Result<Expr<'src>, Error> {
        let begin = self.expect(Kind::LBrace)?.pos();
        let mut fields = Vec::new();
        while self.peek() != Kind::RBrace {
            fields.push(self.parse_table_field()?);
            if self.peek() == Kind::Comma || self.peek() == Kind::Semi {
                self.take();
            }
        }
        let end = self.expect(Kind::RBrace)?.pos();
        let pos = begin.combine(end);
        Ok(Expr::Table { fields, pos })
    }

    fn parse_table_field(&mut self) -> Result<TableField<'src>, Error> {
        match self.peek() {
            Kind::Ident => {
                let key = self.take();
                self.expect(Kind::Eq)?;
                let value = self.parse_expr()?;
                Ok(TableField::NameField(key, value))
            }
            Kind::LBrack => {
                self.take();
                let key = self.parse_expr()?;
                self.expect(Kind::RBrack)?;
                self.expect(Kind::Eq)?;
                let value = self.parse_expr()?;
                Ok(TableField::ExprField(key, value))
            }
            _ => {
                let value = self.parse_expr()?;
                Ok(TableField::CountField(value))
            }
        }
    }

    fn parse_call_expr(&mut self, callee: Expr<'src>) -> Result<Expr<'src>, Error> {
        let method_name = if self.peek() == Kind::Colon {
            self.take();
            Some(self.expect(Kind::Ident)?)
        } else {
            None
        };
        let mut arguments = Vec::new();
        let end = match self.peek() {
            Kind::String | Kind::LBrace => {
                let arg = self.parse_expr()?;
                let pos = arg.pos();
                arguments.push(arg);
                pos
            }
            Kind::LParen => {
                self.take();
                while self.peek() != Kind::RParen {
                    arguments.push(self.parse_expr()?);
                    if self.peek() == Kind::Comma {
                        self.take();
                    } else if self.peek() != Kind::RParen {
                        return Err(self.expect_error("',' or ')'"));
                    }
                }
                self.expect(Kind::RParen)?.pos()
            }
            _ => {
                return Err(
                    self.expect_error("function arguments starting with '(' or '{' or string")
                )
            }
        };
        let pos = callee.pos().combine(end);
        Ok(Expr::Call(Call {
            callee: Box::new(callee),
            method_name,
            arguments,
            pos,
        }))
    }

    fn parse_dot_expr(&mut self, expr: Expr<'src>) -> Result<Expr<'src>, Error> {
        let begin = expr.pos();
        self.expect(Kind::Dot)?;
        let name = self.expect(Kind::Ident)?;
        let pos = begin.combine(name.pos());
        Ok(Expr::Dot {
            expr: Box::new(expr),
            name,
            pos,
        })
    }

    fn parse_index_expr(&mut self, expr: Expr<'src>) -> Result<Expr<'src>, Error> {
        let begin = expr.pos();
        self.expect(Kind::LBrack)?;
        let index = self.parse_expr()?;
        let end = self.expect(Kind::RBrack)?.pos();
        let pos = begin.combine(end);
        Ok(Expr::Index {
            expr: Box::new(expr),
            index: Box::new(index),
            pos,
        })
    }

    fn parse_group_expr(&mut self) -> Result<Expr<'src>, Error> {
        let begin = self.expect(Kind::LParen)?.pos();
        let expr = self.parse_expr()?;
        let end = self.expect(Kind::RParen)?.pos();
        Ok(Expr::Group {
            expr: Box::new(expr),
            pos: begin.combine(end),
        })
    }

    fn parse_binop_expr(&mut self, left: Expr<'src>) -> Result<Expr<'src>, Error> {
        let rule = self.get_rule(self.peek());
        if rule.precedence == PREC_NONE {
            return Err(self.expect_error("binary operator, '.', or '('"));
        }
        let op = self.take();
        let next_prec = if associativity(rule.precedence) == Associativity::Right {
            // If this is a right-associative operator, recurse at the same
            // precedence level. For example, in 'a .. b .. c .. d', the first
            // time parse_binop_expr is called on the left-most '..' operator,
            // the recursive call will return 'b .. (c .. d)', not 'b.'.
            rule.precedence
        } else {
            // If this is a left-associative operator, recurse at a higher
            // precedence level. For example, in 'a + b + c + d', the first
            // time parse_binop_expr is called on the left-most '+' operator,
            // the recursive call with return 'b', not 'b + (c + d)'. The loop
            // in parse_precedence takes care of the rest.
            rule.precedence + 1
        };
        let right = Box::new(self.parse_precedence(next_prec)?);
        Ok(Expr::Binary(Box::new(left), op, right))
    }

    fn parse_unop_expr(&mut self) -> Result<Expr<'src>, Error> {
        let op = self.take();
        let expr = Box::new(self.parse_precedence(PREC_UNARY)?);
        Ok(Expr::Unary(op, expr))
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

    fn parse_function_expr(&mut self) -> Result<Expr<'src>, Error> {
        let param_scope = self.next_scope();
        let body_scope = self.next_scope();
        let begin = self.expect(Kind::Function)?.pos();
        let (parameters, is_variadic, body, end) = self.parse_function_parameters_and_body()?;
        let pos = begin.combine(end);
        Ok(Expr::Function {
            parameters,
            is_variadic,
            body,
            param_scope,
            body_scope,
            pos,
        })
    }

    fn parse_function_parameters_and_body(
        &mut self,
    ) -> Result<(Vec<Param<'src>>, bool, Vec<Stmt<'src>>, Pos), Error> {
        let (parameters, is_variadic) = self.parse_parameters()?;
        let body = self.parse_block_stmts(Kind::End);
        let end = self.expect(Kind::End)?.pos();
        Ok((parameters, is_variadic, body, end))
    }

    fn parse_parameters(&mut self) -> Result<(Vec<Param<'src>>, bool), Error> {
        self.expect(Kind::LParen)?;
        let mut parameters = Vec::new();
        let mut is_variadic = false;
        loop {
            match self.peek() {
                Kind::Ident => {
                    let var = self.next_var();
                    let name = self.expect(Kind::Ident)?;
                    parameters.push(Param { name, var });
                }
                Kind::DotDotDot => {
                    is_variadic = true;
                    break;
                }
                _ => break,
            }
            if self.peek() == Kind::Comma {
                self.take();
            } else if self.peek() != Kind::RParen {
                return Err(self.expect_error("',' or ')'"));
            }
        }
        self.expect(Kind::RParen)?;
        Ok((parameters, is_variadic))
    }

    fn expr_to_lvalue(&self, e: Expr<'src>) -> Result<LValue<'src>, Error> {
        match e {
            Expr::Var { name, var_use, .. } => Ok(LValue::Var { name, var_use }),
            Expr::Dot { expr, name, pos } => Ok(LValue::Dot {
                expr: *expr,
                name,
                pos,
            }),
            Expr::Index { expr, index, pos } => Ok(LValue::Index {
                expr: *expr,
                index: *index,
                pos,
            }),
            _ => Err(self.error(format!(
                "expected variable or table field expression on left side of assignment"
            ))),
        }
    }

    fn get_rule<'p>(&self, kind: Kind) -> ParseRule<'src, 'tok, 'lm, 'p> {
        match kind {
            Kind::Nil | Kind::True | Kind::False | Kind::Number | Kind::String => ParseRule {
                prefix: Some(&Parser::parse_literal_expr),
                infix: Some(&Parser::parse_call_expr),
                precedence: PREC_PRIMARY,
            },
            Kind::Ident => ParseRule {
                prefix: Some(&Parser::parse_var_expr),
                infix: None,
                precedence: PREC_NONE,
            },
            Kind::Function => ParseRule {
                prefix: Some(&Parser::parse_function_expr),
                infix: None,
                precedence: PREC_NONE,
            },
            Kind::Dot => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_dot_expr),
                precedence: PREC_PRIMARY,
            },
            Kind::LBrack => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_index_expr),
                precedence: PREC_PRIMARY,
            },
            Kind::Lt | Kind::LtEq | Kind::Gt | Kind::GtEq | Kind::EqEq | Kind::TildeEq => {
                ParseRule {
                    prefix: None,
                    infix: Some(&Parser::parse_binop_expr),
                    precedence: PREC_COMPARE,
                }
            }
            Kind::Pipe => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_BINOR,
            },
            Kind::Tilde => ParseRule {
                prefix: Some(&Parser::parse_unop_expr),
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_BINXOR,
            },
            Kind::Amp => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_BINAND,
            },
            Kind::LtLt | Kind::GtGt => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_SHIFT,
            },
            Kind::DotDot => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_CONCAT,
            },
            Kind::Plus => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_ADD,
            },
            Kind::Minus => ParseRule {
                prefix: Some(&Parser::parse_unop_expr),
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_ADD,
            },
            Kind::Star | Kind::Slash | Kind::SlashSlash | Kind::Percent => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_MUL,
            },
            Kind::Not | Kind::Hash => ParseRule {
                prefix: Some(&Parser::parse_unop_expr),
                infix: None,
                precedence: PREC_NONE,
            },
            Kind::Caret => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_EXP,
            },
            Kind::And => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_AND,
            },
            Kind::Or => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_binop_expr),
                precedence: PREC_OR,
            },
            Kind::LParen => ParseRule {
                prefix: Some(&Parser::parse_group_expr),
                infix: Some(&Parser::parse_call_expr),
                precedence: PREC_PRIMARY,
            },
            Kind::Colon => ParseRule {
                prefix: None,
                infix: Some(&Parser::parse_call_expr),
                precedence: PREC_PRIMARY,
            },
            Kind::LBrace => ParseRule {
                prefix: Some(&Parser::parse_table_expr),
                infix: Some(&Parser::parse_call_expr),
                precedence: PREC_PRIMARY,
            },
            _ => ParseRule {
                prefix: None,
                infix: None,
                precedence: PREC_NONE,
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

    fn next_label(&mut self) -> LabelID {
        let id = self.next_label;
        self.next_label += 1;
        LabelID(id)
    }

    fn next_label_use(&mut self) -> LabelUseID {
        let id = self.next_label_use;
        self.next_label_use += 1;
        LabelUseID(id)
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

type Precedence = u8;

const PREC_NONE: Precedence = 0;
const PREC_OR: Precedence = 1;
const PREC_AND: Precedence = 2;
const PREC_COMPARE: Precedence = 3;
const PREC_BINOR: Precedence = 4;
const PREC_BINAND: Precedence = 5;
const PREC_BINXOR: Precedence = 6;
const PREC_SHIFT: Precedence = 7;
const PREC_CONCAT: Precedence = 8;
const PREC_ADD: Precedence = 9;
const PREC_MUL: Precedence = 10;
const PREC_UNARY: Precedence = 11;
const PREC_EXP: Precedence = 12;
const PREC_PRIMARY: Precedence = 13;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Associativity {
    Left,
    Right,
}

fn associativity(prec: Precedence) -> Associativity {
    match prec {
        PREC_EXP | PREC_CONCAT => Associativity::Right,
        _ => Associativity::Left,
    }
}
