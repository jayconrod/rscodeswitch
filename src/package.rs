use crate::data::{self, Slice};
use crate::heap::Handle;
use crate::inst;

use std::fmt;

pub struct Package {
    pub globals: Vec<Global>,
    pub functions: Vec<Function>,
    pub strings: Handle<Slice<data::String>>,
}

impl Package {
    pub fn global_by_name(&self, name: &str) -> Option<&Global> {
        self.global_index_by_name(name).map(|i| &self.globals[i])
    }

    pub fn global_index_by_name(&self, name: &str) -> Option<usize> {
        self.globals
            .iter()
            .enumerate()
            .find(|(_, g)| g.name == name)
            .map(|(i, _)| i)
    }

    pub fn function_by_name(&self, name: &str) -> Option<&Function> {
        self.function_index_by_name(name)
            .map(|i| &self.functions[i])
    }

    pub fn function_index_by_name(&self, name: &str) -> Option<usize> {
        self.functions
            .iter()
            .enumerate()
            .find(|(_, f)| f.name == name)
            .map(|(i, _)| i)
    }
}

impl fmt::Display for Package {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut sep = "";
        for gbl in &self.globals {
            write!(f, "{}{}", sep, gbl)?;
            sep = "\n\n";
        }
        for func in &self.functions {
            write!(f, "{}{}", sep, func)?;
            sep = "\n\n";
        }
        Ok(())
    }
}

pub struct Global {
    pub name: std::string::String,
}

impl fmt::Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "var {};", self.name)
    }
}

pub struct Function {
    pub name: std::string::String,
    pub insts: Vec<u8>,
    pub package: *const Package,
    pub param_types: Vec<Type>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "function {}() {{\n", self.name)?;
        inst::disassemble(&self.insts, f)?;
        f.write_str("}")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Nil,
    Bool,
    Float64,
    String,
    Function,
    Nanbox,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Type::Nil => "nil",
            Type::Bool => "bool",
            Type::Float64 => "f64",
            Type::String => "string",
            Type::Function => "function",
            Type::Nanbox => "dynval",
        };
        f.write_str(s)
    }
}
