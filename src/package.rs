use crate::inst;

use std::fmt;

pub struct Package {
    pub functions: Vec<Function>,
}

impl Package {
    pub fn function_by_name(&self, name: &str) -> Option<&Function> {
        self.functions.iter().find(|f| f.name == name)
    }
}

impl fmt::Display for Package {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut sep = "";
        for func in &self.functions {
            write!(f, "{}{}", sep, func)?;
            sep = "\n\n";
        }
        Ok(())
    }
}

pub struct Function {
    pub name: String,
    pub insts: Vec<u8>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "function {}() {{\n", self.name)?;
        inst::disassemble(&self.insts, f)?;
        f.write_str("}}")
    }
}

pub enum Type {
    Bool,
    Float64,
    Nanbox,
}
