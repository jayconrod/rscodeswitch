use crate::compile;
use crate::token::{self, Number};
use codeswitch::package::Package;
use codeswitch::pos::ErrorList;
use codeswitch::runtime::LuaConvertedNumber;

use std::path::Path;

pub struct LuaRuntimeImpl {}

impl codeswitch::runtime::LuaRuntime for LuaRuntimeImpl {
    fn compile(&self, path: &Path, data: &[u8]) -> Result<Package, ErrorList> {
        compile::compile_file_data(path, data)
    }

    fn convert_number(&self, s: &str) -> LuaConvertedNumber {
        match token::convert_number(s) {
            Number::Malformed => LuaConvertedNumber::Malformed,
            Number::Int(n) => LuaConvertedNumber::Int(n),
            Number::Float(n) => LuaConvertedNumber::Float(n),
        }
    }
}
