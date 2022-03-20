extern crate codeswitch;
extern crate lazy_static;
extern crate regex;

pub mod compile;
pub mod luastd;
pub mod runtime;
pub mod scope;
pub mod syntax;
pub mod token;

#[cfg(test)]
mod compile_test;
#[cfg(test)]
mod interpret_test;
