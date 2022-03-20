extern crate codeswitch;
extern crate lazy_static;
extern crate regex;

pub mod compile;
pub mod scope;
pub mod syntax;
pub mod token;

#[cfg(test)]
mod test;
