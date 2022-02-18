#[macro_use]
extern crate lazy_static;
extern crate regex;

pub mod data;
pub mod heap;
pub mod inst;
pub mod interpret;
pub mod lox;
pub mod lua;
pub mod math;
pub mod nanbox;
pub mod package;
pub mod pos;
pub mod runtime;

#[cfg(test)]
mod data_test;
