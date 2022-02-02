//! Provides functions to encode and decode values of various types within
//! IEEE-754 NaN values. This is useful for dynamically typed languages. Most
//! operations may be performed on NaN-boxed values.

use crate::data;
use crate::package::{Closure, Object};

/// Basic encoding for IEEE quiet NaN values. The exponent bits are all set, and
/// the two high mantissa bits are set. The remaining 51 bits of the mantissa
/// may be used to encode boxed values. The sign bit is unused.
const QNAN: u64 = 0x7ffc_0000_0000_0000;

/// The low three bits of the mantissa indicate what kind of value is boxed.
const TAG_MASK: u64 = 7;
const TAG_SIZE: u64 = 3;
const TAG_NIL: u64 = 0;
const TAG_BOOL: u64 = 1;
const TAG_SMALL_INT: u64 = 2;
const TAG_BIG_INT: u64 = 3;
const TAG_STRING: u64 = 4;
const TAG_CLOSURE: u64 = 5;
const TAG_OBJECT: u64 = 6;

const VALUE_MASK: u64 = 0x0003_ffff_ffff_ffff;
const SMALL_INT_BITS: u64 = 47;

pub fn from_nil() -> u64 {
    QNAN | TAG_NIL
}

pub fn is_nil(v: u64) -> bool {
    v == QNAN | TAG_NIL
}

pub fn from_bool(b: bool) -> u64 {
    QNAN | TAG_BOOL | (b as u64) << TAG_SIZE
}

pub fn to_bool(v: u64) -> Option<bool> {
    if v & (QNAN | TAG_MASK) == QNAN | TAG_BOOL {
        Some(v & VALUE_MASK & !TAG_MASK != 0)
    } else {
        None
    }
}

pub fn from_f64(n: f64) -> u64 {
    n.to_bits()
}

pub fn to_f64(v: u64) -> Option<f64> {
    if v & QNAN == QNAN {
        None
    } else {
        Some(f64::from_bits(v))
    }
}

pub fn num_as_f64(v: u64) -> Option<f64> {
    if let Some(i) = to_int(v) {
        Some(i as f64)
    } else if let Some(f) = to_f64(v) {
        Some(f)
    } else {
        None
    }
}

pub fn fits_in_small_int(n: i64) -> bool {
    let mask = !((1 << SMALL_INT_BITS) - 1);
    let high = (n as u64) & mask;
    high == mask || high == 0
}

pub fn from_small_int(n: i64) -> u64 {
    assert!(fits_in_small_int(n));
    let mask = (1 << SMALL_INT_BITS) - 1;
    let un = n as u64 & mask;
    QNAN | TAG_SMALL_INT | (un << TAG_SIZE)
}

pub fn to_small_int(v: u64) -> Option<i64> {
    if v & (QNAN | TAG_MASK) == QNAN | TAG_SMALL_INT {
        let bits = (v & VALUE_MASK) as i64;
        let shift_left = (64 - SMALL_INT_BITS) as i64;
        let shift_right = shift_left + TAG_SIZE as i64;
        Some(bits << shift_left >> shift_right)
    } else {
        None
    }
}

pub fn from_big_int(n: *const i64) -> u64 {
    QNAN | TAG_BIG_INT | n as u64
}

pub fn to_big_int(v: u64) -> Option<*const i64> {
    if v & (QNAN | TAG_MASK) == QNAN | TAG_BIG_INT {
        Some((v & !QNAN & !TAG_MASK) as usize as *const i64)
    } else {
        None
    }
}

pub fn to_int(v: u64) -> Option<i64> {
    if let Some(n) = to_small_int(v) {
        Some(n)
    } else if let Some(n) = to_big_int(v) {
        Some(unsafe { *n })
    } else {
        None
    }
}

pub fn is_number(v: u64) -> bool {
    (v & QNAN) != QNAN || v & TAG_MASK == TAG_SMALL_INT || v & TAG_MASK == TAG_BIG_INT
}

pub fn num_as_i64(v: u64) -> Option<i64> {
    if let Some(i) = to_int(v) {
        Some(i)
    } else if let Some(f) = to_f64(v) {
        let i = f as i64;
        if i as f64 == f {
            Some(i)
        } else {
            None
        }
    } else {
        None
    }
}

pub fn from_string(s: *const data::String) -> u64 {
    assert!(!s.is_null());
    QNAN | TAG_STRING | s as u64
}

pub fn to_string(v: u64) -> Option<*const data::String> {
    if v & (QNAN | TAG_MASK) == QNAN | TAG_STRING {
        Some((v & !QNAN & !TAG_MASK) as usize as *const data::String)
    } else {
        None
    }
}

pub fn from_closure(f: *const Closure) -> u64 {
    assert!(!f.is_null());
    QNAN | TAG_CLOSURE | f as u64
}

pub fn to_closure(v: u64) -> Option<*const Closure> {
    if v & (QNAN | TAG_MASK) == QNAN | TAG_CLOSURE {
        Some((v & !QNAN & !TAG_MASK) as usize as *const Closure)
    } else {
        None
    }
}

pub fn from_object(f: *const Object) -> u64 {
    assert!(!f.is_null());
    QNAN | TAG_OBJECT | f as u64
}

pub fn to_object(v: u64) -> Option<*const Object> {
    if v & (QNAN | TAG_MASK) == QNAN | TAG_OBJECT {
        Some((v & !QNAN & !TAG_MASK) as usize as *const Object)
    } else {
        None
    }
}

pub fn debug_str(v: u64) -> String {
    if is_nil(v) {
        return String::from("nil");
    }
    if let Some(b) = to_bool(v) {
        return format!("{}", b);
    }
    if let Some(n) = to_small_int(v) {
        return format!("{}", n);
    }
    if let Some(np) = to_big_int(v) {
        return format!("{}", unsafe { *np.as_ref().unwrap() });
    }
    if let Some(n) = to_f64(v) {
        return format!("{}", n);
    }
    if let Some(s) = to_string(v) {
        unsafe {
            return format!("{}", s.as_ref().unwrap());
        }
    }
    if let Some(_) = to_closure(v) {
        return String::from("<function>");
    }
    if let Some(_) = to_object(v) {
        return String::from("<object>");
    }
    return format!("Nanbox {:?}", v);
}

pub fn debug_type(v: u64) -> &'static str {
    if is_nil(v) {
        "nil"
    } else if to_bool(v).is_some() {
        "bool"
    } else if to_small_int(v).is_some() || to_big_int(v).is_some() {
        "integer"
    } else if to_f64(v).is_some() {
        "float"
    } else if to_string(v).is_some() {
        "string"
    } else if to_closure(v).is_some() {
        "function"
    } else if to_object(v).is_some() {
        "object"
    } else {
        "invalid value"
    }
}
