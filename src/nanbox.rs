//! Provides functions to encode and decode values of various types within
//! IEEE-754 NaN values. This is useful for dynamically typed languages. Most
//! operations may be performed on NaN-boxed values.

use crate::data;
use crate::heap::{Set, HEAP};
use crate::package::{Closure, Object};
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::{Hash, Hasher};

// TODO: convert everything to use NanBox type.
#[derive(Clone, Copy)]
pub struct NanBox(pub u64);

impl NanBox {
    pub fn from_nil() -> NanBox {
        NanBox(from_nil())
    }
    pub fn from_string(s: &data::String) -> NanBox {
        NanBox(from_string(s))
    }
    pub fn to_closure(&self) -> Option<*const Closure> {
        to_closure(self.0)
    }
    pub fn to_object(&self) -> Option<*const Object> {
        to_object(self.0)
    }
}

impl Debug for NanBox {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(debug_type(self.0))
    }
}

impl Display for NanBox {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(&debug_str(self.0))
    }
}

impl PartialEq for NanBox {
    fn eq(&self, other: &NanBox) -> bool {
        if let (Some(li), Some(ri)) = (num_as_i64(self.0), num_as_i64(other.0)) {
            li == ri
        } else if let (Some(lf), Some(rf)) = (to_f64(self.0), to_f64(other.0)) {
            lf == rf
        } else if let (Some(ls), Some(rs)) = (to_string(self.0), to_string(other.0)) {
            ls == rs
        } else {
            self.0 == other.0
        }
    }
}

impl Set for NanBox {
    fn set(&mut self, v: &Self) {
        self.0 = v.0;
        HEAP.write_barrier_nanbox(self as *mut NanBox as usize, v.0);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct NanBoxKey(u64);

impl TryFrom<NanBox> for NanBoxKey {
    type Error = NanBoxKeyError;
    fn try_from(v: NanBox) -> Result<NanBoxKey, Self::Error> {
        if let Some(f) = to_f64(v.0) {
            if f.is_nan() {
                return Err(NanBoxKeyError {});
            }
            let i = f as i64;
            if i as f64 == f && fits_in_small_int(i) {
                return Ok(NanBoxKey(from_small_int(i)));
            }
        }
        Ok(NanBoxKey(v.0))
    }
}

impl Set for NanBoxKey {
    fn set(&mut self, v: &Self) {
        self.0 = v.0;
        HEAP.write_barrier_nanbox(self as *mut NanBoxKey as usize, v.0);
    }
}

impl Display for NanBoxKey {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        <NanBox as Display>::fmt(&NanBox(self.0), f)
    }
}

impl PartialEq for NanBoxKey {
    fn eq(&self, other: &NanBoxKey) -> bool {
        NanBox(self.0) == NanBox(other.0)
    }
}

impl Eq for NanBoxKey {}

impl Hash for NanBoxKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if let Some(i) = num_as_i64(self.0) {
            i.hash(state)
        } else if let Some(f) = to_f64(self.0) {
            debug_assert!(!f.is_nan());
            self.0.hash(state);
        } else if let Some(s) = to_string(self.0) {
            s.hash(state);
        } else {
            self.0.hash(state);
        }
    }
}

#[derive(Debug)]
pub struct NanBoxKeyError {}

impl Display for NanBoxKeyError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("NaN value can't be used as a property key")
    }
}

/// Basic encoding for IEEE quiet NaN values. The exponent bits are all set, and
/// the two high mantissa bits are set. The remaining 51 bits of the mantissa
/// may be used to encode boxed values. The sign bit is unused.
const QNAN: u64 = 0x7ffc_0000_0000_0000;

/// The low three bits of the mantissa indicate what kind of value is boxed.
const TAG_MASK: u64 = 7;
pub const TAG_SIZE: u64 = 3;
pub const TAG_NIL: u64 = 0;
pub const TAG_BOOL: u64 = 1;
pub const TAG_SMALL_INT: u64 = 2;
pub const TAG_BIG_INT: u64 = 3;
pub const TAG_STRING: u64 = 4;
pub const TAG_CLOSURE: u64 = 5;
pub const TAG_OBJECT: u64 = 6;
pub const TAG_FLOAT: u64 = 8;

const VALUE_MASK: u64 = 0x0003_ffff_ffff_ffff;
const SMALL_INT_BITS: u64 = 47;

pub fn type_tag(v: u64) -> u64 {
    if v & QNAN == QNAN {
        v & TAG_MASK
    } else {
        TAG_FLOAT
    }
}

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
