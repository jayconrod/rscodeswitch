//! Provides functions to encode and decode values of various types within
//! IEEE-754 NaN values. This is useful for dynamically typed languages. Most
//! operations may be performed on NaN-boxed values.

use crate::data;
use crate::heap::{Set, HEAP};
use crate::runtime::{Closure, Object};
use std::cmp::{Ordering, PartialOrd};
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::mem;

/// NanBox encodes various types within the unused bits of IEEE-754 QNaN values
/// that are not naturally produced by supported processors. This is useful for
/// representing values in dynamically typed languages. Most operations may
/// be performed on NaN-boxed values.
#[derive(Clone, Copy)]
pub struct NanBox(pub u64);

impl NanBox {
    /// Returns a 3-bit tag indicating what kind of value is boxed.
    pub fn type_tag(&self) -> u64 {
        if self.0 & QNAN == QNAN {
            self.0 & TAG_MASK
        } else {
            TAG_FLOAT
        }
    }

    pub fn from_nil() -> NanBox {
        NanBox(QNAN | TAG_NIL)
    }

    pub fn is_nil(&self) -> bool {
        self.0 == QNAN | TAG_NIL
    }

    pub unsafe fn from_small_or_big_i64(n: i64) -> NanBox {
        n.try_into().unwrap_or_else(|_| {
            let bi = HEAP.allocate(mem::size_of::<i64>()) as *mut i64;
            *bi = n;
            bi.into()
        })
    }

    pub fn as_i64(&self) -> ConvertResult<i64> {
        <NanBox as TryInto<i64>>::try_into(*self).or_else(|_| {
            match <NanBox as TryInto<f64>>::try_into(*self) {
                Ok(f) if (f as i64) as f64 == f => Ok(f as i64),
                _ => Err(ConvertError {}),
            }
        })
    }

    pub fn as_i64_rounded(&self) -> ConvertResult<i64> {
        <NanBox as TryInto<i64>>::try_into(*self).or_else(|_| {
            match <NanBox as TryInto<f64>>::try_into(*self) {
                Ok(f) => Ok(f as i64),
                _ => Err(ConvertError {}),
            }
        })
    }

    pub fn as_f64(&self) -> ConvertResult<f64> {
        <NanBox as TryInto<f64>>::try_into(*self).or_else(|_| {
            match <NanBox as TryInto<i64>>::try_into(*self) {
                Ok(i) if (i as f64) as i64 == i => Ok(i as f64),
                _ => Err(ConvertError {}),
            }
        })
    }

    pub fn as_f64_imprecise(&self) -> ConvertResult<f64> {
        <NanBox as TryInto<f64>>::try_into(*self).or_else(|_| {
            match <NanBox as TryInto<i64>>::try_into(*self) {
                Ok(i) => Ok(i as f64),
                _ => Err(ConvertError {}),
            }
        })
    }

    pub fn is_number(&self) -> bool {
        match self.type_tag() {
            TAG_SMALL_INT | TAG_BIG_INT | TAG_FLOAT => true,
            _ => false,
        }
    }
}

impl Debug for NanBox {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let s = match self.type_tag() {
            TAG_NIL => "nil",
            TAG_BOOL => "bool",
            TAG_SMALL_INT | TAG_BIG_INT => "integer",
            TAG_STRING => "string",
            TAG_CLOSURE => "function",
            TAG_OBJECT => "object",
            TAG_FLOAT => "float",
            _ => "unknown",
        };
        f.write_str(s)
    }
}

impl Display for NanBox {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let s = match self.type_tag() {
            TAG_NIL => String::from("nil"),
            TAG_BOOL => {
                let b: bool = (*self).try_into().unwrap();
                format!("{}", b)
            }
            TAG_SMALL_INT | TAG_BIG_INT => {
                let i: i64 = (*self).try_into().unwrap();
                format!("{}", i)
            }
            TAG_STRING => unsafe {
                let s: *const data::String = (*self).try_into().unwrap();
                format!("{}", s.as_ref().unwrap())
            },
            TAG_CLOSURE => String::from("<function>"),
            TAG_OBJECT => String::from("<object>"),
            TAG_FLOAT => {
                let f: f64 = (*self).try_into().unwrap();
                format!("{}", f)
            }
            _ => String::from("<unknown>"),
        };
        f.write_str(&s)
    }
}

impl PartialEq for NanBox {
    fn eq(&self, other: &NanBox) -> bool {
        if let (Ok(li), Ok(ri)) = (self.as_i64(), other.as_i64()) {
            li == ri
        } else if let (Ok(lf), Ok(rf)) = (self.as_f64(), other.as_f64()) {
            lf == rf
        } else if let (Ok(ls), Ok(rs)) = (
            <NanBox as TryInto<&data::String>>::try_into(*self),
            <NanBox as TryInto<&data::String>>::try_into(*other),
        ) {
            ls == rs
        } else {
            self.0 == other.0
        }
    }
}

impl PartialOrd for NanBox {
    fn partial_cmp(&self, other: &NanBox) -> Option<Ordering> {
        if let (Ok(li), Ok(ri)) = (
            <NanBox as TryInto<i64>>::try_into(*self),
            <NanBox as TryInto<i64>>::try_into(*other),
        ) {
            li.partial_cmp(&ri)
        } else if let (Ok(lf), Ok(rf)) = (self.as_f64(), other.as_f64()) {
            lf.partial_cmp(&rf)
        } else if let (Ok(ls), Ok(rs)) = (
            <NanBox as TryInto<&data::String>>::try_into(*self),
            <NanBox as TryInto<&data::String>>::try_into(*other),
        ) {
            ls.partial_cmp(rs)
        } else {
            None
        }
    }
}

impl Set for NanBox {
    fn set(&mut self, v: &Self) {
        self.0 = v.0;
        HEAP.write_barrier_nanbox(self as *mut NanBox as usize, v.0);
    }
}

impl From<bool> for NanBox {
    fn from(b: bool) -> NanBox {
        NanBox(QNAN | TAG_BOOL | (b as u64) << TAG_SIZE)
    }
}

impl TryInto<bool> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<bool> {
        if self.type_tag() == TAG_BOOL {
            Ok(((self.0 >> TAG_SIZE) & 1) != 0)
        } else {
            Err(ConvertError {})
        }
    }
}

impl From<f64> for NanBox {
    fn from(f: f64) -> NanBox {
        NanBox(f.to_bits())
    }
}

impl TryInto<f64> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<f64> {
        if self.0 & QNAN != QNAN {
            Ok(f64::from_bits(self.0))
        } else {
            Err(ConvertError {})
        }
    }
}

impl TryFrom<i64> for NanBox {
    type Error = SmallIntError;
    fn try_from(i: i64) -> Result<NanBox, Self::Error> {
        if fits_in_small_int(i) {
            let mask = (1 << SMALL_INT_BITS) - 1;
            let ui = i as u64 & mask;
            Ok(NanBox(QNAN | TAG_SMALL_INT | (ui << TAG_SIZE)))
        } else {
            Err(SmallIntError {})
        }
    }
}

impl TryInto<i64> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<i64> {
        match self.type_tag() {
            TAG_SMALL_INT => {
                let bits = (self.0 & VALUE_MASK) as i64;
                let shift_left = (64 - SMALL_INT_BITS) as i64;
                let shift_right = shift_left + TAG_SIZE as i64;
                Ok(bits << shift_left >> shift_right)
            }
            TAG_BIG_INT => {
                let bi = (self.0 & !QNAN & !TAG_MASK) as usize as *const i64;
                Ok(unsafe { *bi })
            }
            _ => Err(ConvertError {}),
        }
    }
}

impl From<*mut i64> for NanBox {
    fn from(bi: *mut i64) -> NanBox {
        assert!(!bi.is_null());
        NanBox(QNAN | TAG_BIG_INT | (bi as u64))
    }
}

impl From<*const data::String> for NanBox {
    fn from(s: *const data::String) -> NanBox {
        if s.is_null() {
            NanBox::from_nil()
        } else {
            NanBox(QNAN | TAG_STRING | s as u64)
        }
    }
}

impl TryInto<*const data::String> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<*const data::String> {
        if self.0 & (QNAN | TAG_MASK) == QNAN | TAG_STRING {
            Ok((self.0 & !QNAN & !TAG_MASK) as usize as *const data::String)
        } else {
            Err(ConvertError {})
        }
    }
}

impl From<*mut data::String> for NanBox {
    fn from(s: *mut data::String) -> NanBox {
        if s.is_null() {
            NanBox::from_nil()
        } else {
            NanBox(QNAN | TAG_STRING | s as u64)
        }
    }
}

impl From<&data::String> for NanBox {
    fn from(s: &data::String) -> NanBox {
        NanBox::from(s as *const data::String)
    }
}

impl TryInto<&data::String> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<&'static data::String> {
        self.try_into()
            .map(|s: *const data::String| unsafe { s.as_ref().unwrap() })
    }
}

impl From<*mut Closure> for NanBox {
    fn from(c: *mut Closure) -> NanBox {
        if c.is_null() {
            NanBox::from_nil()
        } else {
            NanBox(QNAN | TAG_CLOSURE | c as u64)
        }
    }
}

impl TryInto<*mut Closure> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<*mut Closure> {
        if self.0 & (QNAN | TAG_MASK) == QNAN | TAG_CLOSURE {
            Ok((self.0 & !QNAN & !TAG_MASK) as usize as *mut Closure)
        } else {
            Err(ConvertError {})
        }
    }
}

impl From<*const Closure> for NanBox {
    fn from(c: *const Closure) -> NanBox {
        if c.is_null() {
            NanBox::from_nil()
        } else {
            NanBox(QNAN | TAG_CLOSURE | c as u64)
        }
    }
}

impl From<&mut Closure> for NanBox {
    fn from(c: &mut Closure) -> NanBox {
        NanBox::from(c as *mut Closure)
    }
}

impl TryInto<&mut Closure> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<&'static mut Closure> {
        self.try_into()
            .map(|c: *mut Closure| unsafe { c.as_mut().unwrap() })
    }
}

impl From<&Closure> for NanBox {
    fn from(c: &Closure) -> NanBox {
        NanBox::from(c as *const Closure)
    }
}

impl TryInto<&Closure> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<&'static Closure> {
        self.try_into()
            .map(|c: *mut Closure| unsafe { c.as_ref().unwrap() })
    }
}

impl From<*const Object> for NanBox {
    fn from(o: *const Object) -> NanBox {
        if o.is_null() {
            NanBox::from_nil()
        } else {
            NanBox(QNAN | TAG_OBJECT | o as u64)
        }
    }
}

impl TryInto<*mut Object> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<*mut Object> {
        if self.0 & (QNAN | TAG_MASK) == QNAN | TAG_OBJECT {
            Ok((self.0 & !QNAN & !TAG_MASK) as usize as *mut Object)
        } else {
            Err(ConvertError {})
        }
    }
}

impl From<&mut Object> for NanBox {
    fn from(c: &mut Object) -> NanBox {
        NanBox::from(c as *const Object)
    }
}

impl TryInto<&mut Object> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<&'static mut Object> {
        self.try_into()
            .map(|c: *mut Object| unsafe { c.as_mut().unwrap() })
    }
}

impl From<&Object> for NanBox {
    fn from(c: &Object) -> NanBox {
        NanBox::from(c as *const Object)
    }
}

impl TryInto<&Object> for NanBox {
    type Error = ConvertError;
    fn try_into(self) -> ConvertResult<&'static Object> {
        self.try_into()
            .map(|c: *mut Object| unsafe { c.as_ref().unwrap() })
    }
}

/// A NaN-boxed value that may be used as a hash table key. Actual NaN values
/// are not allowed, since they don't compare equal to themselves.
///
/// NaNBoxKey implements Eq and Hash. Like NanBox, two numbers are equal if
/// they are numerically equal, even if they have different representations.
/// For example, a small integer 0 is equal to a big integer 0 as well as
/// float 0.0 and -0.0
#[derive(Clone, Copy, Debug)]
pub struct NanBoxKey(u64);

impl NanBoxKey {
    pub fn as_array_key(&self) -> ConvertResult<i64> {
        match NanBox(self.0).as_i64() {
            Ok(i) if i < i64::MAX => Ok(i),
            _ => Err(ConvertError {}),
        }
    }
}

impl TryFrom<NanBox> for NanBoxKey {
    type Error = NanBoxKeyError;
    fn try_from(v: NanBox) -> Result<NanBoxKey, Self::Error> {
        let fr: ConvertResult<f64> = v.try_into();
        match fr {
            Ok(f) if f.is_nan() => Err(NanBoxKeyError {}),
            _ => Ok(NanBoxKey(v.0)),
        }
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
        let d = NanBox(self.0);
        if let Ok(i) = d.as_i64() {
            i.hash(state);
        } else if let Ok(s) = <NanBox as TryInto<&data::String>>::try_into(d) {
            s.hash(state)
        } else {
            self.0.hash(state)
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

#[derive(Debug)]
pub struct ConvertError {}

impl Display for ConvertError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("could not convert nanboxed value to desired type")
    }
}

type ConvertResult<T> = std::result::Result<T, ConvertError>;

#[derive(Debug)]
pub struct SmallIntError {}

impl Display for SmallIntError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("integer is too big to be represented as a NaN-boxed small int")
    }
}

/// Basic encoding for IEEE quiet NaN values. The exponent bits are all set, and
/// the two high mantissa bits are set. The remaining 51 bits of the mantissa
/// may be used to encode boxed values. The sign bit is unused.
const QNAN: u64 = 0x7ffc_0000_0000_0000;

/// The low three bits of the mantissa indicate what kind of value is boxed.
pub const TAG_MASK: u64 = 7;
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

pub fn fits_in_small_int(n: i64) -> bool {
    let mask = !((1 << SMALL_INT_BITS) - 1);
    let high = (n as u64) & mask;
    high == mask || high == 0
}
