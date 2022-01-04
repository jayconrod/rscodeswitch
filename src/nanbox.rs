use crate::data;

const QNAN: u64 = 0x7ffc_0000_0000_0000;

const TAG_MASK: u64 = 7;
const TAG_SIZE: u64 = 3;
const TAG_BOOL: u64 = 1;
const TAG_STRING: u64 = 2;

const VALUE_MASK: u64 = 0x0003_ffff_ffff_ffff;

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

pub fn from_string(s: *const data::String) -> u64 {
  QNAN | TAG_STRING | s as u64
}

pub fn to_string(v: u64) -> Option<*const data::String> {
  if v & (QNAN | TAG_MASK) == QNAN | TAG_STRING {
    Some((v & !QNAN & !TAG_MASK) as usize as *const data::String)
  } else {
    None
  }
}

pub fn debug_str(v: u64) -> String {
  if let Some(b) = to_bool(v) {
    return format!("{}", b);
  }
  if let Some(n) = to_f64(v) {
    return format!("{}", n);
  }
  if let Some(s) = to_string(v) {
    unsafe {
      return format!("{}", s.as_ref().unwrap());
    }
  }
  return format!("Nanbox {:?}", v);
}

pub fn debug_type(v: u64) -> &'static str {
  if to_bool(v).is_some() {
    "bool"
  } else if to_f64(v).is_some() {
    "f64"
  } else if to_string(v).is_some() {
    "string"
  } else {
    "invalid value"
  }
}
