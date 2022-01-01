const QNAN: u64 = 0x7ffc000000000000;

const TAG_MASK: u64 = 7;
const TAG_SIZE: u64 = 3;
const TAG_BOOL: u64 = 1;

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

pub fn debug_str(v: u64) -> String {
  if let Some(b) = to_bool(v) {
    return format!("{}", b);
  }
  if let Some(n) = to_f64(v) {
    return format!("{}", n);
  }
  return format!("Nanbox {:?}", v);
}
