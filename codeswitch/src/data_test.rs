use crate::data::{self, Array, List, Slice};
use crate::heap::Handle;

#[test]
fn array_test() {
  unsafe {
    let a = Array::<usize>::alloc(3).as_mut().unwrap();
    for i in 0..3 {
      *a.index_mut(i) = i * 2;
    }
    for i in 0..3 {
      assert_eq!(*a.index(i), i * 2);
    }
  }
}

#[test]
fn slice_test() {
  let s = unsafe { Slice::<usize>::alloc_with_array(3).as_mut().unwrap() };
  assert_eq!(s.len(), 3);
  for i in 0..3 {
    s[i] = i * 2;
  }
  for i in 0..3 {
    assert_eq!(s[i], i * 2);
  }

  let s2 = unsafe { Slice::<usize>::alloc_with_array(3).as_mut().unwrap() };
  for i in 0..3 {
    s2[i] = i * 2;
  }
  assert_eq!(s, s2);
  s2[0] = 99;
  assert_ne!(s, s2);
  assert!(s < s2);
}

#[test]
fn list_test() {
  let mut l = Handle::new(List::<usize>::alloc());
  assert_eq!(l.len(), 0);
  assert_eq!(l.cap(), 0);

  for i in 0..3 {
    l.push_value(i * 2);
  }
  assert_eq!(l.len(), 3);
  assert!(l.cap() >= 3);
  for i in 0..3 {
    assert_eq!(l[i], i * 2);
    l[i] *= 2;
    assert_eq!(l[i], i * 4);
  }
}

#[test]
fn string_test() {
  let s1 = Handle::new(data::String::from_bytes(b"foo"));
  assert_eq!(s1.len(), 3);
  assert_eq!(s1, s1);
  let s2 = Handle::new(data::String::from_bytes(b"foo"));
  assert_eq!(s1, s2);
  let s3 = Handle::new(data::String::from_bytes(b"bar"));
  assert_ne!(s1, s3);
  assert!(s1 > s3);
}

#[test]
fn hashmap_test() {
  let mut m = Handle::new(data::HashMap::<data::String, data::String>::alloc());

  assert_eq!(m.len(), 0);
  let a = Handle::new(data::String::from_bytes(b"a"));
  assert!(!m.contains_key(&*a));
  assert_eq!(m.get(&*a), None);

  m.insert(&*a, &*a);
  assert_eq!(m.len(), 1);
  assert_eq!(m.get(&*a), Some(&*a));
  assert!(m.contains_key(&*a));

  m.insert(&*a, &*a);
  assert_eq!(m.len(), 1);

  m = Handle::new(data::HashMap::<data::String, data::String>::alloc());
  for i in 0..1000 {
    let s = Handle::new(data::String::from_bytes(format!("{}", i).as_bytes()));
    m.insert(&*s, &*s);
    assert_eq!(m.len(), i + 1);
  }
  for i in 0..1000 {
    let s = Handle::new(data::String::from_bytes(format!("{}", i).as_bytes()));
    assert!(m.contains_key(&*s));
    assert_eq!(m.get(&*s), Some(&*s));
  }
}
