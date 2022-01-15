use std::cmp::{Ord, Ordering, PartialOrd};
use std::mem;
use std::ops::{Deref, DerefMut};
use std::sync::Mutex;

use lazy_static;

use crate::math;

pub const ALLOC_ALIGNMENT: usize = 8;

lazy_static! {
  pub static ref HEAP: Heap = Heap {
    mu: Mutex::new(State { alloc: 0 }),
    bytes: Box::new([0; 1024 * 1024]),
  };
}

pub struct Heap {
  mu: Mutex<State>,
  bytes: Box<[u8]>,
}

struct State {
  alloc: usize,
}

impl Heap {
  pub fn allocate(&self, size: usize) -> *mut u8 {
    let mut state = self.mu.lock().unwrap();
    let aligned_size = math::align(size, ALLOC_ALIGNMENT);
    assert!(state.alloc + aligned_size <= self.bytes.len());
    let addr = &self.bytes[state.alloc] as *const u8 as usize as *mut u8;
    state.alloc += aligned_size;
    addr
  }

  pub fn write_barrier(&self, _from: usize, _to: usize) {
    // TODO: implement when there's something useful to do.
  }

  pub fn write_barrier_nanbox(&self, _from: usize, _to: u64) {
    // TODO: implement when there's something useful to do.
  }
}

pub trait Set {
  fn set(&mut self, x: &Self);
}

#[derive(Debug)]
pub struct Ptr<T> {
  p: *mut T,
}

impl<T> Ptr<T> {
  pub fn set_ptr(&mut self, v: *mut T) {
    self.p = v;
    HEAP.write_barrier(&mut self.p as *mut *mut T as usize, v as usize)
  }

  pub fn unwrap(&self) -> *const T {
    self.p
  }

  pub fn unwrap_mut(&mut self) -> *mut T {
    self.p
  }

  pub fn unwrap_ref(&self) -> &T {
    unsafe { self.p.as_ref().unwrap() }
  }
}

impl<T> Set for Ptr<T> {
  fn set(&mut self, other: &Self) {
    self.p = other.p;
    HEAP.write_barrier(&mut self.p as *mut *mut T as usize, other.p as usize)
  }
}

impl<T> Deref for Ptr<T> {
  type Target = T;

  fn deref(&self) -> &T {
    unsafe { self.p.as_ref().unwrap() }
  }
}

impl<T> DerefMut for Ptr<T> {
  fn deref_mut(&mut self) -> &mut T {
    unsafe { self.p.as_mut().unwrap() }
  }
}

#[derive(Debug)]
pub struct Handle<T> {
  slot: *mut *mut T,
}

impl<T> Handle<T> {
  pub fn new(p: *mut T) -> Handle<T> {
    unsafe {
      let mut hs = HANDLE_STORAGE.lock().unwrap();
      let h = Handle {
        slot: hs.make_slot(),
      };
      *h.slot = p;
      h
    }
  }

  pub fn empty() -> Handle<T> {
    Handle {
      slot: 0 as *mut *mut T,
    }
  }
}

impl<T> Deref for Handle<T> {
  type Target = T;
  fn deref(&self) -> &T {
    assert!(!self.slot.is_null());
    unsafe { (*self.slot).as_ref().unwrap() }
  }
}

impl<T> DerefMut for Handle<T> {
  fn deref_mut(&mut self) -> &mut T {
    assert!(!self.slot.is_null());
    unsafe { (*self.slot).as_mut().unwrap() }
  }
}

impl<T> Drop for Handle<T> {
  fn drop(&mut self) {
    if !self.slot.is_null() {
      let mut hs = HANDLE_STORAGE.lock().unwrap();
      hs.drop_slot(self.slot);
    }
  }
}

impl<T: PartialEq> PartialEq for Handle<T> {
  fn eq(&self, other: &Handle<T>) -> bool {
    if self.slot.is_null() {
      return other.slot.is_null();
    }
    if other.slot.is_null() {
      return false;
    }
    self.deref() == other.deref()
  }
}

impl<T: Eq> Eq for Handle<T> {}

impl<T: PartialOrd> PartialOrd for Handle<T> {
  fn partial_cmp(&self, other: &Handle<T>) -> Option<Ordering> {
    if self.slot.is_null() || other.slot.is_null() {
      Some(Ordering::Equal)
    } else if self.slot.is_null() {
      Some(Ordering::Less)
    } else if other.slot.is_null() {
      Some(Ordering::Greater)
    } else {
      self.deref().partial_cmp(other.deref())
    }
  }
}

impl<T: Ord> Ord for Handle<T> {
  fn cmp(&self, other: &Handle<T>) -> Ordering {
    self.partial_cmp(other).unwrap()
  }
}

lazy_static! {
  static ref HANDLE_STORAGE: Mutex<HandleStorage> = Mutex::new(HandleStorage {
    slots: Box::new([0; 1024]),
    len: 0,
    free_list: !0,
  });
}

struct HandleStorage {
  slots: Box<[usize]>,
  len: usize,
  free_list: usize,
}

impl HandleStorage {
  fn make_slot<T>(&mut self) -> *mut *mut T {
    let slot = if self.free_list != !0 {
      // Free list not empty. Use the first free slot in that list.
      let next_free = self.slots[self.free_list];
      let slot = &mut self.slots[self.free_list];
      self.free_list = next_free;
      *slot = 0;
      slot
    } else if self.len < self.slots.len() {
      // Free list empty. Use a new slot.
      let i = self.len;
      self.len += 1;
      &mut self.slots[i]
    } else {
      panic!("not enough handles")
    };
    slot as *mut usize as *mut *mut T
  }

  fn drop_slot<T>(&mut self, slot: *mut *mut T) {
    unsafe {
      let slot = slot as *mut usize;
      *slot = self.free_list;
      let slot_index =
        (slot as usize - &self.slots[0] as *const usize as usize) / mem::size_of::<usize>();
      self.free_list = slot_index;
    }
  }
}
