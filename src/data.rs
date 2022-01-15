use crate::heap::{Ptr, Set, HEAP};
use std::cmp::{Ord, Ordering};
use std::collections::hash_map::DefaultHasher;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use std::ops::Add;
use std::ops::{Index, IndexMut};
use std::slice;
use std::str::{self, Utf8Error};

#[derive(Debug)]
pub struct SetValue<T: Copy> {
    pub value: T,
}

impl<T: Copy> Set for SetValue<T> {
    fn set(&mut self, other: &SetValue<T>) {
        self.value = other.value
    }
}

#[derive(Debug)]
pub struct Array<T> {
    _data: PhantomData<T>,
}

impl<T> Array<T> {
    pub fn alloc(len: usize) -> *mut Array<T> {
        let size = len * mem::size_of::<T>();
        HEAP.allocate(size) as *mut Array<T>
    }

    // index and index_mut are marked unsafe because they can't perform a bounds
    // check. Consequently, they don't implement Index and IndexMut.

    pub unsafe fn index(&self, i: usize) -> &T {
        let p = self as *const Array<T> as usize + i * mem::size_of::<T>();
        (p as *const T).as_ref().unwrap()
    }

    pub unsafe fn index_mut(&mut self, i: usize) -> &mut T {
        let p = self as *mut Array<T> as usize + i * mem::size_of::<T>();
        (p as *mut T).as_mut().unwrap()
    }
}

#[derive(Debug)]
pub struct Slice<T> {
    pub data: Ptr<Array<T>>,
    pub len: usize,
}

impl<T> Slice<T> {
    pub fn alloc() -> *mut Slice<T> {
        HEAP.allocate(mem::size_of::<Slice<T>>()) as *mut Slice<T>
    }

    pub fn alloc_with_array(len: usize) -> *mut Slice<T> {
        unsafe {
            let size = mem::size_of::<Slice<T>>() + mem::size_of::<T>() * len;
            let p = HEAP.allocate(size);
            let s = p as *mut Slice<T>;
            let a = (p as usize + mem::size_of::<Slice<T>>()) as *mut Array<T>;
            s.as_mut().unwrap().init(a, len);
            s
        }
    }

    pub fn init(&mut self, data: *mut Array<T>, len: usize) {
        self.data.set_ptr(data);
        self.len = len;
    }

    pub fn init_from_list(&mut self, list: &List<T>) {
        self.data.set(&list.data.data);
        self.len = list.len;
    }

    pub fn slice(&self, from: usize, to: usize) -> &[T] {
        assert!(from <= to && to <= self.len);
        unsafe {
            let from_addr = self.data.unwrap() as usize + from * mem::size_of::<T>();
            let len = to - from;
            slice::from_raw_parts(from_addr as *const T, len)
        }
    }

    pub fn as_slice(&self) -> &[T] {
        self.slice(0, self.len())
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn iter(&self) -> SliceIter<'_, T> {
        SliceIter::new(self)
    }
}

impl<T> Set for Slice<T> {
    fn set(&mut self, s: &Slice<T>) {
        self.data.set(&s.data);
        self.len = s.len;
    }
}

impl<T> Index<usize> for Slice<T> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        assert!(i < self.len);
        unsafe { self.data.index(i) }
    }
}

impl<T> IndexMut<usize> for Slice<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        assert!(i < self.len);
        unsafe { self.data.index_mut(i) }
    }
}

impl<T: PartialEq> PartialEq<Slice<T>> for Slice<T> {
    fn eq(&self, other: &Slice<T>) -> bool {
        if self.len != other.len {
            return false;
        }
        for i in 0..self.len {
            if self[i] != other[i] {
                return false;
            }
        }
        return true;
    }
}

impl<T: Eq> Eq for Slice<T> {}

impl<T: PartialOrd> PartialOrd<Slice<T>> for Slice<T> {
    fn partial_cmp(&self, other: &Slice<T>) -> Option<Ordering> {
        for i in 0..self.len.min(other.len) {
            match self[i].partial_cmp(&other[i]) {
                Some(Ordering::Equal) => (),
                c => return c,
            }
        }
        Some(self.len.cmp(&other.len))
    }
}

impl<T: Ord> Ord for Slice<T> {
    fn cmp(&self, other: &Slice<T>) -> Ordering {
        for i in 0..self.len.min(other.len) {
            match self[i].cmp(&other[i]) {
                Ordering::Equal => (),
                c => return c,
            }
        }
        self.len.cmp(&other.len)
    }
}

impl<T: Hash> Hash for Slice<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        <T>::hash_slice(self.as_slice(), state)
    }
}

impl<'a, T> IntoIterator for &'a Slice<T> {
    type Item = &'a T;
    type IntoIter = SliceIter<'a, T>;
    fn into_iter(self) -> SliceIter<'a, T> {
        self.iter()
    }
}

pub struct SliceIter<'a, T> {
    slice: &'a Slice<T>,
    index: usize,
}

impl<'a, T> SliceIter<'a, T> {
    fn new(slice: &'a Slice<T>) -> Self {
        SliceIter { slice, index: 0 }
    }
}

impl<'a, T> Iterator for SliceIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.slice.len() {
            let i = self.index;
            self.index += 1;
            Some(&self.slice[i])
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct List<T> {
    data: Slice<T>,
    len: usize,
}

impl<T> List<T> {
    pub fn alloc() -> *mut List<T> {
        HEAP.allocate(mem::size_of::<List<T>>()) as *mut List<T>
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn cap(&self) -> usize {
        self.data.len
    }
}

impl<T: Copy> List<T> {
    pub fn push_value(&mut self, value: T) {
        if self.len() == self.cap() {
            let new_cap = if self.cap() < 32 { 32 } else { self.cap() * 2 };
            let new_data = Array::<T>::alloc(new_cap);
            for i in 0..self.len() {
                unsafe {
                    *new_data.as_mut().unwrap().index_mut(i) = self[i];
                }
            }
            self.data.init(new_data, new_cap);
        }
        let i = self.len;
        self.len += 1;
        self[i] = value;
    }
}

impl<T: Set> List<T> {
    pub fn push(&mut self, v: &T) {
        if self.len() == self.cap() {
            let new_cap = if self.cap() < 32 { 32 } else { self.cap() * 2 };
            let new_data = Array::<T>::alloc(new_cap);
            for i in 0..self.len() {
                unsafe { new_data.as_mut().unwrap().index_mut(i).set(&self[i]) };
            }
            self.data.init(new_data, new_cap);
        }
        let i = self.len;
        self.len += 1;
        self[i].set(v);
    }
}

impl<T> Set for List<T> {
    fn set(&mut self, other: &List<T>) {
        self.data.set(&other.data);
        self.len = other.len;
    }
}

impl<T> Index<usize> for List<T> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        assert!(i < self.len());
        &self.data[i]
    }
}

impl<T> IndexMut<usize> for List<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        assert!(i < self.len());
        &mut self.data[i]
    }
}

#[derive(Eq, Debug, Hash, Ord, PartialEq, PartialOrd)]
pub struct String {
    pub data: Slice<u8>,
}

impl String {
    pub fn alloc() -> *mut String {
        HEAP.allocate(mem::size_of::<String>()) as *mut String
    }

    pub fn init(&mut self, data: &Slice<u8>) {
        self.data.set(data)
    }

    pub fn from_bytes(s: &[u8]) -> *mut String {
        unsafe {
            let data = Slice::<u8>::alloc_with_array(s.len());
            let data_ref = data.as_mut().unwrap();
            for (i, b) in s.iter().enumerate() {
                data_ref[i] = *b;
            }
            data as *mut String
        }
    }

    pub fn as_str(&self) -> Result<&str, Utf8Error> {
        str::from_utf8(self.data.as_slice())
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

impl Set for String {
    fn set(&mut self, other: &String) {
        self.data.set(&other.data)
    }
}

impl fmt::Display for String {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str().unwrap_or("<non utf-8 string>"))
    }
}

impl Add for &String {
    type Output = *const String;
    fn add(self, other: &String) -> *const String {
        unsafe {
            let len = self.len() + other.len();
            let size = mem::size_of::<String>() + len;
            let base = HEAP.allocate(size);
            let s = (base as *mut String).as_mut().unwrap();
            let data = ((base as usize + mem::size_of::<String>()) as *mut Array<u8>)
                .as_mut()
                .unwrap();
            s.data.init(data, len);
            for i in 0..self.data.len() {
                *data.index_mut(i) = self.data[i];
            }
            for i in 0..other.data.len() {
                *data.index_mut(self.len() + i) = other.data[i];
            }
            s
        }
    }
}

#[derive(Debug)]
pub struct HashMap<K: Eq + Hash + Set, V: Set> {
    entries: Slice<HashEntry<K, V>>,
    len: usize,
}

#[derive(Debug)]
struct HashEntry<K: Eq + Hash + Set, V: Set> {
    code: usize,
    key: K,
    value: V,
}

impl<K: Eq + Hash + Set, V: Set> HashMap<K, V> {
    pub fn alloc() -> *mut HashMap<K, V> {
        HEAP.allocate(mem::size_of::<HashMap<K, V>>()) as *mut HashMap<K, V>
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn cap(&self) -> usize {
        self.entries.len
    }

    pub fn contains_key(&self, key: &K) -> bool {
        HashMap::<K, V>::lookup(&self.entries, key).is_some()
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        HashMap::<K, V>::lookup(&self.entries, key).map(|i| &self.entries[i].value)
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        HashMap::<K, V>::lookup(&self.entries, key).map(|i| &mut self.entries[i].value)
    }

    pub fn insert(&mut self, key: &K, value: &V) {
        if self.cap() == 0 || self.cap() / 2 <= self.len() {
            self.grow();
        }
        let (i, code) = HashMap::<K, V>::lookup_for_insert(&self.entries, key);
        if self.entries[i].code == 0 {
            self.len += 1;
        }
        self.entries[i].code = code;
        self.entries[i].key.set(key);
        self.entries[i].value.set(value);
    }

    fn grow(&mut self) {
        let new_cap = if self.cap() == 0 { 32 } else { self.cap() * 2 };
        let new_entries = unsafe {
            Slice::<HashEntry<K, V>>::alloc_with_array(new_cap)
                .as_mut()
                .unwrap()
        };

        for i in 0..self.cap() {
            if self.entries[i].code == 0 {
                continue;
            }
            let j = HashMap::<K, V>::lookup_for_insert_with_code(
                &new_entries,
                &self.entries[i].key,
                self.entries[i].code,
            );
            new_entries[j].set(&self.entries[i]);
        }

        self.entries.set(new_entries);
    }

    fn lookup(entries: &Slice<HashEntry<K, V>>, key: &K) -> Option<usize> {
        if entries.len == 0 {
            return None;
        }
        let mask = entries.len - 1;
        let code = HashMap::<K, V>::hash_key(&key);
        let initial = code & mask;
        let mut i = initial;
        loop {
            if entries[i].code == code && entries[i].key == *key {
                return Some(i);
            }
            if entries[i].code == 0 {
                return None;
            }
            i = (i + 1) & mask;
            if i == initial {
                return None;
            }
        }
    }

    fn lookup_for_insert(entries: &Slice<HashEntry<K, V>>, key: &K) -> (usize, usize) {
        let code = HashMap::<K, V>::hash_key(&key);
        let i = HashMap::<K, V>::lookup_for_insert_with_code(entries, key, code);
        (i, code)
    }

    fn lookup_for_insert_with_code(
        entries: &Slice<HashEntry<K, V>>,
        key: &K,
        code: usize,
    ) -> usize {
        debug_assert!(entries.len != 0);
        let mask = entries.len - 1;
        let initial = code & mask;
        let mut i = initial;
        loop {
            if (entries[i].code == code && entries[i].key == *key) || entries[i].code == 0 {
                return i;
            }
            i = (i + 1) & mask;
            debug_assert!(i != initial);
        }
    }

    fn hash_key(key: &K) -> usize {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let code = hasher.finish() as usize;
        if code == 0 {
            1
        } else {
            code
        }
    }
}

impl<K: Eq + Hash + Set, V: Set> Set for HashEntry<K, V> {
    fn set(&mut self, other: &Self) {
        self.code = other.code;
        self.key.set(&other.key);
        self.value.set(&other.value);
    }
}
