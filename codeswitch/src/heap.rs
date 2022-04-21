use crate::bitmap::Bitmap;
use crate::math;
use std::cmp::{Ord, Ordering, PartialOrd};
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::os::raw::c_void;
use std::sync::{Mutex, MutexGuard};

use lazy_static;
use nix::sys::mman::{self, MapFlags, ProtFlags};

/// Alignment of allocated blocks containing pointers. Pointers must be
/// word-aligned in memory, so they are placed at word-aligned offsets in blocks
/// allocated at word-aligned addresses.
pub const ALLOC_ALIGNMENT: usize = 8;

/// Modern processors high and low 48 bits for virtual addresses. We'll only
/// attempt to use lower addresses. This determines the size of the page table,
/// but it can otherwise be larger or smaller.
const ADDR_BITS: usize = 48;

/// A page is the smallest unit allocated from the system. It may be larger
/// than a virtual memory page. It should be small enough to limit fragmentation
/// but large enough to limit overhead of calling mmap / mmunmap.
const PAGE_BITS: usize = 13;
const PAGE_SIZE: usize = 1 << PAGE_BITS; // 8 KB

/// The page table is used to locate page metadata, given an address. It's
/// split into multiple levels and is sparsely populated.
const PAGE_TABLE_L1_BITS: usize = 18;
const PAGE_TABLE_L1_SIZE: usize = 1 << PAGE_TABLE_L1_BITS;
const PAGE_TABLE_L2_BITS: usize = ADDR_BITS - PAGE_TABLE_L1_BITS - PAGE_BITS;
const PAGE_TABLE_L2_SIZE: usize = 1 << PAGE_TABLE_L2_BITS;
const PAGE_BASE_ADDR: usize = PAGE_SIZE << PAGE_TABLE_L2_BITS;
const PAGE_MAX_ADDR: usize = 1 << ADDR_BITS;
const MIN_GC_THRESHOLD: usize = 1 << 20;

/// List of sizes that small allocations are rounded up to. These are copied
/// from Go and are chosen to limit waste from rounding up.
///
/// When an allocation of at most MAX_SMALL_SIZE bytes is requested, the request
/// is rounded up to the nearest class below, then allocated together with
/// blocks of that size. This reduces fragmentation and allows allocation state
/// to be tracked with a simple bitmap.
const SIZE_CLASS_SIZE: [usize; SIZE_CLASS_COUNT] = [
    0, 8, 16, 24, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 208, 224, 240, 256, 288, 320,
    352, 384, 416, 448, 480, 512, 576, 640, 704, 768, 896, 1024, 1152, 1280, 1408, 1536, 1792,
    2048, 2304, 2688, 3072, 3200, 3456, 4096, 4864, 5376, 6144, 6528, 6784, 6912, 8192, 9472, 9728,
    10240, 10880, 12288, 13568, 14336, 16384, 18432, 19072, 20480, 21760, 24576, 27264, 28672,
    32768,
];
const MAX_SMALL_SIZE: usize = SIZE_CLASS_SIZE[SIZE_CLASS_COUNT - 1];

/// List of page counts for spans of each size class. These are copied from Go
/// and are chosen to limit waste at the end of each span.
///
/// When an allocation of at most MAX_SMALL_SIZE bytes is requested, it's
/// allocated together with blocks of the same size class on a span comprised
/// of contiguous pages.
const SIZE_CLASS_PAGES: [usize; SIZE_CLASS_COUNT] = [
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 2, 3, 4, 5, 6, 1, 7, 6, 5, 4, 3, 5, 7, 2, 9, 7, 5, 8,
    3, 10, 7, 4,
];

const SIZE_CLASS_COUNT: usize = 68;

lazy_static! {
    pub static ref HEAP: Heap = Heap::new();
}

pub struct Heap {
    mu: Mutex<State>,
}

struct State {
    /// List of all spans ever allocated.
    spans: Vec<Span>,

    /// For each size class, holds the index a span with at least one free
    /// block. None if there is no such span.
    size_class_to_span_index: [Option<usize>; SIZE_CLASS_COUNT],

    page_table: PageTable,

    /// Number of bytes currently allocated to blocks.
    total_allocated_bytes: usize,

    /// Maximum value for total_allocated_bytes before triggering
    /// garbage collection.
    gc_threshold_bytes: usize,
}

impl Heap {
    fn new() -> Heap {
        Heap {
            mu: Mutex::new(State {
                spans: Vec::new(),
                size_class_to_span_index: [None; SIZE_CLASS_COUNT],
                page_table: PageTable::new(),
                total_allocated_bytes: 0,
                gc_threshold_bytes: MIN_GC_THRESHOLD,
            }),
        }
    }

    /// Allocates a block of memory of the given size in bytes, returning the
    /// address of the first byte. The block is aligned to ALLOC_ALIGNMENT, and
    /// its contents are zeroed.
    ///
    /// allocate doesn't support failure. Allocate may panic if an attempt is
    /// made to allocate more memory than is available, but it's also possible
    /// that the underlying operating system may provide virtual memory without
    /// physical memory to back it; the OS may terminate the process if anything
    /// is written to that memory, or when other processes increase memory
    /// pressure.
    pub fn allocate(&self, size: usize) -> *mut u8 {
        // TODO: OPT: don't take a global lock for all allocations.
        let mut st = self.mu.lock().unwrap();
        st.total_allocated_bytes += size;
        if st.total_allocated_bytes >= st.gc_threshold_bytes {
            st = self.collect_garbage(st);
        }
        if size < MAX_SMALL_SIZE {
            self.allocate_small(&mut st, size)
        } else {
            self.allocate_large(&mut st, size)
        }
    }

    /// Handles allocations of small blocks. Small allocations are grouped
    /// together on spans that contain blocks of the same size (size class).
    fn allocate_small(&self, st: &mut State, size: usize) -> *mut u8 {
        if size == 0 {
            return PAGE_BASE_ADDR as *mut u8;
        }

        // Round the request up to the nearest size class.
        // OPT: use a lookup table for small sizes.
        let size_class = SIZE_CLASS_SIZE.iter().position(|&sc| size <= sc).unwrap();
        let rounded_size = SIZE_CLASS_SIZE[size_class];

        // Find a span of that size class with a free block.
        // Allocate a new span if needed.
        let span_index = match st.size_class_to_span_index[size_class] {
            Some(i) => i,
            None => self.allocate_small_span(st, size_class),
        };
        let span = match &mut st.spans[span_index] {
            Span::Small(s) => s,
            _ => unreachable!(),
        };

        // Scan the allocation bitmap to find a free block.
        // Mark it as allocated.
        let block_index = span.allocs.find_first_clear().unwrap();
        span.allocs.set(block_index, true);
        span.free_block_count -= 1;
        if span.free_block_count == 0 {
            st.size_class_to_span_index[size_class] = None;
        }
        let addr = span.begin + block_index * rounded_size;
        addr as *mut u8
    }

    /// Allocates a span that will contain blocks of the same size class.
    /// The argument is a size class, not a size in bytes. Returns the index
    /// of the newly created span.
    fn allocate_small_span(&self, st: &mut State, size_class: usize) -> usize {
        let span_index = st.spans.len();
        let begin = self.allocate_span_pages(st, span_index, SIZE_CLASS_PAGES[size_class]);
        let size = SIZE_CLASS_PAGES[size_class] * PAGE_SIZE;
        let block_count = size / SIZE_CLASS_SIZE[size_class];
        st.spans
            .push(Span::Small(SmallSpan::new(begin, size, block_count)));
        span_index
    }

    /// Handles allocation of large blocks. Each large block is allocated on its
    /// own span.
    fn allocate_large(&self, st: &mut State, size: usize) -> *mut u8 {
        let span_index = st.spans.len();
        let aligned_size = math::align(size, PAGE_SIZE);
        let page_count = aligned_size / PAGE_SIZE;
        let begin = self.allocate_span_pages(st, span_index, page_count);
        st.spans
            .push(Span::Large(LargeSpan::new(begin, aligned_size)));
        begin as *mut u8
    }

    /// Allocates a contiguous range of pages to be managed by a span with
    /// the given index, which may not exist yet.
    fn allocate_span_pages(&self, st: &mut State, span_index: usize, page_count: usize) -> usize {
        let size = page_count * PAGE_SIZE;
        let mut begin = PAGE_BASE_ADDR;
        'rangeloop: while begin + size < PAGE_MAX_ADDR {
            // Find an unallocated range of pages.
            let mut p = begin;
            while p < begin + size {
                if st.page_table.find(p).is_some() {
                    begin = p + PAGE_SIZE;
                    continue 'rangeloop;
                }
                p += PAGE_SIZE;
            }

            // Attempt to map those pages.
            unsafe {
                let addr = begin as *mut c_void;
                let prot = ProtFlags::PROT_READ | ProtFlags::PROT_WRITE;
                let flags = MapFlags::MAP_PRIVATE | MapFlags::MAP_ANONYMOUS;
                let fd = -1;
                let offset = 0;
                let res = mman::mmap(addr, size, prot, flags, fd, offset);
                match res {
                    Ok(addr) if addr as usize == begin => break,
                    Ok(addr) => {
                        // The system gave us pages, but not at the address
                        // we requested. Something else might be there.
                        // Unmap and try again.
                        mman::munmap(addr, size).unwrap();
                        begin += size;
                        continue;
                    }
                    _ => {
                        begin = begin + size;
                        continue;
                    }
                }
            }
        }
        if begin == PAGE_MAX_ADDR {
            panic!("failed to allocate new virtual address space for the heap")
        }

        for i in 0..page_count {
            let addr = begin + i * PAGE_SIZE;
            st.page_table.set_allocated(addr, span_index);
        }
        begin
    }

    pub fn write_barrier(&self, from: usize, to: usize) {
        // TODO: OPT: don't take a global lock for all write barriers.
        let mut state = self.mu.lock().unwrap();
        state.write_barrier(from, to);
    }

    pub fn write_barrier_nanbox(&self, _from: usize, _to: u64) {
        // TODO: implement when there's something useful to do.
    }

    fn collect_garbage<'a>(&self, mut st: MutexGuard<'a, State>) -> MutexGuard<'a, State> {
        // TODO: implement.
        st.gc_threshold_bytes = st.total_allocated_bytes * 2;
        st
    }
}

impl State {
    fn write_barrier(&mut self, from: usize, _to: usize) {
        if let Some(page) = self.find_page(from) {
            let word_index = (from & (PAGE_SIZE - 1)) >> 3;
            page.pointers.set(word_index, true);
        }
    }

    fn find_page(&mut self, addr: usize) -> Option<&mut Page> {
        self.page_table.find_mut(addr)
    }
}

/// A contiguous range of pages containing allocatable blocks.
enum Span {
    Small(SmallSpan),
    Large(LargeSpan),
}

/// A contiguous range of pages containing multiple allocatable blocks of the
/// same size.
struct SmallSpan {
    /// Allocation bitmap for blocks within the span. A block is allocated if
    /// the corresponding bit is set.
    allocs: Bitmap,

    /// Marking bitmap for blocks within the span.
    /// Used during garbage collection.
    marks: Bitmap,

    /// Number of unallocated blocks within the span.
    free_block_count: usize,

    /// Address of the lowest byte in the span.
    begin: usize,

    /// Size of the span in bytes.
    size: usize,
}

impl SmallSpan {
    fn new(begin: usize, size: usize, block_count: usize) -> SmallSpan {
        SmallSpan {
            allocs: Bitmap::new(block_count),
            marks: Bitmap::new(block_count),
            free_block_count: block_count,
            begin,
            size,
        }
    }
}

/// A contiguous range of pages containing a single large block.
struct LargeSpan {
    /// Address of the lowest byte in the span.
    begin: usize,

    /// Size of the span in bytes.
    size: usize,
}

impl LargeSpan {
    fn new(begin: usize, size: usize) -> LargeSpan {
        LargeSpan { begin, size }
    }
}

/// An aligned chunk of memory holding allocatable bytes. Managed as part of
/// a span.
struct Page {
    /// Index of the span containing the page.
    span_index: usize,

    /// Bitmap with a bit for each word on the page. The write barrier sets
    /// bits here when pointers are written to the page.
    pointers: Bitmap,
}

impl Page {
    fn new(span_index: usize) -> Page {
        Page {
            span_index,
            pointers: Bitmap::new(PAGE_SIZE / 8),
        }
    }
}

/// Maps addresses to Pages.
///
/// PageTable is organized as a two-level table, much like the kernel data
/// structure used to map virtual addresses to physical addresses. An address
/// is divided into two parts: an index into the L1 table and an index into the
/// L2 table contained within the L1 table. The low bits of the address
/// (the offset within a page) are discarded.
///
/// OPT: use boxed arrays instead of Vec. I couldn't figure out how to allocate
/// these without overflowing the stack.
/// https://github.com/rust-lang/rust/issues/53827 has some potential
/// work-arounds.
struct PageTable(Vec<Option<Vec<Option<Box<Page>>>>>);

impl PageTable {
    fn new() -> PageTable {
        let mut l1 = Vec::new();
        l1.resize_with(PAGE_TABLE_L1_SIZE, || None);
        PageTable(l1)
    }

    fn set_allocated(&mut self, addr: usize, span_index: usize) {
        let (l1_index, l2_index) = Self::indices(addr);
        if self.0[l1_index].is_none() {
            let mut l2 = Vec::new();
            l2.resize_with(PAGE_TABLE_L2_SIZE, || None);
            self.0[l1_index] = Some(l2);
        }
        let l1 = self.0[l1_index].as_mut().unwrap();
        debug_assert!(l1[l2_index].is_none());
        l1[l2_index] = Some(Box::new(Page::new(span_index)));
    }

    fn find(&self, addr: usize) -> Option<&Page> {
        if addr < PAGE_BASE_ADDR || PAGE_MAX_ADDR <= addr {
            return None;
        }
        let (l1_index, l2_index) = Self::indices(addr);
        self.0[l1_index]
            .as_deref()
            .and_then(|l2| l2[l2_index].as_deref())
    }

    fn find_mut(&mut self, addr: usize) -> Option<&mut Page> {
        if addr < PAGE_BASE_ADDR || PAGE_MAX_ADDR <= addr {
            return None;
        }
        let (l1_index, l2_index) = Self::indices(addr);
        self.0[l1_index]
            .as_deref_mut()
            .and_then(|l2| l2[l2_index].as_deref_mut())
    }

    fn indices(addr: usize) -> (usize, usize) {
        let l2_shift = PAGE_BITS;
        let l2_mask = (1 << PAGE_TABLE_L2_BITS) - 1;
        let l2_index = (addr >> l2_shift) & l2_mask;
        let l1_shift = PAGE_BITS + PAGE_TABLE_L2_BITS;
        let l1_mask = (1 << PAGE_TABLE_L1_BITS) - 1;
        let l1_index = (addr >> l1_shift) & l1_mask;
        (l1_index, l2_index)
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

    pub fn as_ref(&self) -> Option<&T> {
        unsafe { self.p.as_ref() }
    }

    pub fn as_mut(&mut self) -> Option<&mut T> {
        unsafe { self.p.as_mut() }
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

impl<T: PartialEq> PartialEq for Ptr<T> {
    fn eq(&self, other: &Ptr<T>) -> bool {
        unsafe {
            match (self.p.as_ref(), other.p.as_ref()) {
                (None, None) => true,
                (Some(l), Some(r)) => l == r,
                _ => false,
            }
        }
    }
}

impl<T: Eq> Eq for Ptr<T> {}

impl<T: Hash> Hash for Ptr<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe {
            match self.p.as_ref() {
                Some(p) => p.hash(state),
                None => (),
            }
        }
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
    static ref HANDLE_STORAGE: Mutex<HandleStorage> = Mutex::new(HandleStorage::new());
}

const HANDLE_STORAGE_FREE_LIST_END: usize = !0;
const HANDLE_STORAGE_SLOTS_PER_CHUNK: usize = 8192;

struct HandleStorage {
    slot_chunks: Vec<Box<[usize; HANDLE_STORAGE_SLOTS_PER_CHUNK]>>,
    free_list: usize,
    next_unused_index: usize,
}

impl HandleStorage {
    fn new() -> HandleStorage {
        HandleStorage {
            slot_chunks: Vec::new(),
            free_list: HANDLE_STORAGE_FREE_LIST_END,
            next_unused_index: 0,
        }
    }

    fn make_slot<T>(&mut self) -> *mut *mut T {
        unsafe {
            if self.free_list != HANDLE_STORAGE_FREE_LIST_END {
                // Free list not empty. Take and use the first slot.
                let slot = self.free_list as *mut usize;
                self.free_list = *slot;
                slot as usize as *mut *mut T
            } else {
                // Free list empty. Use the next unallocated slot.
                let chunk_index = self.next_unused_index / HANDLE_STORAGE_SLOTS_PER_CHUNK;
                let slot_index = self.next_unused_index % HANDLE_STORAGE_SLOTS_PER_CHUNK;
                self.next_unused_index += 1;
                if chunk_index >= self.slot_chunks.len() {
                    self.slot_chunks
                        .push(Box::new([0; HANDLE_STORAGE_SLOTS_PER_CHUNK]));
                }
                &mut self.slot_chunks[chunk_index][slot_index] as *mut usize as usize as *mut *mut T
            }
        }
    }

    fn drop_slot<T>(&mut self, slot: *mut *mut T) {
        unsafe {
            let slot = slot as *mut usize;
            *slot = self.free_list;
            self.free_list = slot as usize;
        }
    }
}
