use crate::bitmap::Bitmap;
use crate::math;
use std::cmp::{Ord, Ordering, PartialOrd};
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::os::raw::c_void;
use std::sync::Mutex;

use lazy_static;
use nix::sys::mman::{self, MapFlags, ProtFlags};

pub const ALLOC_ALIGNMENT: usize = 8;

const PAGE_BITS: usize = 14;
const PAGE_SIZE: usize = 1 << PAGE_BITS;
const PAGES_PER_ARENA_BITS: usize = 10;
const PAGES_PER_ARENA: usize = 1 << PAGES_PER_ARENA_BITS;
const ARENA_SIZE: usize = PAGE_SIZE * PAGES_PER_ARENA;
const ARENA_BASE_ADDR: usize = ARENA_SIZE;
const ARENA_MAX_ADDR: usize = 1 << 48;
const ARENA_BITS: usize = PAGE_BITS + PAGES_PER_ARENA_BITS;
const ARENA_L1_BITS: usize = 12;
const ARENA_L1_SIZE: usize = 1 << ARENA_L1_BITS;
const ARENA_L2_BITS: usize = 12;
const ARENA_L2_SIZE: usize = 1 << ARENA_L2_BITS;
const MAX_SMALL_SIZE: usize = PAGE_SIZE;
const SIZE_CLASS_COUNT: usize = 59;
const SMALL_SPAN_SIZE: usize = PAGE_SIZE * 16;

/// List of sizes that small allocations are rounded up to.
///
/// When an allocation of at most MAX_SMALL_SIZE bytes is requested, the request
/// is rounded up to the nearest class below, then allocated together with
/// blocks of that size. This reduces fragmentation and allows allocation state
/// to be tracked with a simple bitmap.
///
/// Based loosely on Go's heap. The actual sizes are copied from Go's heap
/// up to 4096. Go chose these sizes to limit the maximum amount of waste.
const SIZE_CLASSES: [usize; SIZE_CLASS_COUNT] = [
    8, 16, 24, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 208, 224, 240, 256, 288, 320, 352,
    384, 416, 448, 480, 512, 576, 640, 704, 768, 896, 1024, 1152, 1280, 1408, 1536, 1792, 2048,
    2304, 2688, 3072, 3200, 3456, 4096, 4864, 5376, 6144, 6528, 6784, 6912, 8192, 9472, 9728,
    10240, 10880, 12288, 13568, 14336, 16384,
];

lazy_static! {
    pub static ref HEAP: Heap = Heap {
        mu: Mutex::new(State::new()),
    };
}

pub struct Heap {
    mu: Mutex<State>,
}

impl Heap {
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
        let mut state = self.mu.lock().unwrap();
        state.allocate(size)
    }

    pub fn write_barrier(&self, from: usize, to: usize) {
        // TODO: OPT: don't take a global lock for all write barriers.
        let mut state = self.mu.lock().unwrap();
        state.write_barrier(from, to);
    }

    pub fn write_barrier_nanbox(&self, _from: usize, _to: u64) {
        // TODO: implement when there's something useful to do.
    }
}

struct State {
    /// Two-level table containing all arenas. This is structurally similar to
    /// a page table. An arena can be found for a given address by dropping the
    /// low ARENA_BITS bits, then splitting the remainder into the high
    /// ARENA_L1_BITS and the low ARENA_L2_BITS to get the indices for each
    /// layer.
    arenas: [Option<Box<[Option<Box<Arena>>; ARENA_L1_SIZE]>>; ARENA_L2_SIZE],

    /// Arena-aligned address above which no arenas have been allocated.
    /// Only increases.
    next_arena_addr: usize,

    /// List of spans holding small blocks of the same size.
    small_spans: Vec<SmallSpan>,

    /// For each size class, holds the index in small_spans of a span with
    /// at least one free block. None if there is no such span.
    size_class_to_span_index: [Option<usize>; SIZE_CLASS_COUNT],
}

impl State {
    fn new() -> State {
        const ARENA_L1_INIT: Option<Box<[Option<Box<Arena>>; ARENA_L2_SIZE]>> = None;
        State {
            arenas: [ARENA_L1_INIT; ARENA_L1_SIZE],
            next_arena_addr: ARENA_BASE_ADDR,
            small_spans: Vec::new(),
            size_class_to_span_index: [None; SIZE_CLASS_COUNT],
        }
    }

    fn allocate(&mut self, size: usize) -> *mut u8 {
        if size < MAX_SMALL_SIZE {
            self.allocate_small(size)
        } else {
            self.allocate_large(size)
        }
    }

    /// Handles allocations of small blocks. Small allocations are grouped
    /// together on spans that contain blocks of the same size (size class).
    fn allocate_small(&mut self, size: usize) -> *mut u8 {
        // Round the request up to the nearest size class.
        let size_class = SIZE_CLASSES.iter().position(|&sc| size <= sc).unwrap();
        let rounded_size = SIZE_CLASSES[size_class];

        // Find a span of that size class with a free block.
        // Allocate a new span if needed.
        let span = match self.size_class_to_span_index[size_class] {
            Some(i) => &mut self.small_spans[i],
            None => {
                let i = self.allocate_small_span(size_class);
                self.size_class_to_span_index[size_class] = Some(i);
                &mut self.small_spans[i]
            }
        };

        // Scan the allocation bitmap to find a free block.
        // Mark it as allocated.
        let block_index = span.block_alloc.find_first_clear().unwrap();
        span.block_alloc.set(block_index, true);
        span.free_block_count -= 1;
        if span.free_block_count == 0 {
            self.size_class_to_span_index[size_class] = None;
        }
        let addr = span.begin + block_index * rounded_size;
        addr as *mut u8
    }

    /// Handles allocation of large blocks. Each large block is allocated on its
    /// own span.
    fn allocate_large(&mut self, size: usize) -> *mut u8 {
        self.allocate_span(math::align(size, PAGE_SIZE)) as *mut u8
    }

    /// Allocates a span that will contain blocks of the same size class.
    /// The argument is an index into SIZE_CLASSES. The index of the newly
    /// allocated span in self.small_spans.
    fn allocate_small_span(&mut self, size_class: usize) -> usize {
        let begin = self.allocate_span(SMALL_SPAN_SIZE);
        let block_count = SMALL_SPAN_SIZE / SIZE_CLASSES[size_class];
        let span = SmallSpan {
            block_alloc: Bitmap::new(block_count),
            free_block_count: block_count,
            begin,
        };
        let span_index = self.small_spans.len();
        self.small_spans.push(span);
        span_index
    }

    /// Allocates a span of the given page-aligned size in bytes.
    /// Returns the address of the first byte in the span.
    fn allocate_span(&mut self, size: usize) -> usize {
        debug_assert!(math::is_aligned(size, PAGE_SIZE));

        fn set_range_allocated(state: &mut State, begin: usize, page_count: usize) {
            for i in 0..page_count {
                let addr = begin + i * PAGE_SIZE;
                let arena = state.find_arena(addr).unwrap();
                let page_index_within_arena = (addr - arena.begin) / PAGE_SIZE;
                arena.pages[page_index_within_arena] = Some(Page::new());
            }
        }

        // Try to find a contiguous range of free pages within existing arenas.
        // The range may cross contiguous arenas.
        let page_count = size / PAGE_SIZE;
        let mut begin_page_index = 0;
        let mut end_page_index = 0;
        let mut arena_opt = self.find_next_arena(ARENA_BASE_ADDR);
        while let Some(arena) = arena_opt {
            let arena_page_index = arena.begin / PAGE_SIZE;
            if arena_page_index != end_page_index {
                // Either this is the first arena, or the arena is not
                // contiguous with the previous arena. Reset the range.
                begin_page_index = arena_page_index;
                end_page_index = arena_page_index;
            }
            for _ in 0..PAGES_PER_ARENA {
                let page_index_within_arena = end_page_index - arena_page_index;
                if arena.pages[page_index_within_arena].is_some() {
                    // Page is allocated. Reset the range.
                    begin_page_index = end_page_index + 1;
                    end_page_index += 1;
                } else {
                    // Page is not allocated. Extend the range.
                    end_page_index += 1;
                    if end_page_index - begin_page_index == page_count {
                        let begin = begin_page_index * PAGE_SIZE;
                        set_range_allocated(self, begin, page_count);
                        return begin;
                    }
                }
            }
            let next = arena.begin + ARENA_SIZE;
            arena_opt = self.find_next_arena(next);
        }

        // No range found. Allocate new arenas.
        // TODO: OPT: if the highest arena has free pages at the end, try to use
        // those pages in the span, and possibly allocate one less arena.
        let arena_count = math::align(page_count, PAGES_PER_ARENA) / PAGES_PER_ARENA;
        let begin = self.allocate_arenas(arena_count);
        set_range_allocated(self, begin, page_count);
        begin
    }

    /// Allocates memory from the OS to hold the given number of arenas.
    /// The memory is allocated as one anonymous private mapped region
    /// at an arena-aligned address.
    fn allocate_arenas(&mut self, arena_count: usize) -> usize {
        // Attempt to allocate memory for the arenas at the next address.
        // The allocation may fail if something else is already mapped there,
        // so keep incrementing the address until we succeed.
        let mut begin: usize = 0;
        while self.next_arena_addr < ARENA_MAX_ADDR {
            unsafe {
                let addr = self.next_arena_addr as *mut c_void;
                self.next_arena_addr += ARENA_SIZE;
                let length = arena_count * ARENA_SIZE;
                let prot = ProtFlags::PROT_READ | ProtFlags::PROT_WRITE;
                let flags = MapFlags::MAP_PRIVATE | MapFlags::MAP_ANONYMOUS | MapFlags::MAP_FIXED;
                let fd = -1;
                let offset = 0;
                let res = mman::mmap(addr, length, prot, flags, fd, offset);
                if let Ok(addr) = res {
                    begin = addr as usize;
                    break;
                }
            }
        }
        if begin == 0 {
            panic!("failed to allocate new virtual address space for the heap")
        }

        // Initialize arena metadata.
        for i in 0..arena_count {
            let addr = begin + i * ARENA_SIZE;
            let l1_index = (addr >> (ARENA_BITS + ARENA_L2_BITS)) & ((1 << ARENA_L1_BITS) - 1);
            if self.arenas[l1_index].is_none() {
                const ARENA_L2_INIT: Option<Box<Arena>> = None;
                self.arenas[l1_index] = Some(Box::new([ARENA_L2_INIT; ARENA_L2_SIZE]));
            }
            let l2_index = (addr >> ARENA_BITS) & ((1 << ARENA_L2_BITS) - 1);
            self.arenas[l1_index].as_mut().unwrap()[l2_index] = Some(Box::new(Arena::new(addr)));
        }
        begin
    }

    fn write_barrier(&mut self, from: usize, _to: usize) {
        if let Some(page) = self.find_page(from) {
            let word_index = (from & (PAGE_SIZE - 1)) >> 3;
            page.pointers.set(word_index, true);
        }
    }

    /// Returns the arena containing the given address if there is one,
    /// or None if the address is not on the heap.
    fn find_arena(&mut self, addr: usize) -> Option<&mut Arena> {
        if addr < ARENA_BASE_ADDR || addr >= ARENA_MAX_ADDR {
            return None;
        }
        let l1_index = (addr >> (ARENA_BITS + ARENA_L2_BITS)) & ((1 << ARENA_L1_BITS) - 1);
        let l2_index = (addr >> ARENA_BITS) & ((1 << ARENA_L2_BITS) - 1);
        self.arenas[l1_index]
            .as_mut()
            .and_then(|l1| l1[l2_index].as_mut())
            .map(|a| a.as_mut())
    }

    /// Returns the arena containing the given address or the next arena with a
    /// higher address, if there is one. Used to iterate over arenas.
    fn find_next_arena(&mut self, addr: usize) -> Option<&mut Arena> {
        if addr < ARENA_BASE_ADDR || addr >= ARENA_MAX_ADDR {
            return None;
        }
        let mut l1_index = (addr >> (ARENA_BITS + ARENA_L2_BITS)) & ((1 << ARENA_L1_BITS) - 1);
        let mut l2_index = (addr >> ARENA_BITS) & ((1 << ARENA_L2_BITS) - 1);
        'outer: while l1_index < ARENA_L1_SIZE {
            if let Some(l1) = &self.arenas[l1_index] {
                while l2_index < ARENA_L2_SIZE {
                    if l1[l2_index].is_some() {
                        break 'outer;
                    }
                    l2_index += 1;
                }
            }
            l1_index += 1;
            l2_index = 0;
        }
        if l1_index < ARENA_L1_SIZE {
            let l1 = self.arenas[l1_index].as_mut().unwrap().as_mut();
            let a = l1[l2_index].as_mut().unwrap().as_mut();
            Some(a)
        } else {
            None
        }
    }

    fn find_page(&mut self, addr: usize) -> Option<&mut Page> {
        self.find_arena(addr).and_then(|arena| {
            let page_index_within_arena = (addr >> PAGE_BITS) & (PAGES_PER_ARENA - 1);
            arena.pages[page_index_within_arena].as_mut()
        })
    }
}

/// A chunk of memory allocated directly from the operating system. ARENA_SIZE
/// is both the size in bytes and alignment.
struct Arena {
    /// Address of the lowest byte in the arena. Aligned to ARENA_SIZE.
    begin: usize,

    /// List of pages within the arena. Some if allocated to a span,
    /// None if not.
    pages: [Option<Page>; PAGES_PER_ARENA],
}

impl Arena {
    fn new(begin: usize) -> Arena {
        const PAGES_INIT: Option<Page> = None;
        Arena {
            begin,
            pages: [PAGES_INIT; PAGES_PER_ARENA],
        }
    }
}

/// An aligned chunk of memory dedicated to some specific purpose. Exists within
/// an arena, which consists of a constant number of pages. Each page is part
/// of a span, which may cross arena boundaries.
struct Page {
    /// Tracks whether each word on the page contains a pointer. Bits are set
    /// by the write barrier.
    // TODO: OPT: don't allocate a bitmap if we know the page won't contain
    // any pointers.
    pointers: Bitmap,
}

impl Page {
    fn new() -> Page {
        Page {
            pointers: Bitmap::new(PAGE_SIZE / 8),
        }
    }
}

/// A contiguous range of pages containing blocks of the same size. The span may
/// cross multiple arenas.
struct SmallSpan {
    /// Allocation bitmap for blocks within the span. A block is allocated if
    /// the corresponding bit is set.
    block_alloc: Bitmap,

    /// Number of unallocated blocks within the span.
    free_block_count: usize,

    /// Address of the lowest byte in the span.
    begin: usize,
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
