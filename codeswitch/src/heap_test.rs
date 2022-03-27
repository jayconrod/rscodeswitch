use crate::heap::{Handle, HEAP};
use std::slice;

/// Allocates blocks of random size on the heap and verifies they are zeroed.
/// Fills each block with ones to verify the heap doesn't return a block that
/// was allocated earlier.
#[test]
fn alloc_test() {
    const MAX_SIZE: usize = 17000; // A little more than MAX_SMALL_SIZE.
    const MAX_ALLOCATED: usize = 8 << 20;
    const LARGE_PRIME: usize = 99999199999;
    let mut handles = Vec::new();
    let mut size = 1;
    let mut total_allocated = 0;
    while total_allocated < MAX_ALLOCATED {
        let addr = HEAP.allocate(size);
        let s = unsafe { slice::from_raw_parts_mut(addr, size) };
        assert!(s.iter().all(|b| *b == 0));
        s.fill(1);
        handles.push(Handle::new(addr));
        total_allocated += size;
        size = (size + LARGE_PRIME) % MAX_SIZE + 1;
    }
}
