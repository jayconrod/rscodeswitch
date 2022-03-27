pub fn align(n: usize, alignment: usize) -> usize {
    (n + alignment - 1) & !(alignment - 1)
}

pub fn is_aligned(n: usize, alignment: usize) -> bool {
    align(n, alignment) == n
}
