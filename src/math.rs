pub fn align(n: usize, alignment: usize) -> usize {
  (n + alignment - 1) & !(alignment - 1)
}
