use crate::math;

pub struct Bitmap {
    words: Vec<u64>,
    len: usize,
}

impl Bitmap {
    pub fn new(len: usize) -> Bitmap {
        let word_count = math::align(len, 64) / 64;
        Bitmap {
            words: vec![0; word_count],
            len,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn get(&self, index: usize) -> bool {
        debug_assert!(index < self.len);
        let word_index = index / 64;
        let bit_index = index % 64;
        let mask = 1 << bit_index;
        self.words[word_index] & mask != 0
    }

    pub fn set(&mut self, index: usize, bit: bool) {
        debug_assert!(index < self.len);
        let word_index = index >> 6;
        let bit_index = index & ((1 << 6) - 1);
        let word = (bit as u64) << bit_index;
        let mask = !(1 << bit_index);
        self.words[word_index] = (self.words[word_index] & mask) | word;
    }

    pub fn find_first_clear(&self) -> Option<usize> {
        self.words
            .iter()
            .position(|&w| w != u64::MAX)
            .map(|wi| wi * 64 + self.words[wi].trailing_ones() as usize)
            .filter(|&i| i < self.len)
    }
}
