#![forbid(unsafe_code)]

use bitflags::bitflags;

pub mod instruction;

/// Private trait to prevent implementation of [`Word`] for arbitrary types.
trait Sealed {}

impl Sealed for i16 {}

/// A memory word for use in the Varian 620/i Emulator. Either 16 or 18 bits.
#[allow(private_bounds)]
pub trait Word: Sealed + PartialEq + Eq + PartialOrd + Ord + Clone + Copy + Default {}

impl Word for i16 {}

/// 5 bit word
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Default)]
struct Shift(u8);

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Default)]
struct Cpu<Word> {
    /// Accumulator, input/output
    a: Word,
    /// Low-order accumulator, input/output, index register
    b: Word,
    /// Index register, multi-purpose register
    x: Word,
    /// Instruction counter
    p: Word,
    /// Instruction register
    u: u16,
    /// Memory address register
    l: u16,
    /// Memory word register
    w: Word,
    /// Shift register
    s: Shift,
    /// Operand register
    r: Word,
}

bitflags! {
    #[derive(Debug, PartialEq, Eq, Clone, Hash, Default)]
    struct Control: u8 {
        const REPEAT = 0b0001;
        const SENSE_1 = 0b0010;
        const SENSE_2 = 0b0100;
        const SENSE_3 = 0b1000;
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Varian620i<Word> {
    /// Magnetic core memory, 4096 words minimum, expandable in 4096-word modules to 32,768 words
    memory: Box<[Word]>,
    /// CPU registers
    cpu: Cpu<Word>,
    /// Control Register
    control: Control,
}

impl<W: Word> Varian620i<W> {
    /// Number of words per memory bank.
    const WORDS_PER_BANK: usize = 4096;

    /// Maximum number of banks supported.
    const MAX_BANKS: u8 = 8;

    /// # Panics
    /// Panics if `banks` is greater than 8 (the maximum number of banks allowed by the Varian 620/i).
    pub fn new(banks: u8) -> Self {
        assert!(
            banks <= Self::MAX_BANKS,
            "Banks must not be greater than 8."
        );
        Self {
            memory: std::iter::repeat(W::default())
                .take(usize::from(banks) * Self::WORDS_PER_BANK)
                .collect(),
            cpu: Cpu::default(),
            control: Control::empty(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic = "Banks must not be greater than 8."]
    fn more_than_8_banks_panic() {
        Varian620i::<i16>::new(9);
    }
}
