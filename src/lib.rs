#![forbid(unsafe_code)]

use std::{
    borrow::Cow,
    ops::{BitAndAssign, BitOrAssign, BitXorAssign, Not},
};

use bitflags::bitflags;
use instruction::{
    BasicOperation, Instruction, Operand, OverflowMode, RegisterChangeMode, RegisterChangeRegister,
};

pub mod instruction;
mod teletype;

/// Private trait to prevent implementation of [`Word`] for arbitrary types.
trait Sealed {}

impl Sealed for u16 {}

/// A memory word for use in the Varian 620/i Emulator. Either 16 or 18 bits.
#[allow(private_bounds)]
pub trait Word:
    Sealed
    + PartialEq
    + Eq
    + Clone
    + Copy
    + Default
    + Into<usize>
    + From<u16>
    + BitAndAssign
    + BitOrAssign
    + BitXorAssign
    + Not<Output = Self>
{
    fn u16(self) -> u16;
    fn wrapping_add(self, rhs: Self) -> Self;
    fn wrapping_sub(self, rhs: Self) -> Self;
}

impl Word for u16 {
    fn u16(self) -> u16 {
        self
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_sub(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }
}

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
}

impl<W: Word> Cpu<W> {
    fn pc(&mut self) -> W {
        let ret = self.p;
        self.p = ret.wrapping_add(1.into());
        ret
    }
}

bitflags! {
    #[derive(Debug, PartialEq, Eq, Clone, Hash, Default)]
    struct Control: u8 {
        const OVERFLOW = 0b0000001;
        const HALT = 0b0000010;
        const ERROR = 0b0000100;
        const REPEAT = 0b0001000;
        const SENSE_1 = 0b0010000;
        const SENSE_2 = 0b0100000;
        const SENSE_3 = 0b1000000;
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

    /// # Panics
    /// Panics if the size of `image` is not a multiple of 4096 between 1 and 8.
    pub fn from_image(image: Box<[W]>) -> Self {
        assert!(
            image.len() > 0 && image.len() & 0xFFF == 0 && image.len() >> 12 <= 8,
            "the size of `image` must be a multiple of 4096 between 1 and 8"
        );
        Self {
            memory: image,
            cpu: Cpu::default(),
            control: Control::empty(),
        }
    }

    fn operand_addr(&self, operand: Operand) -> Option<usize> {
        Some(match operand {
            Operand::Direct(addr) => addr.into(),
            Operand::Relative(off) => self.cpu.x.wrapping_add(off.into()).into(),
            Operand::IndexX(off) => self.cpu.x.wrapping_add(off.into()).into(),
            Operand::IndexB(off) => self.cpu.x.wrapping_add(off.into()).into(),
            Operand::Indirect(_addr) => todo!(),
            Operand::Immediate(_) => return None,
        })
    }

    fn operand(&self, operand: Operand) -> Cow<'_, W> {
        if let Some(a) = self.operand_addr(operand) {
            Cow::Borrowed(&self.memory[a])
        } else if let Operand::Immediate(imm) = operand {
            Cow::Owned(imm.into())
        } else {
            unreachable!()
        }
    }

    fn operand_mut(&mut self, operand: Operand) -> &mut W {
        self.operand_addr(operand)
            .map(|addr| &mut self.memory[addr])
            .expect("cannot mutably get an immediate")
    }

    pub fn step(&mut self) {
        let insn = self.memory[self.cpu.pc().into()];
        let insn = Instruction::decode(insn.u16(), || self.memory[self.cpu.pc().into()].u16());
        if let Some(insn) = insn {
            match insn {
                Instruction::Hlt => self.control.insert(Control::HALT),
                Instruction::Jump {
                    mode,
                    conditions,
                    address,
                } => todo!(),
                Instruction::Shift {
                    registers,
                    mode,
                    count,
                } => todo!(),
                Instruction::RegisterChange {
                    conditional,
                    mode,
                    source,
                    dest,
                } => {
                    if !conditional || self.control.contains(Control::OVERFLOW) {
                        let mut r: W = Default::default();
                        if source.contains(RegisterChangeRegister::X) {
                            r |= self.cpu.x
                        }
                        if source.contains(RegisterChangeRegister::B) {
                            r |= self.cpu.b
                        }
                        if source.contains(RegisterChangeRegister::A) {
                            r |= self.cpu.a
                        }
                        match mode {
                            RegisterChangeMode::Transfer => {}
                            RegisterChangeMode::Increment => r = r.wrapping_add(1.into()),
                            RegisterChangeMode::Complement => r = !r,
                            RegisterChangeMode::Decrement => r = r.wrapping_sub(1.into()),
                        }
                        if dest.contains(RegisterChangeRegister::X) {
                            self.cpu.x = r
                        }
                        if dest.contains(RegisterChangeRegister::B) {
                            self.cpu.b = r
                        }
                        if dest.contains(RegisterChangeRegister::A) {
                            self.cpu.a = r
                        }
                    }
                }
                Instruction::Overflow(OverflowMode::Set) => self.control.insert(Control::OVERFLOW),
                Instruction::Overflow(OverflowMode::Reset) => {
                    self.control.remove(Control::OVERFLOW)
                }
                Instruction::BasicOperation { operation, operand } => match operation {
                    BasicOperation::Lda => self.cpu.a = *self.operand(operand),
                    BasicOperation::Ldb => self.cpu.b = *self.operand(operand),
                    BasicOperation::Ldx => self.cpu.x = *self.operand(operand),
                    BasicOperation::Inr => {
                        let w = self.operand_mut(operand);
                        *w = w.wrapping_add(1.into());
                    }
                    BasicOperation::Sta => *self.operand_mut(operand) = self.cpu.a,
                    BasicOperation::Stb => *self.operand_mut(operand) = self.cpu.b,
                    BasicOperation::Stx => *self.operand_mut(operand) = self.cpu.x,
                    BasicOperation::Ora => self.cpu.a |= *self.operand(operand),
                    BasicOperation::Add => {
                        self.cpu.a = self.cpu.a.wrapping_add(*self.operand(operand))
                    }
                    BasicOperation::Era => self.cpu.a ^= *self.operand(operand),
                    BasicOperation::Sub => {
                        self.cpu.a = self.cpu.a.wrapping_sub(*self.operand(operand))
                    }
                    BasicOperation::Ana => self.cpu.a &= *self.operand(operand),
                    BasicOperation::Mul => todo!(),
                    BasicOperation::Div => todo!(),
                },
                Instruction::InputOutput { operation, device } => todo!(),
            }
        } else {
            self.control.insert(Control::HALT | Control::ERROR);
        }
    }

    pub fn running(&self) -> bool {
        !self.control.contains(Control::HALT)
    }

    pub fn memory(&self) -> &[W] {
        &self.memory
    }

    pub fn memory_mut(&mut self) -> &mut [W] {
        &mut self.memory
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic = "Banks must not be greater than 8."]
    fn more_than_8_banks_panic() {
        Varian620i::<u16>::new(9);
    }

    #[test]
    fn add_halt() {
        let add_rel_pc = 0o120000;
        let mut emu = Varian620i::<u16>::new(1);
        emu.memory_mut()[0] = add_rel_pc;
        emu.step();
        emu.step();
        assert_eq!(emu.cpu.a, add_rel_pc);
        assert!(emu.control.contains(Control::HALT));
    }
}
