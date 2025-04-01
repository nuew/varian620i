#![forbid(unsafe_code)]
#![warn(
    clippy::nursery,
    clippy::pedantic,
    clippy::decimal_literal_representation,
    clippy::if_then_some_else_none,
    clippy::indexing_slicing,
    clippy::str_to_string,
    clippy::string_to_string,
    clippy::undocumented_unsafe_blocks,
    clippy::verbose_file_reads,
    macro_use_extern_crate,
    meta_variable_misuse,
    missing_copy_implementations,
    missing_debug_implementations,
    // missing_docs,
    rustdoc::all,
    single_use_lifetimes,
    trivial_casts,
    trivial_numeric_casts,
    unused_crate_dependencies,
    unused_import_braces,
    unused_lifetimes,
    unused_qualifications,
    unused_results,
    variant_size_differences
)]
#![allow(clippy::must_use_candidate, clippy::return_self_not_must_use)]

use std::{
    borrow::Cow,
    fmt::Debug,
    ops::{BitAndAssign, BitOrAssign, BitXorAssign, Not},
};

use bitflags::bitflags;
pub use error::VarianError;
use instruction::{
    BasicOperation, Instruction, JumpConditions, JumpMode, Operand, OverflowMode,
    RegisterChangeMode, RegisterChangeRegister, ShiftMode, ShiftRegisters,
};

mod error;
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
    + PartialOrd
    + Ord
    + Clone
    + Copy
    + Default
    + From<u16>
    + Into<usize>
    + Into<u64>
    + TryFrom<u64>
    + BitAndAssign
    + BitOrAssign
    + BitXorAssign
    + Not<Output = Self>
{
    const BITS: u32;
    fn to_u16(self) -> u16;
    fn wrapping_add(self, rhs: Self) -> Self;
    fn wrapping_sub(self, rhs: Self) -> Self;
}

impl Word for u16 {
    const BITS: u32 = Self::BITS;

    fn to_u16(self) -> u16 {
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
    p: u16,
}

impl<W: Word> Cpu<W> {
    fn pc(&mut self) -> u16 {
        let ret = self.p;
        self.p = ret.wrapping_add(1);
        ret
    }
}

bitflags! {
    #[derive(Debug, PartialEq, Eq, Clone, Hash, Default)]
    struct Control: u8 {
        const OVERFLOW = 0b000_0001;
        const HALT = 0b000_0010;
        const ERROR = 0b000_0100;
        const REPEAT = 0b000_1000;
        const SENSE_1 = 0b001_0000;
        const SENSE_2 = 0b010_0000;
        const SENSE_3 = 0b100_0000;
    }
}

#[derive(PartialEq, Eq, Clone, Hash)]
pub struct Varian620i<Word> {
    /// Magnetic core memory, 4096 words minimum, expandable in 4096-word modules to 32,768 words
    memory: Box<[Word]>,
    /// CPU registers
    cpu: Cpu<Word>,
    /// Control Register
    control: Control,
}

impl<W: Debug> Debug for Varian620i<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Varian620i")
            .field("cpu", &self.cpu)
            .field("control", &self.control)
            .finish_non_exhaustive()
    }
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
            image.len() > 0 && image.len().trailing_zeros() >= 12 && image.len() >> 12 <= 8,
            "the size of `image` must be a multiple of 4096 between 1 and 8"
        );
        Self {
            memory: image,
            cpu: Cpu::default(),
            control: Control::empty(),
        }
    }

    fn indirect(&self, mut address: u16) -> Result<u16, VarianError> {
        while address >> 15 != 0 {
            address = self
                .memory
                .get(usize::from(address & 0x7FFF))
                .ok_or(VarianError::InvalidAddressError)?
                .to_u16();
        }
        Ok(address)
    }

    fn operand_addr(&self, operand: Operand) -> Result<Option<usize>, VarianError> {
        Ok(match operand {
            Operand::Direct(addr) => Some(addr.into()),
            Operand::Relative(off) => Some(self.cpu.p.wrapping_add(off).into()),
            Operand::IndexX(off) => Some(self.cpu.x.wrapping_add(off.into()).into()),
            Operand::IndexB(off) => Some(self.cpu.b.wrapping_add(off.into()).into()),
            Operand::Indirect(addr) => Some(self.indirect(addr)?.into()),
            Operand::Immediate(_) => None,
        })
    }

    fn operand(&self, operand: Operand) -> Result<Cow<'_, W>, VarianError> {
        if let Some(a) = self.operand_addr(operand)? {
            Ok(Cow::Borrowed(
                self.memory.get(a).ok_or(VarianError::InvalidAddressError)?,
            ))
        } else if let Operand::Immediate(imm) = operand {
            Ok(Cow::Owned(imm.into()))
        } else {
            unreachable!()
        }
    }

    fn operand_mut(&mut self, operand: Operand) -> Result<&mut W, VarianError> {
        self.operand_addr(operand)
            .transpose()
            .expect("cannot mutably get an immediate")
            .and_then(|addr| {
                self.memory
                    .get_mut(addr)
                    .ok_or(VarianError::InvalidAddressError)
            })
    }

    fn step_inner(&mut self, pc: u16) -> Result<(), VarianError> {
        let insn = self
            .memory
            .get(usize::from(pc))
            .ok_or(VarianError::InvalidAddressError)?
            .to_u16();
        let insn = Instruction::decode(insn, || {
            // this will get the second part of the instruction from the next PC address, even if a
            // non-PC address for the instruction was provided. This may appear to be a bug, but it
            // is not; the manual notes that this is how the 620i actually behaves in execute mode.
            self.memory
                .get(usize::from(self.cpu.pc()))
                .copied()
                .map(W::to_u16)
                .ok_or(VarianError::InvalidAddressError)
        })?;

        match insn {
            Instruction::Hlt => self.control.insert(Control::HALT),
            Instruction::Jump {
                mode,
                conditions,
                address,
            } => {
                let mut ok = true;
                if conditions.contains(JumpConditions::OVERFLOW) {
                    ok |= self.control.contains(Control::OVERFLOW);
                }
                if conditions.contains(JumpConditions::A_GE_ZERO) {
                    ok |= self.cpu.a >= 0.into();
                }
                if conditions.contains(JumpConditions::A_LT_ZERO) {
                    ok |= self.cpu.a < 0.into();
                }
                if conditions.contains(JumpConditions::A_EQ_ZERO) {
                    ok |= self.cpu.a == 0.into();
                }
                if conditions.contains(JumpConditions::B_EQ_ZERO) {
                    ok |= self.cpu.b == 0.into();
                }
                if conditions.contains(JumpConditions::X_EQ_ZERO) {
                    ok |= self.cpu.x == 0.into();
                }
                if conditions.contains(JumpConditions::SS1_SET) {
                    ok |= self.control.contains(Control::SENSE_1);
                }
                if conditions.contains(JumpConditions::SS2_SET) {
                    ok |= self.control.contains(Control::SENSE_2);
                }
                if conditions.contains(JumpConditions::SS3_SET) {
                    ok |= self.control.contains(Control::SENSE_3);
                }
                if ok {
                    let address = self.indirect(address)?;
                    match mode {
                        JumpMode::Jump => self.cpu.p = address,
                        JumpMode::Mark => {
                            *self
                                .memory
                                .get_mut(usize::from(address.wrapping_sub(1)))
                                .ok_or(VarianError::InvalidAddressError)? =
                                W::from(self.cpu.p.wrapping_sub(1));
                            self.cpu.p = address;
                        }
                        JumpMode::Execute => self.step_inner(address)?,
                    }
                }
            }
            Instruction::Shift {
                registers,
                mode,
                count,
            } => {
                let mut r: u64 = match registers {
                    ShiftRegisters::B => self.cpu.b.into(),
                    ShiftRegisters::A => self.cpu.a.into(),
                    ShiftRegisters::Long => {
                        (Into::<u64>::into(self.cpu.a) << W::BITS) | Into::<u64>::into(self.cpu.b)
                    }
                };
                match mode {
                    ShiftMode::ArithmeticShiftLeft => r <<= count,
                    // FIXME doesn't actually rotate in word size
                    ShiftMode::LogicalRotateLeft => r = r.rotate_left(count.into()),
                    // FIXME this is a logical shift, not an arithmetic one
                    ShiftMode::ArithmeticShiftRight => r >>= count,
                    ShiftMode::LogicalShiftRight => r >>= count,
                };
                // FIXME ugly
                match registers {
                    ShiftRegisters::B => {
                        self.cpu.b = W::try_from(r & ((1 << u64::from(W::BITS)) - 1))
                            .unwrap_or_else(|_| unreachable!());
                    }
                    ShiftRegisters::A => {
                        self.cpu.a = W::try_from(r & ((1 << u64::from(W::BITS)) - 1))
                            .unwrap_or_else(|_| unreachable!());
                    }
                    ShiftRegisters::Long => {
                        self.cpu.b = W::try_from(r & ((1 << u64::from(W::BITS)) - 1))
                            .unwrap_or_else(|_| unreachable!());
                        self.cpu.a = W::try_from((r >> W::BITS) & ((1 << u64::from(W::BITS)) - 1))
                            .unwrap_or_else(|_| unreachable!());
                    }
                };
            }
            Instruction::RegisterChange {
                conditional,
                mode,
                source,
                dest,
            } => {
                if !conditional || self.control.contains(Control::OVERFLOW) {
                    let mut r: W = Default::default();
                    // Is this the right way to handle Complement?
                    if source.contains(RegisterChangeRegister::X) {
                        r |= self.cpu.x;
                    }
                    if source.contains(RegisterChangeRegister::B) {
                        r |= self.cpu.b;
                    }
                    if source.contains(RegisterChangeRegister::A) {
                        r |= self.cpu.a;
                    }
                    match mode {
                        RegisterChangeMode::Transfer => {}
                        RegisterChangeMode::Increment => r = r.wrapping_add(1.into()),
                        RegisterChangeMode::Complement => r = !r,
                        RegisterChangeMode::Decrement => r = r.wrapping_sub(1.into()),
                    }
                    // The manual doesn't say how to handle this case, but this is the only thing
                    // that seems to make sense.
                    if dest.contains(RegisterChangeRegister::X) {
                        self.cpu.x = r;
                    }
                    if dest.contains(RegisterChangeRegister::B) {
                        self.cpu.b = r;
                    }
                    if dest.contains(RegisterChangeRegister::A) {
                        self.cpu.a = r;
                    }
                }
            }
            Instruction::Overflow(OverflowMode::Set) => self.control.insert(Control::OVERFLOW),
            Instruction::Overflow(OverflowMode::Reset) => self.control.remove(Control::OVERFLOW),
            // FIXME none of these handle overflow
            Instruction::BasicOperation { operation, operand } => match operation {
                BasicOperation::Lda => self.cpu.a = *self.operand(operand)?,
                BasicOperation::Ldb => self.cpu.b = *self.operand(operand)?,
                BasicOperation::Ldx => self.cpu.x = *self.operand(operand)?,
                BasicOperation::Inr => {
                    let w = self.operand_mut(operand)?;
                    *w = w.wrapping_add(1.into());
                }
                BasicOperation::Sta => *self.operand_mut(operand)? = self.cpu.a,
                BasicOperation::Stb => *self.operand_mut(operand)? = self.cpu.b,
                BasicOperation::Stx => *self.operand_mut(operand)? = self.cpu.x,
                BasicOperation::Ora => self.cpu.a |= *self.operand(operand)?,
                BasicOperation::Add => {
                    self.cpu.a = self.cpu.a.wrapping_add(*self.operand(operand)?);
                }
                BasicOperation::Era => self.cpu.a ^= *self.operand(operand)?,
                BasicOperation::Sub => {
                    self.cpu.a = self.cpu.a.wrapping_sub(*self.operand(operand)?);
                }
                BasicOperation::Ana => self.cpu.a &= *self.operand(operand)?,
                // FIXME ugly
                BasicOperation::Mul => {
                    let r: u64 = (Into::<u64>::into(self.cpu.b)
                        * Into::<u64>::into(*self.operand(operand)?))
                        + Into::<u64>::into(self.cpu.a);
                    self.cpu.b = W::try_from(r & ((1 << u64::from(W::BITS)) - 1))
                        .unwrap_or_else(|_| unreachable!());
                    self.cpu.a = W::try_from((r >> W::BITS) & ((1 << u64::from(W::BITS)) - 1))
                        .unwrap_or_else(|_| unreachable!());
                }
                // FIXME also ugly
                BasicOperation::Div => {
                    let r: u64 = ((Into::<u64>::into(self.cpu.a) << W::BITS)
                        | Into::<u64>::into(self.cpu.b))
                        / Into::<u64>::into(*self.operand(operand)?);
                    self.cpu.b = W::try_from(r & ((1 << u64::from(W::BITS)) - 1))
                        .unwrap_or_else(|_| unreachable!());
                    self.cpu.a = W::try_from((r >> W::BITS) & ((1 << u64::from(W::BITS)) - 1))
                        .unwrap_or_else(|_| unreachable!());
                }
            },
            Instruction::InputOutput { .. } => {} // TODO
        }

        Ok(())
    }

    pub fn step(&mut self) -> Result<(), VarianError> {
        let pc = self.cpu.pc();
        self.step_inner(pc)
            .inspect_err(|_| self.control.insert(Control::HALT | Control::ERROR))
    }

    pub const fn is_halted(&self) -> bool {
        self.control.contains(Control::HALT)
    }

    pub const fn is_errored(&self) -> bool {
        self.control.contains(Control::ERROR)
    }

    pub const fn memory(&self) -> &[W] {
        &self.memory
    }

    pub const fn memory_mut(&mut self) -> &mut [W] {
        &mut self.memory
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic = "Banks must not be greater than 8."]
    fn more_than_8_banks_panic() {
        let _ = Varian620i::<u16>::new(9);
    }

    #[test]
    fn add_halt() {
        let add_rel_pc = 0o120000;
        let mut emu = Varian620i::<u16>::new(1);
        emu.memory_mut()[0] = add_rel_pc;
        emu.step().unwrap();
        emu.step().unwrap();
        assert_eq!(emu.cpu.a, add_rel_pc);
        assert!(emu.control.contains(Control::HALT));
    }
}
