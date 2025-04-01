use bitflags::bitflags;

use crate::VarianError;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum BasicOperation {
    /// Load A register.
    Lda,
    /// Load B register
    Ldb,
    /// Load Index register
    Ldx,
    /// Increment Memory and Replace
    Inr,
    /// Store A register
    Sta,
    /// Store B register
    Stb,
    /// Store Index register
    Stx,
    /// Inclusive-OR memory and A
    Ora,
    /// Add Memory to A
    Add,
    /// Exclusive-OR memory and A
    Era,
    /// Subtract Memory from A
    Sub,
    /// AND memory and A
    Ana,
    /// Multiply (optional)
    Mul,
    /// Divide (optional)
    Div,
}

impl BasicOperation {
    fn from_opcode(opcode: u8) -> Option<Self> {
        match opcode & 0b1111 {
            0o01 => Some(Self::Lda),
            0o02 => Some(Self::Ldb),
            0o03 => Some(Self::Ldx),
            0o04 => Some(Self::Inr),
            0o05 => Some(Self::Sta),
            0o06 => Some(Self::Stb),
            0o07 => Some(Self::Stx),
            0o11 => Some(Self::Ora),
            0o12 => Some(Self::Add),
            0o13 => Some(Self::Era),
            0o14 => Some(Self::Sub),
            0o15 => Some(Self::Ana),
            0o16 => Some(Self::Mul),
            0o17 => Some(Self::Div),
            0o00 | 0o10 => None,
            _ => unreachable!(),
        }
    }

    fn from_a(a: u16) -> Option<Self> {
        Self::from_opcode(u8::try_from(a >> 3).unwrap())
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Operand {
    /// Direct
    Direct(u16),
    /// Relative to P register
    Relative(u16),
    /// Index with X register
    IndexX(u16),
    /// Index with B register
    IndexB(u16),
    /// Multilevel indirect
    Indirect(u16),
    /// Immediate
    Immediate(u16),
}

impl Operand {
    /// # Panics
    /// Panics if `m` has any bits above position 3 set, or if `a` has any bits above position 9
    /// set.
    fn from_ma(m: u8, a: u16) -> Self {
        assert!(
            a & !0o777 == 0,
            "a must not have any bits above position 9 set"
        );
        match m {
            0b000..=0b011 => Self::Direct(((u16::from(m) & 0b11) << 9) | a),
            0b100 => Self::Relative(a),
            0b101 => Self::IndexX(a),
            0b110 => Self::IndexB(a),
            0b111 => Self::Indirect(a),
            _ => panic!("m must not have any bits above position 3 set"),
        }
    }

    fn from_x(a: u16, next: u16) -> Self {
        match a & 0b111 {
            0b000..=0b011 => Self::Immediate(next),
            0b100 => Self::Relative(next),
            0b101 => Self::IndexX(next),
            0b110 => Self::IndexB(next),
            0b111 if next & 0x8000 == 0 => Self::Direct(next),
            0b111 if next & 0x8000 != 0 => Self::Indirect(next & 0x7FFF),
            _ => panic!("m must not have any bits above position 3 set"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum JumpMode {
    Jump,
    Mark,
    Execute,
}

bitflags! {
    /// Acutal condition is logical and of all bits
    #[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
    pub struct JumpConditions: u16 {
        /// Jump if Overflow Set
        const OVERFLOW = 0b0_0000_0001;
        /// Jump if A Register Positive or Zero
        const A_GE_ZERO = 0b0_0000_0010;
        /// Jump if A Register Negative
        const A_LT_ZERO = 0b0_0000_0100;
        /// Jump if A Register Zero
        const A_EQ_ZERO = 0b0_0000_1000;
        /// Jump if B Register Zero
        const B_EQ_ZERO = 0b0_0001_0000;
        /// Jump if X Register Zero
        const X_EQ_ZERO = 0b0_0010_0000;
        /// Jump if Sense Switch 1 Set
        const SS1_SET = 0b0_0100_0000;
        /// Jump if Sense Switch 2 Set
        const SS2_SET = 0b0_1000_0000;
        /// Jump if Sense Switch 3 Set
        const SS3_SET = 0b1_0000_0000;
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum ShiftRegisters {
    B,
    A,
    Long,
}

impl ShiftRegisters {
    fn from_a(a: u16) -> Option<Self> {
        match (a >> 7) & 0b11 {
            0b00 => Some(Self::B),
            0b01 => Some(Self::A),
            0b10 => Some(Self::Long),
            0b11 => None,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum ShiftMode {
    ArithmeticShiftLeft,
    LogicalRotateLeft,
    ArithmeticShiftRight,
    LogicalShiftRight,
}

impl ShiftMode {
    fn from_a(a: u16) -> Self {
        match (a >> 5) & 0b11 {
            0b00 => Self::ArithmeticShiftLeft,
            0b01 => Self::LogicalRotateLeft,
            0b10 => Self::ArithmeticShiftRight,
            0b11 => Self::LogicalShiftRight,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum RegisterChangeMode {
    Transfer,
    Increment,
    Complement,
    Decrement,
}

impl RegisterChangeMode {
    fn from_a(a: u16) -> Self {
        match (a >> 6) & 0b11 {
            0b00 => Self::Transfer,
            0b01 => Self::Increment,
            0b10 => Self::Complement,
            0b11 => Self::Decrement,
            _ => unreachable!(),
        }
    }
}

bitflags! {
    #[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
    pub struct RegisterChangeRegister: u8 {
        const X = 0b100;
        const B = 0b010;
        const A = 0b001;
    }
}

impl RegisterChangeRegister {
    fn from_source(a: u16) -> Self {
        let field = u8::try_from((a >> 3) & 0o7).unwrap();
        Self::from_bits(field).unwrap()
    }

    fn from_dest(a: u16) -> Self {
        let field = u8::try_from(a & 0o7).unwrap();
        Self::from_bits(field).unwrap()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum OverflowMode {
    Set,
    Reset,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum IoOperation {
    /// External Control
    Exc { x: u8 },
    /// Program Sense
    Sen { x: u8, address: u16 },
    /// Input to Memory
    Ime { address: u16 },
    /// Input to A Register
    Ina,
    /// Input to B Register
    Inb,
    #[allow(clippy::doc_markdown)]
    /// Input ORed to ORed A and B
    Inab,
    /// Clear and Input to A Register
    Cia,
    /// Clear and Input to B Register
    Cib,
    /// Clear and Input to A and B
    Ciab,
    /// Output from memory
    Ome { address: u16 },
    /// Output from A Register
    Oar,
    /// Output from B Register
    Obr,
    /// Output inclusive or of A and B
    Oab,
}

impl IoOperation {
    fn parse<T>(m: u8, a: u16, next: T) -> Result<Self, VarianError>
    where
        T: FnOnce() -> Result<u16, VarianError>,
    {
        let x = u8::try_from((a >> 6) & 0o7).unwrap();
        match (m, x) {
            (0o0, _) => Ok(Self::Exc { x }),
            (0o1, _) => Ok(Self::Sen {
                x,
                address: next()?,
            }),
            (0o2, 0o0) => Ok(Self::Ime { address: next()? }),
            (0o2, 0o1) => Ok(Self::Ina),
            (0o2, 0o2) => Ok(Self::Inb),
            (0o2, 0o3) => Ok(Self::Inab),
            (0o2, 0o5) => Ok(Self::Cia),
            (0o2, 0o6) => Ok(Self::Cib),
            (0o2, 0o7) => Ok(Self::Ciab),
            (0o3, 0o0) => Ok(Self::Ome { address: next()? }),
            (0o3, 0o1) => Ok(Self::Oar),
            (0o3, 0o2) => Ok(Self::Obr),
            (0o3, 0o3) => Ok(Self::Oab),
            (0o2, 0o4) | (0o3, 0o4..=0o7) | (0o4..=0o7, _) => {
                Err(VarianError::InstructionDecodeError)
            }
            (_, 0o10..) => unreachable!(),
            (0o10.., _) => panic!("m must not have any bits above position 3 set"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Instruction {
    /// Halt
    Hlt,
    /// Jump/Jump-and-Mark Instruction Groups
    Jump {
        mode: JumpMode,
        conditions: JumpConditions,
        address: u16,
    },
    /// Shift Instruction Group
    Shift {
        registers: ShiftRegisters,
        mode: ShiftMode,
        count: u8,
    },
    /// Register Change Instruction Group
    RegisterChange {
        conditional: bool,
        mode: RegisterChangeMode,
        source: RegisterChangeRegister,
        dest: RegisterChangeRegister,
    },
    /// Set/Reset Overflow Indicator
    Overflow(OverflowMode),
    /// Single-Word Addressing + Immediate/Extended Instruction Groups
    ///
    /// The single-word addressing groups include the Load/Store, Arithmetic, and Logical
    /// instruction groups.
    BasicOperation {
        operation: BasicOperation,
        operand: Operand,
    },
    /// Input Output Instruction Group
    InputOutput { operation: IoOperation, device: u8 },
}

impl Instruction {
    pub fn decode<T>(insn: u16, next: T) -> Result<Self, VarianError>
    where
        T: FnOnce() -> Result<u16, VarianError>,
    {
        let opcode = u8::try_from(insn >> 12).unwrap();
        let m = u8::try_from((insn >> 9) & 0o7).unwrap();
        let a = insn & 0o777;
        match (opcode, m) {
            (0o00, 0o0) => Ok(Self::Hlt),
            (0o00, 0o1) => Ok(Self::Jump {
                mode: JumpMode::Jump,
                conditions: JumpConditions::from_bits(a).unwrap(),
                address: next()?,
            }),
            (0o00, 0o2) => Ok(Self::Jump {
                mode: JumpMode::Mark,
                conditions: JumpConditions::from_bits(a).unwrap(),
                address: next()?,
            }),
            (0o00, 0o3) => Ok(Self::Jump {
                mode: JumpMode::Execute,
                conditions: JumpConditions::from_bits(a).unwrap(),
                address: next()?,
            }),
            (0o00, 0o4) => Ok(Self::Shift {
                registers: ShiftRegisters::from_a(a).ok_or(VarianError::InstructionDecodeError)?,
                mode: ShiftMode::from_a(a),
                count: u8::try_from(a & 0b11111).unwrap(),
            }),
            (0o00, 0o5) => Ok(Self::RegisterChange {
                conditional: a >> 8 != 0,
                mode: RegisterChangeMode::from_a(a),
                source: RegisterChangeRegister::from_source(a),
                dest: RegisterChangeRegister::from_dest(a),
            }),
            (0o00, 0o6) => Ok(Self::BasicOperation {
                operation: BasicOperation::from_a(a).ok_or(VarianError::InstructionDecodeError)?,
                operand: Operand::from_x(a, next()?),
            }),
            (0o00, 0o7) if a == 0o400 => Ok(Self::Overflow(OverflowMode::Reset)),
            (0o00, 0o7) if a == 0o401 => Ok(Self::Overflow(OverflowMode::Set)),
            (0o00, 0o7) => Err(VarianError::InstructionDecodeError),
            (0o01..=0o07 | 0o11..=0o17, _) => Ok(Self::BasicOperation {
                operation: BasicOperation::from_opcode(opcode).unwrap(),
                operand: Operand::from_ma(m, a),
            }),
            (0o10, _) => Ok(Self::InputOutput {
                operation: IoOperation::parse(m, a, next)?,
                device: u8::try_from(a & 0o77).unwrap(),
            }),
            (0o00, 0o10..) | (0o20.., _) => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lda_direct() {
        assert_eq!(
            Instruction::decode(0o010001, || panic!()),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Lda,
                operand: Operand::Direct(0o0001)
            })
        );
    }

    #[test]
    fn ldb_relative() {
        assert_eq!(
            Instruction::decode(0o024002, || panic!()),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Ldb,
                operand: Operand::Relative(2)
            })
        );
    }

    #[test]
    fn ldx_index_x() {
        assert_eq!(
            Instruction::decode(0o035010, || panic!()),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Ldx,
                operand: Operand::IndexX(0o10)
            })
        );
    }

    #[test]
    fn sta_index_b() {
        assert_eq!(
            Instruction::decode(0o056020, || panic!()),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Sta,
                operand: Operand::IndexB(0o20)
            })
        );
    }

    #[test]
    fn stb_indirect() {
        assert_eq!(
            Instruction::decode(0o067030, || panic!()),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Stb,
                operand: Operand::Indirect(0o30)
            })
        );
    }

    #[test]
    fn stx_direct_hi() {
        assert_eq!(
            Instruction::decode(0o072001, || panic!()),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Stx,
                operand: Operand::Direct(0o2001)
            })
        );
    }

    #[test]
    fn inr_immediate() {
        assert_eq!(
            Instruction::decode(0o006040, || Ok(0o123456)),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Inr,
                operand: Operand::Immediate(0o123456)
            })
        );
    }

    #[test]
    fn add_ext_relative() {
        assert_eq!(
            Instruction::decode(0o006124, || Ok(0o076543)),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Add,
                operand: Operand::Relative(0o076543)
            })
        );
    }

    #[test]
    fn sub_ext_index_x() {
        assert_eq!(
            Instruction::decode(0o006145, || Ok(0o000000)),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Sub,
                operand: Operand::IndexX(0o000000)
            })
        );
    }

    #[test]
    fn mul_ext_index_b() {
        assert_eq!(
            Instruction::decode(0o006166, || Ok(0o177777)),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Mul,
                operand: Operand::IndexB(0o177777)
            })
        );
    }

    #[test]
    fn div_ext_direct() {
        assert_eq!(
            Instruction::decode(0o006177, || Ok(0o052525)),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Div,
                operand: Operand::Direct(0o052525)
            })
        );
    }

    #[test]
    fn ora_ext_indirect() {
        assert_eq!(
            Instruction::decode(0o006117, || Ok(0o125252)),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Ora,
                operand: Operand::Indirect(0o25252)
            })
        );
    }

    #[test]
    fn era_ext_weird_immediate_1() {
        assert_eq!(
            Instruction::decode(0o006131, || Ok(0o070707)),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Era,
                operand: Operand::Immediate(0o070707)
            })
        );
    }

    #[test]
    fn era_ext_weird_immediate_3() {
        assert_eq!(
            Instruction::decode(0o006133, || Ok(0o101010)),
            Ok(Instruction::BasicOperation {
                operation: BasicOperation::Era,
                operand: Operand::Immediate(0o101010)
            })
        );
    }

    #[test]
    fn invalid_immediate_00() {
        assert_eq!(
            Instruction::decode(0o006000, || panic!()),
            Err(VarianError::InstructionDecodeError)
        );
    }

    #[test]
    fn invalid_ext_direct_10() {
        assert_eq!(
            Instruction::decode(0o006107, || panic!()),
            Err(VarianError::InstructionDecodeError)
        );
    }

    #[test]
    fn hlt() {
        assert_eq!(
            Instruction::decode(0o000000, || panic!()),
            Ok(Instruction::Hlt)
        );
    }

    #[test]
    fn hlt_junk() {
        assert_eq!(
            Instruction::decode(0o000123, || panic!()),
            Ok(Instruction::Hlt)
        );
    }

    #[test]
    fn reg_nop() {
        assert_eq!(
            Instruction::decode(0o005000, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::empty(),
                dest: RegisterChangeRegister::empty()
            })
        );
    }

    #[test]
    fn sof() {
        assert_eq!(
            Instruction::decode(0o007401, || panic!()),
            Ok(Instruction::Overflow(OverflowMode::Set))
        );
    }

    #[test]
    fn rof() {
        assert_eq!(
            Instruction::decode(0o007400, || panic!()),
            Ok(Instruction::Overflow(OverflowMode::Reset))
        );
    }

    #[test]
    fn shift_lsra() {
        assert_eq!(
            Instruction::decode(0o004340, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::A,
                mode: ShiftMode::LogicalShiftRight,
                count: 0
            })
        );
    }

    #[test]
    fn shift_lsrb() {
        assert_eq!(
            Instruction::decode(0o004177, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::B,
                mode: ShiftMode::LogicalShiftRight,
                count: 0o37
            })
        );
    }

    #[test]
    fn shift_lrla() {
        assert_eq!(
            Instruction::decode(0o004247, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::A,
                mode: ShiftMode::LogicalRotateLeft,
                count: 0o7
            })
        );
    }

    #[test]
    fn shift_lrlb() {
        assert_eq!(
            Instruction::decode(0o004070, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::B,
                mode: ShiftMode::LogicalRotateLeft,
                count: 0o30
            })
        );
    }

    #[test]
    fn shift_llsr() {
        assert_eq!(
            Instruction::decode(0o004555, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::Long,
                mode: ShiftMode::LogicalShiftRight,
                count: 0o15
            })
        );
    }

    #[test]
    fn shift_llrl() {
        assert_eq!(
            Instruction::decode(0o004467, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::Long,
                mode: ShiftMode::LogicalRotateLeft,
                count: 0o27
            })
        );
    }

    #[test]
    fn shift_asra() {
        assert_eq!(
            Instruction::decode(0o004337, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::A,
                mode: ShiftMode::ArithmeticShiftRight,
                count: 0o37
            })
        );
    }

    #[test]
    fn shift_asla() {
        assert_eq!(
            Instruction::decode(0o004216, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::A,
                mode: ShiftMode::ArithmeticShiftLeft,
                count: 0o16
            })
        );
    }

    #[test]
    fn shift_asrb() {
        assert_eq!(
            Instruction::decode(0o004101, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::B,
                mode: ShiftMode::ArithmeticShiftRight,
                count: 0o01
            })
        );
    }

    #[test]
    fn shift_aslb() {
        assert_eq!(
            Instruction::decode(0o004007, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::B,
                mode: ShiftMode::ArithmeticShiftLeft,
                count: 0o07
            })
        );
    }

    #[test]
    fn shift_lasr() {
        assert_eq!(
            Instruction::decode(0o004510, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::Long,
                mode: ShiftMode::ArithmeticShiftRight,
                count: 0o10
            })
        );
    }

    #[test]
    fn shift_lasl() {
        assert_eq!(
            Instruction::decode(0o004420, || panic!()),
            Ok(Instruction::Shift {
                registers: ShiftRegisters::Long,
                mode: ShiftMode::ArithmeticShiftLeft,
                count: 0o20
            })
        );
    }

    #[test]
    fn reg_iar() {
        assert_eq!(
            Instruction::decode(0o005111, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Increment,
                source: RegisterChangeRegister::A,
                dest: RegisterChangeRegister::A
            })
        );
    }

    #[test]
    fn reg_ibr() {
        assert_eq!(
            Instruction::decode(0o005122, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Increment,
                source: RegisterChangeRegister::B,
                dest: RegisterChangeRegister::B
            })
        );
    }

    #[test]
    fn reg_ixr() {
        assert_eq!(
            Instruction::decode(0o005144, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Increment,
                source: RegisterChangeRegister::X,
                dest: RegisterChangeRegister::X
            })
        );
    }

    #[test]
    fn reg_dar() {
        assert_eq!(
            Instruction::decode(0o005311, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Decrement,
                source: RegisterChangeRegister::A,
                dest: RegisterChangeRegister::A
            })
        );
    }

    #[test]
    fn reg_dbr() {
        assert_eq!(
            Instruction::decode(0o005322, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Decrement,
                source: RegisterChangeRegister::B,
                dest: RegisterChangeRegister::B
            })
        );
    }

    #[test]
    fn reg_dxr() {
        assert_eq!(
            Instruction::decode(0o005344, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Decrement,
                source: RegisterChangeRegister::X,
                dest: RegisterChangeRegister::X
            })
        );
    }

    #[test]
    fn reg_cpa() {
        assert_eq!(
            Instruction::decode(0o005211, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Complement,
                source: RegisterChangeRegister::A,
                dest: RegisterChangeRegister::A
            })
        );
    }

    #[test]
    fn reg_cpb() {
        assert_eq!(
            Instruction::decode(0o005222, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Complement,
                source: RegisterChangeRegister::B,
                dest: RegisterChangeRegister::B
            })
        );
    }

    #[test]
    fn reg_cpx() {
        assert_eq!(
            Instruction::decode(0o005244, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Complement,
                source: RegisterChangeRegister::X,
                dest: RegisterChangeRegister::X
            })
        );
    }

    #[test]
    fn reg_tab() {
        assert_eq!(
            Instruction::decode(0o005012, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::A,
                dest: RegisterChangeRegister::B
            })
        );
    }

    #[test]
    fn reg_tax() {
        assert_eq!(
            Instruction::decode(0o005014, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::A,
                dest: RegisterChangeRegister::X
            })
        );
    }

    #[test]
    fn reg_tba() {
        assert_eq!(
            Instruction::decode(0o005021, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::B,
                dest: RegisterChangeRegister::A
            })
        );
    }

    #[test]
    fn reg_tbx() {
        assert_eq!(
            Instruction::decode(0o005024, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::B,
                dest: RegisterChangeRegister::X
            })
        );
    }

    #[test]
    fn reg_txa() {
        assert_eq!(
            Instruction::decode(0o005041, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::X,
                dest: RegisterChangeRegister::A
            })
        );
    }

    #[test]
    fn reg_txb() {
        assert_eq!(
            Instruction::decode(0o005042, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::X,
                dest: RegisterChangeRegister::B
            })
        );
    }

    #[test]
    fn reg_tza() {
        assert_eq!(
            Instruction::decode(0o005001, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::empty(),
                dest: RegisterChangeRegister::A
            })
        );
    }

    #[test]
    fn reg_tzb() {
        assert_eq!(
            Instruction::decode(0o005002, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::empty(),
                dest: RegisterChangeRegister::B
            })
        );
    }

    #[test]
    fn reg_tzx() {
        assert_eq!(
            Instruction::decode(0o005004, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: false,
                mode: RegisterChangeMode::Transfer,
                source: RegisterChangeRegister::empty(),
                dest: RegisterChangeRegister::X
            })
        );
    }

    #[test]
    fn reg_aofa() {
        assert_eq!(
            Instruction::decode(0o005511, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: true,
                mode: RegisterChangeMode::Increment,
                source: RegisterChangeRegister::A,
                dest: RegisterChangeRegister::A
            })
        );
    }

    #[test]
    fn reg_aofb() {
        assert_eq!(
            Instruction::decode(0o005522, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: true,
                mode: RegisterChangeMode::Increment,
                source: RegisterChangeRegister::B,
                dest: RegisterChangeRegister::B
            })
        );
    }

    #[test]
    fn reg_aofx() {
        assert_eq!(
            Instruction::decode(0o005544, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: true,
                mode: RegisterChangeMode::Increment,
                source: RegisterChangeRegister::X,
                dest: RegisterChangeRegister::X
            })
        );
    }

    #[test]
    fn reg_sofa() {
        assert_eq!(
            Instruction::decode(0o005711, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: true,
                mode: RegisterChangeMode::Decrement,
                source: RegisterChangeRegister::A,
                dest: RegisterChangeRegister::A
            })
        );
    }

    #[test]
    fn reg_sofb() {
        assert_eq!(
            Instruction::decode(0o005722, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: true,
                mode: RegisterChangeMode::Decrement,
                source: RegisterChangeRegister::B,
                dest: RegisterChangeRegister::B
            })
        );
    }

    #[test]
    fn reg_sofx() {
        assert_eq!(
            Instruction::decode(0o005744, || panic!()),
            Ok(Instruction::RegisterChange {
                conditional: true,
                mode: RegisterChangeMode::Decrement,
                source: RegisterChangeRegister::X,
                dest: RegisterChangeRegister::X
            })
        );
    }

    #[test]
    fn jmp_jmp() {
        assert_eq!(
            Instruction::decode(0o001000, || Ok(0o000000)),
            Ok(Instruction::Jump {
                mode: JumpMode::Jump,
                conditions: JumpConditions::empty(),
                address: 0o000000,
            })
        );
    }

    #[test]
    fn jmp_jofm() {
        assert_eq!(
            Instruction::decode(0o002001, || Ok(0o077777)),
            Ok(Instruction::Jump {
                mode: JumpMode::Mark,
                conditions: JumpConditions::OVERFLOW,
                address: 0o077777,
            })
        );
    }

    #[test]
    fn jmp_xap() {
        assert_eq!(
            Instruction::decode(0o003002, || Ok(0o010101)),
            Ok(Instruction::Jump {
                mode: JumpMode::Execute,
                conditions: JumpConditions::A_GE_ZERO,
                address: 0o010101,
            })
        );
    }

    #[test]
    fn jmp_jan_indirect() {
        assert_eq!(
            Instruction::decode(0o001004, || Ok(0o101010)),
            Ok(Instruction::Jump {
                mode: JumpMode::Jump,
                conditions: JumpConditions::A_LT_ZERO,
                address: 0o101010,
            })
        );
    }

    #[test]
    fn jmp_jazm_indirect() {
        assert_eq!(
            Instruction::decode(0o002010, || Ok(0o170707)),
            Ok(Instruction::Jump {
                mode: JumpMode::Mark,
                conditions: JumpConditions::A_EQ_ZERO,
                address: 0o170707,
            })
        );
    }

    #[test]
    fn jmp_xbz_indirect() {
        assert_eq!(
            Instruction::decode(0o003020, || Ok(0o100000)),
            Ok(Instruction::Jump {
                mode: JumpMode::Execute,
                conditions: JumpConditions::B_EQ_ZERO,
                address: 0o100000,
            })
        );
    }

    #[test]
    fn jmp_jxz_indirect() {
        assert_eq!(
            Instruction::decode(0o001040, || Ok(0o177777)),
            Ok(Instruction::Jump {
                mode: JumpMode::Jump,
                conditions: JumpConditions::X_EQ_ZERO,
                address: 0o177777,
            })
        );
    }

    #[test]
    fn jmp_js1() {
        assert_eq!(
            Instruction::decode(0o001100, || Ok(0o000000)),
            Ok(Instruction::Jump {
                mode: JumpMode::Jump,
                conditions: JumpConditions::SS1_SET,
                address: 0o000000,
            })
        );
    }

    #[test]
    fn jmp_js2m() {
        assert_eq!(
            Instruction::decode(0o002200, || Ok(0o000001)),
            Ok(Instruction::Jump {
                mode: JumpMode::Mark,
                conditions: JumpConditions::SS2_SET,
                address: 0o000001,
            })
        );
    }

    #[test]
    fn jmp_xs3() {
        assert_eq!(
            Instruction::decode(0o003400, || Ok(0o000002)),
            Ok(Instruction::Jump {
                mode: JumpMode::Execute,
                conditions: JumpConditions::SS3_SET,
                address: 0o000002,
            })
        );
    }

    #[test]
    fn io_exc_rtc_enable() {
        assert_eq!(
            Instruction::decode(0o100147, || panic!()),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Exc { x: 0o1 },
                device: 0o47
            })
        );
    }

    #[test]
    fn io_sen_card_char_ready() {
        assert_eq!(
            Instruction::decode(0o101130, || Ok(0o100000)),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Sen {
                    x: 0o1,
                    address: 0o100000
                },
                device: 0o30
            })
        );
    }

    #[test]
    fn io_ime_tty_read_reg_to_mem() {
        assert_eq!(
            Instruction::decode(0o102001, || Ok(0o077777)),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Ime { address: 0o077777 },
                device: 0o01
            })
        );
    }

    #[test]
    fn io_ina_buf_init_reg_to_a() {
        assert_eq!(
            Instruction::decode(0o102120, || panic!()),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Ina,
                device: 0o20
            })
        );
    }

    #[test]
    fn io_inb_tape_buf_to_b() {
        assert_eq!(
            Instruction::decode(0o102210, || panic!()),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Inb,
                device: 0o10
            })
        );
    }

    #[test]
    fn io_inab_coupler_buf_to_ab() {
        assert_eq!(
            Instruction::decode(0o102371, || panic!()),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Inab,
                device: 0o71
            })
        );
    }

    #[test]
    fn io_cia_tapectl_buf_to_a_clr() {
        assert_eq!(
            Instruction::decode(0o102510, || panic!()),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Cia,
                device: 0o10
            })
        );
    }

    #[test]
    fn io_cib_discctl_in_to_b_clr() {
        assert_eq!(
            Instruction::decode(0o102614, || panic!()),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Cib,
                device: 0o14
            })
        );
    }

    #[test]
    fn io_ciab_paper_buf_to_ab_clr() {
        assert_eq!(
            Instruction::decode(0o102737, || panic!()),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Ciab,
                device: 0o37
            })
        );
    }

    #[test]
    fn io_ome_plotter_buf_from_mem() {
        assert_eq!(
            Instruction::decode(0o103032, || Ok(0o000001)),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Ome { address: 0o000001 },
                device: 0o32
            })
        );
    }

    #[test]
    fn io_oar_interrupt_mask_from_a() {
        assert_eq!(
            Instruction::decode(0o103140, || Ok(0o000001)),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Oar,
                device: 0o40
            })
        );
    }

    #[test]
    fn io_obr_bufio_buf_from_b() {
        assert_eq!(
            Instruction::decode(0o103267, || Ok(0o000001)),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Obr,
                device: 0o67
            })
        );
    }

    #[test]
    fn io_oab_relay_contacts_from_ab() {
        assert_eq!(
            Instruction::decode(0o103377, || Ok(0o000001)),
            Ok(Instruction::InputOutput {
                operation: IoOperation::Oab,
                device: 0o77
            })
        );
    }
}
