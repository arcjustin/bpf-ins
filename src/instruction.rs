use anyhow::{bail, Context, Result};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum OpcodeClass {
    Load = 0x00,         // non-standard load
    LoadReg = 0x01,      // load into register
    Store = 0x02,        // store from immediate
    StoreReg = 0x03,     // store from register
    Arithmetic = 0x04,   // 32-bit arithmetic
    Jump = 0x05,         // 64-bit jumps
    Jump32 = 0x06,       // 32-bit jumps
    Arithmetic64 = 0x07, // 64-bit arithmetic
}

impl OpcodeClass {
    const MASK: u64 = 0x07;
    fn from_raw(instruction: u64) -> Self {
        let class = (instruction & Self::MASK) as u8;
        match class {
            x if x == Self::Load as u8 => Self::Load,
            x if x == Self::LoadReg as u8 => Self::LoadReg,
            x if x == Self::Store as u8 => Self::Store,
            x if x == Self::StoreReg as u8 => Self::StoreReg,
            x if x == Self::Arithmetic as u8 => Self::Arithmetic,
            x if x == Self::Jump as u8 => Self::Jump,
            x if x == Self::Jump32 as u8 => Self::Jump32,
            x if x == Self::Arithmetic64 as u8 => Self::Arithmetic64,
            _ => panic!("Opcode class match arms have been broken"),
        }
    }

    fn opcode(&self) -> u8 {
        *self as u8
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SourceOperand {
    Immediate, // use immediate for jump/arithmetic
    Register,  // use source register for jump/arithmetic
}

impl SourceOperand {
    const MASK: u64 = 0x08;
    const IMMEDIATE: u8 = 0x00;
    const REGISTER: u8 = 0x08;

    fn from_raw(instruction: u64) -> Self {
        if instruction & Self::MASK == Self::MASK {
            Self::Register
        } else {
            Self::Immediate
        }
    }

    fn opcode(&self) -> u8 {
        match self {
            Self::Register => Self::REGISTER,
            Self::Immediate => Self::IMMEDIATE,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ArithmeticOperation {
    Add, // dst += src
    Sub, // dst -= src
    Mul, // dst *= src
    Div, // dst /= src
    Or,  // dst |= src
    And, // dst &= src
    Lhs, // dst <<= src
    Rhs, // dst >>= src
    Neg, // dst = ~src
    Mod, // dst %= src
    Xor, // dst ^= src
    Mov, // dst = src
    Ash, // dst s>> src
    End, // dst = swap(dst)
}

impl ArithmeticOperation {
    const MASK: u64 = 0xf0;
    const ADD: u8 = 0x00; // dst += src
    const SUB: u8 = 0x10; // dst -= src
    const MUL: u8 = 0x20; // dst *= src
    const DIV: u8 = 0x30; // dst /= src
    const OR: u8 = 0x40; // dst |= src
    const AND: u8 = 0x50; // dst &= src
    const LHS: u8 = 0x60; // dst <<= src
    const RHS: u8 = 0x70; // dst >>= src
    const NEG: u8 = 0x80; // dst: u8 = ~src
    const MOD: u8 = 0x90; // dst %= src
    const XOR: u8 = 0xa0; // dst ^= src
    const MOV: u8 = 0xb0; // dst: u8 = src
    const ASH: u8 = 0xc0; // dst s>> src
    const END: u8 = 0xd0; // dst: u8 = swap(dst)

    fn from_raw(instruction: u64) -> Option<Self> {
        let operation = (instruction & Self::MASK) as u8;
        match operation {
            Self::ADD => Some(Self::Add),
            Self::SUB => Some(Self::Sub),
            Self::MUL => Some(Self::Mul),
            Self::DIV => Some(Self::Div),
            Self::OR => Some(Self::Or),
            Self::AND => Some(Self::And),
            Self::LHS => Some(Self::Lhs),
            Self::RHS => Some(Self::Rhs),
            Self::NEG => Some(Self::Neg),
            Self::MOD => Some(Self::Mod),
            Self::XOR => Some(Self::Xor),
            Self::MOV => Some(Self::Mov),
            Self::ASH => Some(Self::Ash),
            Self::END => Some(Self::End),
            _ => None,
        }
    }

    fn opcode(&self) -> u8 {
        match self {
            Self::Add => Self::ADD,
            Self::Sub => Self::SUB,
            Self::Mul => Self::MUL,
            Self::Div => Self::DIV,
            Self::Or => Self::OR,
            Self::And => Self::AND,
            Self::Lhs => Self::LHS,
            Self::Rhs => Self::RHS,
            Self::Neg => Self::NEG,
            Self::Mod => Self::MOD,
            Self::Xor => Self::XOR,
            Self::Mov => Self::MOV,
            Self::Ash => Self::ASH,
            Self::End => Self::END,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub enum SwapOrder {
    #[default]
    Little = 0x00,
    Big = 0x08,
}

impl SwapOrder {
    const MASK: u64 = 0x08;
    const LITTLE: u8 = 0x00;
    const BIG: u8 = 0x08;

    fn from_raw(instruction: u64) -> Self {
        if instruction & Self::MASK == Self::MASK {
            Self::Big
        } else {
            Self::Little
        }
    }

    fn opcode(&self) -> u8 {
        match self {
            Self::Big => Self::BIG,
            Self::Little => Self::LITTLE,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ArithmeticInstruction {
    class: OpcodeClass,
    source: SourceOperand,
    operation: ArithmeticOperation,
    order: SwapOrder,
}

impl ArithmeticInstruction {
    fn from_raw(instruction: u64) -> Result<Self> {
        let class = OpcodeClass::from_raw(instruction);
        match class {
            OpcodeClass::Arithmetic | OpcodeClass::Arithmetic64 => (),
            _ => bail!("Tried to decode arithmetic instruction for non-arithmetic class"),
        }

        Ok(Self {
            class,
            source: SourceOperand::from_raw(instruction),
            operation: ArithmeticOperation::from_raw(instruction)
                .context("Invalid arithmetic operation")?,
            order: SwapOrder::from_raw(instruction),
        })
    }

    fn opcode(&self) -> u8 {
        self.class.opcode() | self.source.opcode() | self.operation.opcode() | self.order.opcode()
    }

    /// Returns the opcode's class.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Opcode, OpcodeClass, Register};
    ///
    /// let instruction = Instruction::addx64(Register::R1, Register::R2);
    /// let opcode = instruction.get_opcode();
    /// assert!(matches!(opcode, Opcode::Arithmetic(_)));
    /// if let Opcode::Arithmetic(arithmetic) = opcode {
    ///     assert!(matches!(arithmetic.get_class(), OpcodeClass::Arithmetic64));
    /// }
    /// ```
    pub fn get_class(&self) -> &OpcodeClass {
        &self.class
    }

    /// Returns the opcode's source operand.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Opcode, Register, SourceOperand};
    ///
    /// let instruction = Instruction::addx64(Register::R1, Register::R2);
    /// let opcode = instruction.get_opcode();
    /// assert!(matches!(opcode, Opcode::Arithmetic(_)));
    /// if let Opcode::Arithmetic(arithmetic) = opcode {
    ///     assert!(matches!(arithmetic.get_source(), SourceOperand::Register));
    /// }
    /// ```
    pub fn get_source(&self) -> &SourceOperand {
        &self.source
    }

    /// Returns the arithmetic operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{ArithmeticOperation, Instruction, Opcode, Register};
    ///
    /// let instruction = Instruction::addx64(Register::R1, Register::R2);
    /// let opcode = instruction.get_opcode();
    /// assert!(matches!(opcode, Opcode::Arithmetic(_)));
    /// if let Opcode::Arithmetic(arithmetic) = opcode {
    ///     assert!(matches!(arithmetic.get_operation(), ArithmeticOperation::Add));
    /// }
    /// ```
    pub fn get_operation(&self) -> &ArithmeticOperation {
        &self.operation
    }

    /// Returns the operation's swap order, if the operation is ArithmeticOperation::End.
    pub fn get_order(&self) -> &SwapOrder {
        &self.order
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum JumpOperation {
    Absolute,
    IfEqual,
    IfGreater,
    IfGreaterOrEqual,
    IfAnd,
    IfNotEqual,
    IfSignedGreater,
    IfSignedGreaterOrEqual,
    Call,
    Exit,
    IfLessThan,
    IfLessThanOrEqual,
    IfSignedLessThan,
    IfSignedLessThanOrEqual,
}

impl JumpOperation {
    const MASK: u64 = 0xf0;
    const ABS: u8 = 0x00;
    const EQ: u8 = 0x10;
    const GT: u8 = 0x20;
    const GTE: u8 = 0x30;
    const AND: u8 = 0x40;
    const NEQ: u8 = 0x50;
    const SGT: u8 = 0x60;
    const SGTE: u8 = 0x70;
    const CALL: u8 = 0x80;
    const EXIT: u8 = 0x90;
    const LT: u8 = 0xa0;
    const LTE: u8 = 0xb0;
    const SLT: u8 = 0xc0;
    const SLTE: u8 = 0xd0;

    fn from_raw(instruction: u64) -> Option<Self> {
        let operation = (instruction & Self::MASK) as u8;
        match operation {
            Self::ABS => Some(Self::Absolute),
            Self::EQ => Some(Self::IfEqual),
            Self::GT => Some(Self::IfGreater),
            Self::GTE => Some(Self::IfGreaterOrEqual),
            Self::AND => Some(Self::IfAnd),
            Self::NEQ => Some(Self::IfNotEqual),
            Self::SGT => Some(Self::IfSignedGreater),
            Self::SGTE => Some(Self::IfSignedGreaterOrEqual),
            Self::CALL => Some(Self::Call),
            Self::EXIT => Some(Self::Exit),
            Self::LT => Some(Self::IfLessThan),
            Self::LTE => Some(Self::IfLessThanOrEqual),
            Self::SLT => Some(Self::IfSignedLessThan),
            Self::SLTE => Some(Self::IfSignedLessThanOrEqual),
            _ => None,
        }
    }

    fn opcode(&self) -> u8 {
        match self {
            Self::Absolute => Self::ABS,
            Self::IfEqual => Self::EQ,
            Self::IfGreater => Self::GT,
            Self::IfGreaterOrEqual => Self::GTE,
            Self::IfAnd => Self::AND,
            Self::IfNotEqual => Self::NEQ,
            Self::IfSignedGreater => Self::SGT,
            Self::IfSignedGreaterOrEqual => Self::SGTE,
            Self::Call => Self::CALL,
            Self::Exit => Self::EXIT,
            Self::IfLessThan => Self::LT,
            Self::IfLessThanOrEqual => Self::LTE,
            Self::IfSignedLessThan => Self::SLT,
            Self::IfSignedLessThanOrEqual => Self::SLTE,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct JumpInstruction {
    class: OpcodeClass,
    source: SourceOperand,
    operation: JumpOperation,
}

impl JumpInstruction {
    fn from_raw(instruction: u64) -> Result<Self> {
        let class = OpcodeClass::from_raw(instruction);
        match class {
            OpcodeClass::Jump | OpcodeClass::Jump32 => (),
            _ => bail!("Tried to decode jump instruction for non-jump class"),
        }

        Ok(Self {
            class,
            source: SourceOperand::from_raw(instruction),
            operation: JumpOperation::from_raw(instruction).context("Invalid jump operation")?,
        })
    }

    fn opcode(&self) -> u8 {
        self.class.opcode() | self.source.opcode() | self.operation.opcode()
    }

    /// Returns the opcode's class.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Opcode, OpcodeClass, Register};
    ///
    /// let instruction = Instruction::exit();
    /// let opcode = instruction.get_opcode();
    /// assert!(matches!(opcode, Opcode::Jump(_)));
    /// if let Opcode::Jump(jump) = opcode {
    ///     assert!(matches!(jump.get_class(), OpcodeClass::Jump));
    /// }
    /// ```
    pub fn get_class(&self) -> &OpcodeClass {
        &self.class
    }

    /// Returns the opcode's source operand.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Opcode, Register, SourceOperand};
    ///
    /// let instruction = Instruction::exit();
    /// let opcode = instruction.get_opcode();
    /// assert!(matches!(opcode, Opcode::Jump(_)));
    /// if let Opcode::Jump(jump) = opcode {
    ///     assert!(matches!(jump.get_source(), SourceOperand::Immediate));
    /// }
    /// ```
    pub fn get_source(&self) -> &SourceOperand {
        &self.source
    }

    /// Returns the jump operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, JumpOperation, Opcode, Register};
    ///
    /// let instruction = Instruction::exit();
    /// let opcode = instruction.get_opcode();
    /// assert!(matches!(opcode, Opcode::Jump(_)));
    /// if let Opcode::Jump(jump) = opcode {
    ///     assert!(matches!(jump.get_operation(), JumpOperation::Exit));
    /// }
    /// ```
    pub fn get_operation(&self) -> &JumpOperation {
        &self.operation
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MemoryOpSize {
    Word,
    HalfWord,
    Byte,
    DoubleWord,
}

impl MemoryOpSize {
    const MASK: u64 = 0x18;
    const WORD: u8 = 0x00;
    const HALF_WORD: u8 = 0x08;
    const BYTE: u8 = 0x10;
    const DOUBLE_WORD: u8 = 0x18;

    fn from_raw(instruction: u64) -> Option<Self> {
        let size = (instruction & Self::MASK) as u8;
        match size {
            Self::WORD => Some(Self::Word),
            Self::HALF_WORD => Some(Self::HalfWord),
            Self::BYTE => Some(Self::Byte),
            Self::DOUBLE_WORD => Some(Self::DoubleWord),
            _ => None,
        }
    }

    fn opcode(&self) -> u8 {
        match self {
            Self::Word => Self::WORD,
            Self::HalfWord => Self::HALF_WORD,
            Self::Byte => Self::BYTE,
            Self::DoubleWord => Self::DOUBLE_WORD,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MemoryOpMode {
    Immediate,
    Memory,
    Atomic,
}

impl MemoryOpMode {
    const MASK: u64 = 0xe0;
    const IMMEDIATE: u8 = 0x00;
    const MEMORY: u8 = 0x60;
    const ATOMIC: u8 = 0xc0;

    fn from_raw(instruction: u64) -> Option<Self> {
        let mode = (instruction & Self::MASK) as u8;
        match mode {
            Self::IMMEDIATE => Some(Self::Immediate),
            Self::MEMORY => Some(Self::Memory),
            Self::ATOMIC => Some(Self::Atomic),
            _ => None,
        }
    }

    fn opcode(&self) -> u8 {
        match self {
            Self::Immediate => Self::IMMEDIATE,
            Self::Memory => Self::MEMORY,
            Self::Atomic => Self::ATOMIC,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MemoryOpLoadType {
    Void,
    Map,
    MapValue,
    BtfId,
    Function,
    MapIndex,
    MapIndexValue,
}

impl MemoryOpLoadType {
    const fn register_identifier(&self) -> Register {
        match self {
            Self::Void => Register::R0,
            Self::Map => Register::R1,
            Self::MapValue => Register::R2,
            Self::BtfId => Register::R3,
            Self::Function => Register::R4,
            Self::MapIndex => Register::R5,
            Self::MapIndexValue => Register::R6,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MemoryInstruction {
    class: OpcodeClass,
    size: MemoryOpSize,
    mode: MemoryOpMode,
}

impl MemoryInstruction {
    fn from_raw(instruction: u64) -> Result<Self> {
        let class = OpcodeClass::from_raw(instruction);
        match class {
            OpcodeClass::Load
            | OpcodeClass::LoadReg
            | OpcodeClass::Store
            | OpcodeClass::StoreReg => (),
            _ => bail!("Tried to decode memory instruction for non-memory class"),
        }

        Ok(Self {
            class,
            size: MemoryOpSize::from_raw(instruction).context("Invalid memory operations size")?,
            mode: MemoryOpMode::from_raw(instruction).context("Invalid memory operation mode")?,
        })
    }

    fn opcode(&self) -> u8 {
        self.class.opcode() | self.size.opcode() | self.mode.opcode()
    }

    /// Returns the opcode's class.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Opcode, OpcodeClass, Register};
    ///
    /// let instruction = Instruction::storex64(Register::R1, 0, Register::R2);
    /// let opcode = instruction.get_opcode();
    /// assert!(matches!(opcode, Opcode::Memory(_)));
    /// if let Opcode::Memory(memory) = opcode {
    ///     assert!(matches!(memory.get_class(), OpcodeClass::StoreReg));
    /// }
    /// ```
    pub fn get_class(&self) -> &OpcodeClass {
        &self.class
    }

    /// Returns the memory operation size.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpSize, Opcode, Register};
    ///
    /// let instruction = Instruction::storex64(Register::R1, 0, Register::R2);
    /// let opcode = instruction.get_opcode();
    /// assert!(matches!(opcode, Opcode::Memory(_)));
    /// if let Opcode::Memory(memory) = opcode {
    ///     assert!(matches!(memory.get_size(), MemoryOpSize::DoubleWord));
    /// }
    /// ```
    pub fn get_size(&self) -> &MemoryOpSize {
        &self.size
    }

    /// Returns the memory operation mode.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpMode, Opcode, Register};
    ///
    /// let instruction = Instruction::storex64(Register::R1, 0, Register::R2);
    /// let opcode = instruction.get_opcode();
    /// assert!(matches!(opcode, Opcode::Memory(_)));
    /// if let Opcode::Memory(memory) = opcode {
    ///     assert!(matches!(memory.get_mode(), MemoryOpMode::Memory));
    /// }
    /// ```
    pub fn get_mode(&self) -> &MemoryOpMode {
        &self.mode
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub enum Register {
    #[default]
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
}

impl Register {
    /// Returns a register that corresponds to the given integer.
    ///
    /// # Arguments
    ///
    /// * `n` - The integer representing the register.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// assert_eq!(Register::from_num(5).unwrap(), Register::R5)
    /// ```
    pub fn from_num(n: u8) -> Option<Self> {
        match n {
            0 => Some(Self::R0),
            1 => Some(Self::R1),
            2 => Some(Self::R2),
            3 => Some(Self::R3),
            4 => Some(Self::R4),
            5 => Some(Self::R5),
            6 => Some(Self::R6),
            7 => Some(Self::R7),
            8 => Some(Self::R8),
            9 => Some(Self::R9),
            10 => Some(Self::R10),
            _ => None,
        }
    }

    /// Returns the integer representation of a register.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::Register;
    ///
    /// let register = Register::R5;
    /// assert_eq!(register.as_num(), 5)
    /// ```
    pub fn as_num(&self) -> u8 {
        match self {
            Self::R0 => 0,
            Self::R1 => 1,
            Self::R2 => 2,
            Self::R3 => 3,
            Self::R4 => 4,
            Self::R5 => 5,
            Self::R6 => 6,
            Self::R7 => 7,
            Self::R8 => 8,
            Self::R9 => 9,
            Self::R10 => 10,
        }
    }

    /// Returns the string representation of a register.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{MemoryOpSize, Register};
    ///
    /// let register = Register::R5;
    /// assert_eq!(register.as_str(MemoryOpSize::DoubleWord), "r5")
    /// ```
    pub fn as_str(&self, size: MemoryOpSize) -> &'static str {
        match (self, size) {
            (Self::R0, MemoryOpSize::Byte) => "b0",
            (Self::R1, MemoryOpSize::Byte) => "b1",
            (Self::R2, MemoryOpSize::Byte) => "b2",
            (Self::R3, MemoryOpSize::Byte) => "b3",
            (Self::R4, MemoryOpSize::Byte) => "b4",
            (Self::R5, MemoryOpSize::Byte) => "b5",
            (Self::R6, MemoryOpSize::Byte) => "b6",
            (Self::R7, MemoryOpSize::Byte) => "b7",
            (Self::R8, MemoryOpSize::Byte) => "b8",
            (Self::R9, MemoryOpSize::Byte) => "b9",
            (Self::R10, MemoryOpSize::Byte) => "b10",
            (Self::R0, MemoryOpSize::HalfWord) => "h0",
            (Self::R1, MemoryOpSize::HalfWord) => "h1",
            (Self::R2, MemoryOpSize::HalfWord) => "h2",
            (Self::R3, MemoryOpSize::HalfWord) => "h3",
            (Self::R4, MemoryOpSize::HalfWord) => "h4",
            (Self::R5, MemoryOpSize::HalfWord) => "h5",
            (Self::R6, MemoryOpSize::HalfWord) => "h6",
            (Self::R7, MemoryOpSize::HalfWord) => "h7",
            (Self::R8, MemoryOpSize::HalfWord) => "h8",
            (Self::R9, MemoryOpSize::HalfWord) => "h9",
            (Self::R10, MemoryOpSize::HalfWord) => "h10",
            (Self::R0, MemoryOpSize::Word) => "w0",
            (Self::R1, MemoryOpSize::Word) => "w1",
            (Self::R2, MemoryOpSize::Word) => "w2",
            (Self::R3, MemoryOpSize::Word) => "w3",
            (Self::R4, MemoryOpSize::Word) => "w4",
            (Self::R5, MemoryOpSize::Word) => "w5",
            (Self::R6, MemoryOpSize::Word) => "w6",
            (Self::R7, MemoryOpSize::Word) => "w7",
            (Self::R8, MemoryOpSize::Word) => "w8",
            (Self::R9, MemoryOpSize::Word) => "w9",
            (Self::R10, MemoryOpSize::Word) => "w10",
            (Self::R0, MemoryOpSize::DoubleWord) => "r0",
            (Self::R1, MemoryOpSize::DoubleWord) => "r1",
            (Self::R2, MemoryOpSize::DoubleWord) => "r2",
            (Self::R3, MemoryOpSize::DoubleWord) => "r3",
            (Self::R4, MemoryOpSize::DoubleWord) => "r4",
            (Self::R5, MemoryOpSize::DoubleWord) => "r5",
            (Self::R6, MemoryOpSize::DoubleWord) => "r6",
            (Self::R7, MemoryOpSize::DoubleWord) => "r7",
            (Self::R8, MemoryOpSize::DoubleWord) => "r8",
            (Self::R9, MemoryOpSize::DoubleWord) => "r9",
            (Self::R10, MemoryOpSize::DoubleWord) => "r10",
        }
    }

    fn get_dst(instruction: u64) -> Option<Register> {
        Self::from_num(((instruction >> 8) & 0xf) as u8)
    }

    fn get_src(instruction: u64) -> Option<Register> {
        Self::from_num(((instruction >> 12) & 0xf) as u8)
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Opcode {
    Arithmetic(ArithmeticInstruction),
    Jump(JumpInstruction),
    Memory(MemoryInstruction),
}

impl Opcode {
    fn from_raw(instruction: u64) -> Result<Self> {
        let class = OpcodeClass::from_raw(instruction);
        match class {
            OpcodeClass::Arithmetic | OpcodeClass::Arithmetic64 => Ok(Self::Arithmetic(
                ArithmeticInstruction::from_raw(instruction)?,
            )),
            OpcodeClass::Jump | OpcodeClass::Jump32 => {
                Ok(Self::Jump(JumpInstruction::from_raw(instruction)?))
            }
            OpcodeClass::Load
            | OpcodeClass::LoadReg
            | OpcodeClass::Store
            | OpcodeClass::StoreReg => Ok(Self::Memory(MemoryInstruction::from_raw(instruction)?)),
        }
    }

    fn opcode(&self) -> u8 {
        match self {
            Self::Arithmetic(arithmetic) => arithmetic.opcode(),
            Self::Jump(jump) => jump.opcode(),
            Self::Memory(memory) => memory.opcode(),
        }
    }

    fn is_wide(&self) -> bool {
        if let Self::Memory(memory_instruction) = self {
            matches!(memory_instruction.size, MemoryOpSize::DoubleWord)
                && matches!(memory_instruction.class, OpcodeClass::Load)
        } else {
            false
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Instruction {
    opcode: Opcode,
    dst_reg: Register,
    src_reg: Register,
    offset: i16,
    imm: i64,
}

impl Instruction {
    /// Given a `u64` slice, this decodes a single instruction. Since eBPF instructions
    /// can be "wide", meaning a single instruction is represented by two 64-bit values,
    /// a slice is required. The user must check if the instruction was wide by calling
    /// `is_wide` when deciding how many instructions to advance the slice before the
    /// next invocation of this function.
    ///
    /// # Arguments
    ///
    /// * `instructions` - A slice of raw eBPF instructions.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Opcode, Register};
    ///
    /// let instructions = [ 0x000000fff81a7b ];
    /// let instruction = Instruction::decode(&instructions).unwrap();
    /// assert!(matches!(instruction.get_opcode(), Opcode::Memory(_)));
    /// assert!(matches!(instruction.get_dst_reg(), Register::R10));
    /// assert!(matches!(instruction.get_src_reg(), Register::R1));
    /// assert!(matches!(instruction.get_offset(), -8));
    /// assert!(matches!(instruction.get_imm(), 0));
    /// ```
    pub fn decode(instructions: &[u64]) -> Result<Self> {
        if instructions.is_empty() {
            bail!("No instructions remaining to decode");
        }

        let opcode = Opcode::from_raw(instructions[0])?;
        let dst_reg = Register::get_dst(instructions[0]).context("Invalid destination register")?;
        let src_reg = Register::get_src(instructions[0]).context("Invalid source register")?;
        let offset = ((instructions[0] >> 16) & 0xffff) as i16;
        let mut imm = ((instructions[0] >> 32) & 0xffffffff) as i64;
        if opcode.is_wide() {
            if instructions.len() < 2 {
                bail!("Wide instruction was truncated");
            } else {
                imm |= (instructions[1] as u64 & 0xffffffff00000000) as i64;
            }
        }

        Ok(Self {
            opcode,
            dst_reg,
            src_reg,
            offset,
            imm,
        })
    }

    /// Encodes this instruction object into raw 64-bit eBPF instructions. If the
    /// instruction was wide, the second entry of the tuple is populated with the
    /// extended part of the instruction.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpSize, Register};
    ///
    /// let instruction = Instruction::load(Register::R10, 0xdeadbeef, MemoryOpSize::DoubleWord);
    /// assert!(instruction.is_wide());
    /// assert_eq!(instruction.encode(), (0xdeadbeef00000a18, Some(0)));
    /// ```
    pub fn encode(&self) -> (u64, Option<u64>) {
        let opcode = self.opcode.opcode() as u64;
        let dst_reg = self.dst_reg.as_num() as u64;
        let src_reg = self.src_reg.as_num() as u64;
        let offset = (self.offset as u64) & 0xffff;
        let imm = self.imm as u64;
        let n = opcode | (dst_reg << 8) | (src_reg << 12) | (offset << 16) | (imm << 32);
        if self.opcode.is_wide() {
            let x = imm & 0xffffffff00000000;
            (n, Some(x))
        } else {
            (n, None)
        }
    }

    /// Returns the "opcode" portion of this instruction.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpSize, Opcode, Register};
    ///
    /// let instruction = Instruction::addx64(Register::R5, Register::R6);
    /// assert!(matches!(instruction.get_opcode(), Opcode::Arithmetic(_)));
    ///
    /// let instruction = Instruction::exit();
    /// assert!(matches!(instruction.get_opcode(), Opcode::Jump(_)));
    ///
    /// let instruction = Instruction::load(Register::R10, 0xdeadbeef, MemoryOpSize::Byte);
    /// assert!(matches!(instruction.get_opcode(), Opcode::Memory(_)));
    ///
    /// let instruction = Instruction::store64(Register::R10, 0, 0xdeadbeef);
    /// assert!(matches!(instruction.get_opcode(), Opcode::Memory(_)));
    /// ```
    pub fn get_opcode(&self) -> Opcode {
        self.opcode
    }

    /// Returns "source register" portion of this instruction.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::addx64(Register::R2, Register::R3);
    /// assert_eq!(instruction.get_src_reg(), Register::R3);
    /// ```
    pub fn get_src_reg(&self) -> Register {
        self.src_reg
    }

    /// Returns "destination register" portion of this instruction.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::addx64(Register::R2, Register::R3);
    /// assert_eq!(instruction.get_dst_reg(), Register::R2);
    /// ```
    pub fn get_dst_reg(&self) -> Register {
        self.dst_reg
    }

    /// Returns the "offset" portion of this instruction.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::store64(Register::R10, -300, 0);
    /// assert_eq!(instruction.get_offset(), -300);
    /// ```
    pub fn get_offset(&self) -> i16 {
        self.offset
    }

    /// Returns the "immediate" portion of this instruction.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::store64(Register::R10, 0, 0xffbbccdd);
    /// assert_eq!(instruction.get_imm(), 0xffbbccdd);
    /// ```
    pub fn get_imm(&self) -> i64 {
        self.imm
    }

    /// Returns whether this instruction is wide or not. That is, if it's
    /// represented by two 64-bit values when encoded.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpSize, Register};
    ///
    /// let instruction = Instruction::load(Register::R9, 0xdeadbeef, MemoryOpSize::DoubleWord);
    /// assert!(instruction.is_wide());
    /// ```
    pub fn is_wide(&self) -> bool {
        self.opcode.is_wide()
    }

    /// Helper function for encoding immediate ALU instructions.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register on which the operation is performed.
    /// * `imm` - The immediate value of the operation.
    /// * `op` - The type of arithmetic operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{ArithmeticOperation, Instruction, Register};
    ///
    /// let instruction = Instruction::alu32(Register::R1, -10000, ArithmeticOperation::Add);
    /// assert_eq!(instruction.encode(), (0xffffd8f000000104, None))
    /// ```
    pub const fn alu32(reg: Register, imm: i32, op: ArithmeticOperation) -> Self {
        let opcode = Opcode::Arithmetic(ArithmeticInstruction {
            class: OpcodeClass::Arithmetic,
            source: SourceOperand::Immediate,
            operation: op,
            order: SwapOrder::Little,
        });

        Self {
            opcode,
            dst_reg: reg,
            src_reg: Register::R0,
            offset: 0,
            imm: imm as i64,
        }
    }

    /// Helper function for encoding 64-bit immediate ALU instructions.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register on which the operation is performed.
    /// * `imm` - The immediate value of the operation.
    /// * `op` - The type of arithmetic operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{ArithmeticOperation, Instruction, Register};
    ///
    /// let instruction = Instruction::alu64(Register::R1, -10000, ArithmeticOperation::Add);
    /// assert_eq!(instruction.encode(), (0xffffd8f000000107, None))
    /// ```
    pub const fn alu64(reg: Register, imm: i32, op: ArithmeticOperation) -> Self {
        let opcode = Opcode::Arithmetic(ArithmeticInstruction {
            class: OpcodeClass::Arithmetic64,
            source: SourceOperand::Immediate,
            operation: op,
            order: SwapOrder::Little,
        });

        Self {
            opcode,
            dst_reg: reg,
            src_reg: Register::R0,
            offset: 0,
            imm: imm as i64,
        }
    }

    /// Helper function for encoding register ALU instructions.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The destination register involved in the operation.
    /// * `src_reg` - The source register involved in the operation.
    /// * `op` - The type of arithmetic operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{ArithmeticOperation, Instruction, Register};
    ///
    /// let instruction = Instruction::alux32(Register::R1, Register::R2, ArithmeticOperation::Mul);
    /// assert_eq!(instruction.encode(), (0x212c, None))
    /// ```
    pub const fn alux32(dst_reg: Register, src_reg: Register, op: ArithmeticOperation) -> Self {
        let opcode = Opcode::Arithmetic(ArithmeticInstruction {
            class: OpcodeClass::Arithmetic,
            source: SourceOperand::Register,
            operation: op,
            order: SwapOrder::Little,
        });

        Self {
            opcode,
            dst_reg,
            src_reg,
            offset: 0,
            imm: 0,
        }
    }

    /// Helper function for encoding 64-bit register ALU instructions.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The destination register involved in the operation.
    /// * `src_reg` - The source register involved in the operation.
    /// * `op` - The type of arithmetic operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{ArithmeticOperation, Instruction, Register};
    ///
    /// let instruction = Instruction::alux64(Register::R1, Register::R2, ArithmeticOperation::Mul);
    /// assert_eq!(instruction.encode(), (0x212f, None))
    /// ```
    pub const fn alux64(dst_reg: Register, src_reg: Register, op: ArithmeticOperation) -> Self {
        let opcode = Opcode::Arithmetic(ArithmeticInstruction {
            class: OpcodeClass::Arithmetic64,
            source: SourceOperand::Register,
            operation: op,
            order: SwapOrder::Little,
        });

        Self {
            opcode,
            dst_reg,
            src_reg,
            offset: 0,
            imm: 0,
        }
    }

    /// Helper function for encoding 32-bit immediate add instructions. Equivalent to calling
    /// `Instruction::alu32(reg, imm, ArithmeticOperation::Add)`.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register on which the operation is performed.
    /// * `imm` - The immediate value of the operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::add32(Register::R1, -10000);
    /// assert_eq!(instruction.encode(), (0xffffd8f000000104, None))
    /// ```
    pub const fn add32(reg: Register, imm: i32) -> Self {
        Self::alu32(reg, imm, ArithmeticOperation::Add)
    }

    /// Helper function for encoding 64-bit immediate add instructions. Equivalent to calling
    /// `Instruction::alu64(reg, imm, ArithmeticOperation::Add)`.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register on which the operation is performed.
    /// * `imm` - The immediate value of the operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::add64(Register::R1, -10000);
    /// assert_eq!(instruction.encode(), (0xffffd8f000000107, None))
    /// ```
    pub const fn add64(reg: Register, imm: i32) -> Self {
        Self::alu64(reg, imm, ArithmeticOperation::Add)
    }

    /// Helper function for encoding 32-bit register add instructions. Equivalent to calling
    /// `Instruction::alux32(dst_reg, src_reg, ArithmeticOperation::Add)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The destination register involved in the operation.
    /// * `src_reg` - The source register involved in the operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{ArithmeticOperation, Instruction, Register};
    ///
    /// let instruction = Instruction::addx32(Register::R1, Register::R2);
    /// assert_eq!(instruction.encode(), (0x210c, None))
    /// ```
    pub const fn addx32(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux32(dst_reg, src_reg, ArithmeticOperation::Add)
    }

    /// Helper function for encoding 64-bit register add instructions. Equivalent to calling
    /// `Instruction::alux64(dst_reg, src_reg, ArithmeticOperation::Add)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The destination register involved in the operation.
    /// * `src_reg` - The source register involved in the operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::addx64(Register::R1, Register::R2);
    /// assert_eq!(instruction.encode(), (0x210f, None))
    /// ```
    pub const fn addx64(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux64(dst_reg, src_reg, ArithmeticOperation::Add)
    }

    /// Helper function for encoding immediate 32-bit ALU move instructions. Equivalent to
    /// calling `Instruction::alu32(reg, imm, ArithmeticOperation::Mov)`.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register involved in the operation.
    /// * `imm` - The immediate value to move into the register.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::mov32(Register::R7, 0xfffffff);
    /// assert_eq!(instruction.encode(), (0xfffffff000007b4, None))
    /// ```
    pub const fn mov32(reg: Register, imm: i32) -> Self {
        Self::alu32(reg, imm, ArithmeticOperation::Mov)
    }

    /// Helper function for encoding immediate 64-bit ALU move instructions. Equivalent to
    /// calling `Instruction::alu64(reg, imm, ArithmeticOperation::Mov)`.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register involved in the operation.
    /// * `imm` - The immediate value to move into the register.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::mov64(Register::R7, 0xfffffff);
    /// assert_eq!(instruction.encode(), (0xfffffff000007b7, None))
    /// ```
    pub const fn mov64(reg: Register, imm: i32) -> Self {
        Self::alu64(reg, imm, ArithmeticOperation::Mov)
    }

    /// Helper function for encoding register 32-bit ALU move instructions. Equivalent to
    /// calling `Instruction::alux32(dst_reg, src_reg, ArithmeticOperation::Mov)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The destination register involved in the operation.
    /// * `src_reg` - The source register involved in the operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::movx32(Register::R7, Register::R8);
    /// assert_eq!(instruction.encode(), (0x87bc, None))
    /// ```
    pub const fn movx32(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux32(dst_reg, src_reg, ArithmeticOperation::Mov)
    }

    /// Helper function for encoding register 64-bit ALU move instructions. Equivalent to
    /// calling `Instruction::alux64(dst_reg, src_reg, ArithmeticOperation::Mov)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The destination register involved in the operation.
    /// * `src_reg` - The source register involved in the operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::movx64(Register::R7, Register::R8);
    /// assert_eq!(instruction.encode(), (0x87bf, None))
    /// ```
    pub const fn movx64(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux64(dst_reg, src_reg, ArithmeticOperation::Mov)
    }

    /// Helper function for creating instructions that load values from memory.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register to load the value into.
    /// * `imm` - The memory address.
    /// * `size` - The size of the load.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpSize, Register};
    ///
    /// let instruction = Instruction::load(Register::R9, 0x7fff880000000000, MemoryOpSize::Byte);
    /// assert_eq!(instruction.encode(), (0x910, None))
    /// ```
    pub const fn load(reg: Register, imm: i64, size: MemoryOpSize) -> Self {
        let opcode = Opcode::Memory(MemoryInstruction {
            class: OpcodeClass::Load,
            size,
            mode: MemoryOpMode::Immediate,
        });

        Self {
            opcode,
            dst_reg: reg,
            src_reg: Register::R0,
            offset: 0,
            imm,
        }
    }

    /// Helper function for creating instructions that load values from memory. This is
    /// currently only used for "special" loads, ie: when loading a map fd into a register,
    /// the eBPF verifier will replace the fd number with the map's virtual address.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register to load the value into.
    /// * `imm` - The memory address.
    /// * `load_type` - The type to assign to the load.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpLoadType, Register};
    ///
    /// let instruction = Instruction::loadtype(Register::R4, 3, MemoryOpLoadType::Map);
    /// assert_eq!(instruction.encode(), (0x300001418, Some(0)));
    /// assert_eq!(instruction.get_src_reg(), Register::R1);
    /// ```
    pub const fn loadtype(reg: Register, imm: i64, load_type: MemoryOpLoadType) -> Self {
        let opcode = Opcode::Memory(MemoryInstruction {
            class: OpcodeClass::Load,
            size: MemoryOpSize::DoubleWord,
            mode: MemoryOpMode::Immediate,
        });

        Self {
            opcode,
            dst_reg: reg,
            src_reg: load_type.register_identifier(),
            offset: 0,
            imm,
        }
    }

    /// Helper function for creating instructions that load values from memory into a register
    /// using one register as the address value.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register to load the value into.
    /// * `src_reg` - The register holding the memory address.
    /// * `offset` - The offset from the address in `src_reg` to load.
    /// * `size` - The size of the value to load from the memory location.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpSize, Register};
    ///
    /// let instruction = Instruction::loadx(Register::R4, Register::R5, -16, MemoryOpSize::Byte);
    /// assert_eq!(instruction.encode(), (0xfff05471, None));
    /// assert_eq!(instruction.get_dst_reg(), Register::R4);
    /// assert_eq!(instruction.get_src_reg(), Register::R5);
    /// ```
    pub const fn loadx(
        dst_reg: Register,
        src_reg: Register,
        offset: i16,
        size: MemoryOpSize,
    ) -> Self {
        let opcode = Opcode::Memory(MemoryInstruction {
            class: OpcodeClass::LoadReg,
            size,
            mode: MemoryOpMode::Memory,
        });

        Self {
            opcode,
            dst_reg,
            src_reg,
            offset,
            imm: 0,
        }
    }

    /// Helper function for creating instructions that load a byte from memory. Equivalent
    /// to calling `Instruction::loadx(dst_reg, src_reg, offset, MemoryOpSize::Byte)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register to load the value into.
    /// * `src_reg` - The register holding the memory address.
    /// * `offset` - The offset from the address in `src_reg` to load.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::loadx8(Register::R2, Register::R3, -16);
    /// assert_eq!(instruction.encode(), (0xfff03271, None));
    /// assert_eq!(instruction.get_dst_reg(), Register::R2);
    /// assert_eq!(instruction.get_src_reg(), Register::R3);
    /// ```
    pub const fn loadx8(dst_reg: Register, src_reg: Register, offset: i16) -> Self {
        Self::loadx(dst_reg, src_reg, offset, MemoryOpSize::Byte)
    }

    /// Helper function for creating instructions that load a half word from memory. Equivalent
    /// to calling `Instruction::loadx(dst_reg, src_reg, offset, MemoryOpSize::HalfWord)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register to load the value into.
    /// * `src_reg` - The register holding the memory address.
    /// * `offset` - The offset from the address in `src_reg` to load.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::loadx16(Register::R1, Register::R2, -16);
    /// assert_eq!(instruction.encode(), (0xfff02169, None));
    /// assert_eq!(instruction.get_dst_reg(), Register::R1);
    /// assert_eq!(instruction.get_src_reg(), Register::R2);
    /// ```
    pub const fn loadx16(dst_reg: Register, src_reg: Register, offset: i16) -> Self {
        Self::loadx(dst_reg, src_reg, offset, MemoryOpSize::HalfWord)
    }

    /// Helper function for creating instructions that load a word from memory. Equivalent
    /// to calling `Instruction::loadx(dst_reg, src_reg, offset, MemoryOpSize::Word)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register to load the value into.
    /// * `src_reg` - The register holding the memory address.
    /// * `offset` - The offset from the address in `src_reg` to load.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::loadx32(Register::R8, Register::R9, -16);
    /// assert_eq!(instruction.encode(), (0xfff09861, None));
    /// assert_eq!(instruction.get_dst_reg(), Register::R8);
    /// assert_eq!(instruction.get_src_reg(), Register::R9);
    /// ```
    pub const fn loadx32(dst_reg: Register, src_reg: Register, offset: i16) -> Self {
        Self::loadx(dst_reg, src_reg, offset, MemoryOpSize::Word)
    }

    /// Helper function for creating instructions that load a double word from memory. Equivalent
    /// to calling `Instruction::loadx(dst_reg, src_reg, offset, MemoryOpSize::DoubleWord)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register to load the value into.
    /// * `src_reg` - The register holding the memory address.
    /// * `offset` - The offset from the address in `src_reg` to load.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::loadx64(Register::R7, Register::R10, -16);
    /// assert_eq!(instruction.encode(), (0xfff0a779, None));
    /// assert_eq!(instruction.get_dst_reg(), Register::R7);
    /// assert_eq!(instruction.get_src_reg(), Register::R10);
    /// ```
    pub const fn loadx64(dst_reg: Register, src_reg: Register, offset: i16) -> Self {
        Self::loadx(dst_reg, src_reg, offset, MemoryOpSize::DoubleWord)
    }

    /// Helper function for creating instructions that store immediate values to memory.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register containing the memory address.
    /// * `offset` - The offset from the address held in `reg` to store the value.
    /// * `imm` - The immediate value to store.
    /// * `size` - The size of the store operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpSize, Register};
    ///
    /// let instruction = Instruction::store(Register::R1, 2808, i64::max_value(),
    /// MemoryOpSize::DoubleWord);
    /// assert_eq!(instruction.encode(), (0xffffffff0af8017a, None));
    /// assert_eq!(instruction.get_dst_reg(), Register::R1);
    /// ```
    pub const fn store(reg: Register, offset: i16, imm: i64, size: MemoryOpSize) -> Self {
        let opcode = Opcode::Memory(MemoryInstruction {
            class: OpcodeClass::Store,
            size,
            mode: MemoryOpMode::Memory,
        });

        Self {
            opcode,
            dst_reg: reg,
            src_reg: Register::R0,
            offset,
            imm,
        }
    }

    /// Helper function for creating instructions that store a byte to a memory address.
    /// Equivalent to calling `Instruction::store(reg, offset, imm, MemoryOpSize::Byte)`.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register containing the memory address.
    /// * `offset` - The offset from the address held in `reg` to store the value.
    /// * `imm` - The immediate value to store.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::store8(Register::R2, i16::min_value(), i8::max_value());
    /// assert_eq!(instruction.get_dst_reg(), Register::R2);
    /// assert_eq!(instruction.get_offset(), i16::min_value());
    /// assert_eq!(instruction.get_imm(), i8::max_value() as i64);
    /// ```
    pub const fn store8(reg: Register, offset: i16, imm: i8) -> Self {
        Self::store(reg, offset, imm as i64, MemoryOpSize::Byte)
    }

    /// Helper function for creating instructions that store a half word to a memory address.
    /// Equivalent to calling `Instruction::store(reg, offset, imm, MemoryOpSize::HalfWord)`.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register containing the memory address.
    /// * `offset` - The offset from the address held in `reg` to store the value.
    /// * `imm` - The immediate value to store.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::store16(Register::R3, i16::max_value(), i16::min_value());
    /// assert_eq!(instruction.get_dst_reg(), Register::R3);
    /// assert_eq!(instruction.get_offset(), i16::max_value());
    /// assert_eq!(instruction.get_imm(), i16::min_value() as i64);
    /// ```
    pub const fn store16(reg: Register, offset: i16, imm: i16) -> Self {
        Self::store(reg, offset, imm as i64, MemoryOpSize::HalfWord)
    }

    /// Helper function for creating instructions that store a word to a memory address.
    /// Equivalent to calling `Instruction::store(reg, offset, imm, MemoryOpSize::Word)`.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register containing the memory address.
    /// * `offset` - The offset from the address held in `reg` to store the value.
    /// * `imm` - The immediate value to store.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::store32(Register::R4, i16::max_value(), i32::min_value());
    /// assert_eq!(instruction.get_dst_reg(), Register::R4);
    /// assert_eq!(instruction.get_offset(), i16::max_value());
    /// assert_eq!(instruction.get_imm(), i32::min_value() as i64);
    /// ```
    pub const fn store32(reg: Register, offset: i16, imm: i32) -> Self {
        Self::store(reg, offset, imm as i64, MemoryOpSize::Word)
    }

    /// Helper function for creating instructions that store a double word to a memory address.
    /// Equivalent to calling `Instruction::store(reg, offset, imm, MemoryOpSize::DoubleWord)`.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register containing the memory address.
    /// * `offset` - The offset from the address held in `reg` to store the value.
    /// * `imm` - The immediate value to store.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::store64(Register::R4, i16::max_value(), i64::min_value());
    /// assert_eq!(instruction.get_dst_reg(), Register::R4);
    /// assert_eq!(instruction.get_offset(), i16::max_value());
    /// assert_eq!(instruction.get_imm(), i64::min_value() as i64);
    /// ```
    pub const fn store64(reg: Register, offset: i16, imm: i64) -> Self {
        Self::store(reg, offset, imm, MemoryOpSize::DoubleWord)
    }

    /// Helper function or creating instructions that store register values to memory.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register holding the address of the store operation.
    /// * `offset` - The offset, from `dst_reg`, to store the value.
    /// * `src_reg` - The register holding the value to be stored.
    /// * `size` - The size of the store operation.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, MemoryOpSize, Register};
    ///
    /// let instruction = Instruction::storex(Register::R4, -128, Register::R5, MemoryOpSize::Word);
    /// assert_eq!(instruction.get_dst_reg(), Register::R4);
    /// assert_eq!(instruction.get_src_reg(), Register::R5);
    /// assert_eq!(instruction.get_offset(),-128);
    /// assert_eq!(instruction.encode(), (0xff805463, None));
    /// ```
    pub const fn storex(
        dst_reg: Register,
        offset: i16,
        src_reg: Register,
        size: MemoryOpSize,
    ) -> Self {
        let opcode = Opcode::Memory(MemoryInstruction {
            class: OpcodeClass::StoreReg,
            size,
            mode: MemoryOpMode::Memory,
        });

        Self {
            opcode,
            dst_reg,
            src_reg,
            offset,
            imm: 0,
        }
    }

    /// Helper function or creating instructions that store a byte from a register into memory.
    /// Equivalent to `Instruction::storex(dst_reg, offset, src_reg, MemoryOpSize::Byte)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register holding the address of the store operation.
    /// * `offset` - The offset, from `dst_reg`, to store the value.
    /// * `src_reg` - The register holding the value to be stored.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::storex8(Register::R4, -128, Register::R5);
    /// assert_eq!(instruction.get_dst_reg(), Register::R4);
    /// assert_eq!(instruction.get_src_reg(), Register::R5);
    /// assert_eq!(instruction.get_offset(),-128);
    /// assert_eq!(instruction.encode(), (0xff805473, None));
    /// ```
    pub const fn storex8(dst_reg: Register, offset: i16, src_reg: Register) -> Self {
        Self::storex(dst_reg, offset, src_reg, MemoryOpSize::Byte)
    }

    /// Helper function or creating instructions that store a half word from a register into memory.
    /// Equivalent to `Instruction::storex(dst_reg, offset, src_reg, MemoryOpSize::HalfWord)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register holding the address of the store operation.
    /// * `offset` - The offset, from `dst_reg`, to store the value.
    /// * `src_reg` - The register holding the value to be stored.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::storex16(Register::R4, -128, Register::R5);
    /// assert_eq!(instruction.get_dst_reg(), Register::R4);
    /// assert_eq!(instruction.get_src_reg(), Register::R5);
    /// assert_eq!(instruction.get_offset(),-128);
    /// assert_eq!(instruction.encode(), (0xff80546b, None));
    /// ```
    pub const fn storex16(dst_reg: Register, offset: i16, src_reg: Register) -> Self {
        Self::storex(dst_reg, offset, src_reg, MemoryOpSize::HalfWord)
    }

    /// Helper function or creating instructions that store a word from a register into memory.
    /// Equivalent to `Instruction::storex(dst_reg, offset, src_reg, MemoryOpSize::Word)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register holding the address of the store operation.
    /// * `offset` - The offset, from `dst_reg`, to store the value.
    /// * `src_reg` - The register holding the value to be stored.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::storex32(Register::R4, -128, Register::R5);
    /// assert_eq!(instruction.get_dst_reg(), Register::R4);
    /// assert_eq!(instruction.get_src_reg(), Register::R5);
    /// assert_eq!(instruction.get_offset(),-128);
    /// assert_eq!(instruction.encode(), (0xff805463, None));
    /// ```
    pub const fn storex32(dst_reg: Register, offset: i16, src_reg: Register) -> Self {
        Self::storex(dst_reg, offset, src_reg, MemoryOpSize::Word)
    }

    /// Helper function or creating instructions that store a double word from a register into memory.
    /// Equivalent to `Instruction::storex(dst_reg, offset, src_reg, MemoryOpSize::DoubleWord)`.
    ///
    /// # Arguments
    ///
    /// * `dst_reg` - The register holding the address of the store operation.
    /// * `offset` - The offset, from `dst_reg`, to store the value.
    /// * `src_reg` - The register holding the value to be stored.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction, Register};
    ///
    /// let instruction = Instruction::storex64(Register::R4, -128, Register::R5);
    /// assert_eq!(instruction.get_dst_reg(), Register::R4);
    /// assert_eq!(instruction.get_src_reg(), Register::R5);
    /// assert_eq!(instruction.get_offset(),-128);
    /// assert_eq!(instruction.encode(), (0xff80547b, None));
    /// ```
    pub const fn storex64(dst_reg: Register, offset: i16, src_reg: Register) -> Self {
        Self::storex(dst_reg, offset, src_reg, MemoryOpSize::DoubleWord)
    }

    /// Helper function for creating instructions that call eBPF helpers.
    ///
    /// # Arguments
    ///
    /// * `n` - The number of the helper function to call.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction};
    /// const PROBE_WRITE_USER_NUM: u32 = 36;
    ///
    /// let instruction = Instruction::call(PROBE_WRITE_USER_NUM);
    /// assert_eq!(instruction.encode(), (0x2400000085, None));
    /// ```
    pub const fn call(n: u32) -> Self {
        let opcode = Opcode::Jump(JumpInstruction {
            class: OpcodeClass::Jump,
            source: SourceOperand::Immediate,
            operation: JumpOperation::Call,
        });

        Self {
            opcode,
            dst_reg: Register::R0,
            src_reg: Register::R0,
            offset: 0,
            imm: n as i64,
        }
    }

    /// Helper function for creating an exit instruction.
    ///
    /// # Example
    /// ```
    /// use bpf_ins::{Instruction};
    ///
    /// let instruction = Instruction::exit();
    /// assert_eq!(instruction.encode(), (0x95, None));
    /// ```
    pub const fn exit() -> Self {
        let opcode = Opcode::Jump(JumpInstruction {
            class: OpcodeClass::Jump,
            source: SourceOperand::Immediate,
            operation: JumpOperation::Exit,
        });

        Self {
            opcode,
            dst_reg: Register::R0,
            src_reg: Register::R0,
            offset: 0,
            imm: 0,
        }
    }
}
