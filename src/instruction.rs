use anyhow::{bail, Context, Result};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum OpcodeClass {
    Load,         // non-standard load
    LoadReg,      // load into register
    Store,        // store from immediate
    StoreReg,     // store from register
    Arithmetic,   // 32-bit arithmetic
    Jump,         // 64-bit jumps
    Jump32,       // 32-bit jumps
    Arithmetic64, // 64-bit arithmetic
}

impl OpcodeClass {
    const MASK: u64 = 0x07;
    const LOAD: u8 = 0x00;
    const LOAD_REG: u8 = 0x01;
    const STORE: u8 = 0x02;
    const STORE_REG: u8 = 0x03;
    const ARITHMETIC: u8 = 0x04;
    const JUMP: u8 = 0x05;
    const JUMP32: u8 = 0x06;
    const ARITHMETIC64: u8 = 0x07;

    fn from_raw(instruction: u64) -> Self {
        let class = (instruction & Self::MASK) as u8;
        match class {
            Self::LOAD => Self::Load,
            Self::LOAD_REG => Self::LoadReg,
            Self::STORE => Self::Store,
            Self::STORE_REG => Self::StoreReg,
            Self::ARITHMETIC => Self::Arithmetic,
            Self::JUMP => Self::Jump,
            Self::JUMP32 => Self::Jump32,
            Self::ARITHMETIC64 => Self::Arithmetic64,
            _ => panic!("Opcode class match arms have been broken"),
        }
    }

    pub fn opcode(&self) -> u8 {
        match self {
            Self::Load => Self::LOAD,
            Self::LoadReg => Self::LOAD_REG,
            Self::Store => Self::STORE,
            Self::StoreReg => Self::STORE_REG,
            Self::Arithmetic => Self::ARITHMETIC,
            Self::Jump => Self::JUMP,
            Self::Jump32 => Self::JUMP32,
            Self::Arithmetic64 => Self::ARITHMETIC64,
        }
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

    pub fn from_raw(instruction: u64) -> Self {
        if instruction & Self::MASK == Self::MASK {
            Self::Register
        } else {
            Self::Immediate
        }
    }

    pub fn opcode(&self) -> u8 {
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

    pub fn from_raw(instruction: u64) -> Option<Self> {
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

    pub fn opcode(&self) -> u8 {
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

    pub fn from_raw(instruction: u64) -> Self {
        if instruction & Self::MASK == Self::MASK {
            Self::Big
        } else {
            Self::Little
        }
    }

    pub fn opcode(&self) -> u8 {
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
    pub fn from_raw(instruction: u64) -> Result<Self> {
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

    pub fn opcode(&self) -> u8 {
        self.class.opcode() | self.source.opcode() | self.operation.opcode() | self.order.opcode()
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

    pub fn from_raw(instruction: u64) -> Option<Self> {
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

    pub fn opcode(&self) -> u8 {
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
    pub fn from_raw(instruction: u64) -> Result<Self> {
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

    pub fn opcode(&self) -> u8 {
        self.class.opcode() | self.source.opcode() | self.operation.opcode()
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

    pub fn from_raw(instruction: u64) -> Option<Self> {
        let size = (instruction & Self::MASK) as u8;
        match size {
            Self::WORD => Some(Self::Word),
            Self::HALF_WORD => Some(Self::HalfWord),
            Self::BYTE => Some(Self::Byte),
            Self::DOUBLE_WORD => Some(Self::DoubleWord),
            _ => None,
        }
    }

    pub fn opcode(&self) -> u8 {
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

    pub fn from_raw(instruction: u64) -> Option<Self> {
        let mode = (instruction & Self::MASK) as u8;
        match mode {
            Self::IMMEDIATE => Some(Self::Immediate),
            Self::MEMORY => Some(Self::Memory),
            Self::ATOMIC => Some(Self::Atomic),
            _ => None,
        }
    }

    pub fn opcode(&self) -> u8 {
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
    pub fn from_raw(instruction: u64) -> Option<Self> {
        let src_reg = Register::get_src(instruction)?;
        match src_reg {
            Register::R0 => Some(Self::Void),
            Register::R1 => Some(Self::Map),
            Register::R2 => Some(Self::MapValue),
            Register::R3 => Some(Self::BtfId),
            Register::R4 => Some(Self::Function),
            Register::R5 => Some(Self::MapIndex),
            Register::R6 => Some(Self::MapIndexValue),
            _ => None,
        }
    }

    pub const fn register_identifier(&self) -> Register {
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
    pub fn from_raw(instruction: u64) -> Result<Self> {
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

    pub fn opcode(&self) -> u8 {
        self.class.opcode() | self.size.opcode() | self.mode.opcode()
    }

    pub fn get_class(&self) -> &OpcodeClass {
        &self.class
    }

    pub fn get_size(&self) -> &MemoryOpSize {
        &self.size
    }

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

    pub fn get_dst(instruction: u64) -> Option<Register> {
        Self::from_num(((instruction >> 8) & 0xf) as u8)
    }
    pub fn get_src(instruction: u64) -> Option<Register> {
        Self::from_num(((instruction >> 12) & 0xf) as u8)
    }

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
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Opcode {
    Arithmetic(ArithmeticInstruction),
    Jump(JumpInstruction),
    Memory(MemoryInstruction),
}

impl Opcode {
    pub fn from_raw(instruction: u64) -> Result<Self> {
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

    pub fn opcode(&self) -> u8 {
        match self {
            Self::Arithmetic(arithmetic) => arithmetic.opcode(),
            Self::Jump(jump) => jump.opcode(),
            Self::Memory(memory) => memory.opcode(),
        }
    }

    pub fn is_wide(&self) -> bool {
        if let Self::Memory(memory_instruction) = self {
            matches!(memory_instruction.get_size(), MemoryOpSize::DoubleWord)
                && matches!(memory_instruction.get_class(), OpcodeClass::Load)
        } else {
            false
        }
    }
}

#[repr(C, align(8))]
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Instruction {
    opcode: Opcode,
    dst_reg: Register,
    src_reg: Register,
    offset: i16,
    imm: i64,
}

impl Instruction {
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

    pub fn get_opcode(&self) -> Opcode {
        self.opcode
    }

    pub fn get_src_reg(&self) -> Register {
        self.src_reg
    }

    pub fn get_dst_reg(&self) -> Register {
        self.dst_reg
    }

    pub fn get_offset(&self) -> i16 {
        self.offset
    }

    pub fn get_imm(&self) -> i64 {
        self.imm
    }

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

    pub const fn add32(reg: Register, imm: i32) -> Self {
        Self::alu32(reg, imm, ArithmeticOperation::Add)
    }

    pub const fn add64(reg: Register, imm: i32) -> Self {
        Self::alu64(reg, imm, ArithmeticOperation::Add)
    }

    pub const fn addx32(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux32(dst_reg, src_reg, ArithmeticOperation::Add)
    }

    pub const fn addx64(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux64(dst_reg, src_reg, ArithmeticOperation::Add)
    }

    pub const fn sub32(reg: Register, imm: i32) -> Self {
        Self::alu32(reg, imm, ArithmeticOperation::Sub)
    }

    pub const fn sub64(reg: Register, imm: i32) -> Self {
        Self::alu64(reg, imm, ArithmeticOperation::Sub)
    }

    pub const fn subx32(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux32(dst_reg, src_reg, ArithmeticOperation::Sub)
    }

    pub const fn subx64(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux64(dst_reg, src_reg, ArithmeticOperation::Sub)
    }

    pub const fn mov32(reg: Register, imm: i32) -> Self {
        Self::alu32(reg, imm, ArithmeticOperation::Mov)
    }

    pub const fn mov64(reg: Register, imm: i32) -> Self {
        Self::alu64(reg, imm, ArithmeticOperation::Mov)
    }

    pub const fn movx32(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux32(dst_reg, src_reg, ArithmeticOperation::Mov)
    }

    pub const fn movx64(dst_reg: Register, src_reg: Register) -> Self {
        Self::alux64(dst_reg, src_reg, ArithmeticOperation::Mov)
    }

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

    pub const fn load8(reg: Register, imm: i8) -> Self {
        Self::load(reg, imm as i64, MemoryOpSize::Byte)
    }

    pub const fn load16(reg: Register, imm: i16) -> Self {
        Self::load(reg, imm as i64, MemoryOpSize::HalfWord)
    }

    pub const fn load32(reg: Register, imm: i32) -> Self {
        Self::load(reg, imm as i64, MemoryOpSize::Word)
    }

    pub const fn load64(reg: Register, imm: i64) -> Self {
        Self::load(reg, imm, MemoryOpSize::DoubleWord)
    }

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

    pub const fn loadx8(dst_reg: Register, src_reg: Register, offset: i16) -> Self {
        Self::loadx(dst_reg, src_reg, offset, MemoryOpSize::Byte)
    }

    pub const fn loadx16(dst_reg: Register, src_reg: Register, offset: i16) -> Self {
        Self::loadx(dst_reg, src_reg, offset, MemoryOpSize::HalfWord)
    }

    pub const fn loadx32(dst_reg: Register, src_reg: Register, offset: i16) -> Self {
        Self::loadx(dst_reg, src_reg, offset, MemoryOpSize::Word)
    }

    pub const fn loadx64(dst_reg: Register, src_reg: Register, offset: i16) -> Self {
        Self::loadx(dst_reg, src_reg, offset, MemoryOpSize::DoubleWord)
    }

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

    pub const fn store8(reg: Register, offset: i16, imm: i8) -> Self {
        Self::store(reg, offset, imm as i64, MemoryOpSize::Byte)
    }

    pub const fn store16(reg: Register, offset: i16, imm: i16) -> Self {
        Self::store(reg, offset, imm as i64, MemoryOpSize::HalfWord)
    }

    pub const fn store32(reg: Register, offset: i16, imm: i32) -> Self {
        Self::store(reg, offset, imm as i64, MemoryOpSize::Word)
    }

    pub const fn store64(reg: Register, offset: i16, imm: i64) -> Self {
        Self::store(reg, offset, imm, MemoryOpSize::DoubleWord)
    }

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

    pub const fn storex8(dst_reg: Register, offset: i16, src_reg: Register) -> Self {
        Self::storex(dst_reg, offset, src_reg, MemoryOpSize::Byte)
    }

    pub const fn storex16(dst_reg: Register, offset: i16, src_reg: Register) -> Self {
        Self::storex(dst_reg, offset, src_reg, MemoryOpSize::HalfWord)
    }

    pub const fn storex32(dst_reg: Register, offset: i16, src_reg: Register) -> Self {
        Self::storex(dst_reg, offset, src_reg, MemoryOpSize::Word)
    }

    pub const fn storex64(dst_reg: Register, offset: i16, src_reg: Register) -> Self {
        Self::storex(dst_reg, offset, src_reg, MemoryOpSize::DoubleWord)
    }

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
