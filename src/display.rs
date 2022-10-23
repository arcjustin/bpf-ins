use crate::{
    ArithmeticInstruction, ArithmeticOperation, Instruction, JumpInstruction, JumpOperation,
    MemoryInstruction, MemoryOpSize, Opcode, OpcodeClass, SourceOperand,
};

use std::fmt;

fn get_dst_src_str(
    instruction: &Instruction,
    size: MemoryOpSize,
    source: SourceOperand,
) -> (&'static str, String) {
    let dst_str = instruction.get_dst_reg().as_str(size);
    let src_str = if matches!(source, SourceOperand::Register) {
        instruction.get_src_reg().as_str(size).to_owned()
    } else {
        instruction.get_imm().to_string()
    };

    (dst_str, src_str)
}

fn display_arithmetic(
    instruction: &Instruction,
    arithmetic: ArithmeticInstruction,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    let (dst_str, src_str) = get_dst_src_str(
        instruction,
        MemoryOpSize::DoubleWord,
        *arithmetic.get_source(),
    );
    let op_str = match arithmetic.get_operation() {
        ArithmeticOperation::Add => "+",
        ArithmeticOperation::Sub => "-",
        ArithmeticOperation::Mul => "*",
        ArithmeticOperation::Div => "/",
        ArithmeticOperation::Or => "|",
        ArithmeticOperation::And => "&",
        ArithmeticOperation::Lhs => "<<",
        ArithmeticOperation::Rhs => ">>",
        ArithmeticOperation::Neg => "!",
        ArithmeticOperation::Mod => "%",
        ArithmeticOperation::Xor => "^",
        ArithmeticOperation::Mov => "",
        ArithmeticOperation::Ash => "s>>",
        ArithmeticOperation::End => "(swap)",
    };

    write!(f, "{} {}= {}", dst_str, op_str, src_str)
}

fn display_jump(
    instruction: &Instruction,
    jump: JumpInstruction,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    let (dst_str, src_str) =
        get_dst_src_str(instruction, MemoryOpSize::DoubleWord, *jump.get_source());
    let offset = instruction.get_offset();
    let op_str = match jump.get_operation() {
        JumpOperation::Absolute => {
            return write!(f, "PC += {}", offset);
        }
        JumpOperation::IfEqual => "==",
        JumpOperation::IfGreater => ">",
        JumpOperation::IfGreaterOrEqual => ">=",
        JumpOperation::IfAnd => "&",
        JumpOperation::IfNotEqual => "!=",
        JumpOperation::IfSignedGreater => "s>",
        JumpOperation::IfSignedGreaterOrEqual => "s>=",
        JumpOperation::Call => {
            return write!(f, "call #{}", instruction.get_imm());
        }
        JumpOperation::Exit => {
            return write!(f, "exit");
        }
        JumpOperation::IfLessThan => "<",
        JumpOperation::IfLessThanOrEqual => "<=",
        JumpOperation::IfSignedLessThan => "s<",
        JumpOperation::IfSignedLessThanOrEqual => "s<=",
    };

    write!(
        f,
        "if {} {} {}; PC += {} ",
        dst_str, op_str, src_str, offset
    )
}

fn display_memory(
    instruction: &Instruction,
    memory: MemoryInstruction,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    let size = memory.get_size();
    let dst_str = instruction.get_dst_reg().as_str(*size);
    let src_str = instruction.get_src_reg().as_str(*size);
    let offset = instruction.get_offset();
    let imm = instruction.get_imm();
    match memory.get_class() {
        OpcodeClass::Load => write!(f, "{} = {}", dst_str, imm),
        OpcodeClass::LoadReg => write!(f, "{} = *({} + {})", dst_str, src_str, offset),
        OpcodeClass::Store => write!(f, "*({} + {}) = {}", dst_str, offset, imm),
        OpcodeClass::StoreReg => write!(f, "*({} + {}) = {}", dst_str, offset, src_str),
        _ => Ok(()),
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.get_opcode() {
            Opcode::Arithmetic(arithmetic) => display_arithmetic(self, arithmetic, f),
            Opcode::Jump(jump) => display_jump(self, jump, f),
            Opcode::Memory(memory) => display_memory(self, memory, f),
        }
    }
}
