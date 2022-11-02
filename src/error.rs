use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    /// Encountered an invalid opcode when decoding
    #[error("unknown opcode {0:#02x}")]
    InvalidOpcode(u8),

    /// Encountered an invalid arithmetic operation when decoding
    #[error("unknown arithmetic operation {0:#02x}")]
    InvalidArithmeticOperation(u8),

    /// Encountered an invalid jump operation when decoding
    #[error("unknown jump operation {0:#02x}")]
    InvalidJumpOperation(u8),

    /// Encountered an invalid memory operation size when decoding
    #[error("unknown memory operation size {0:#02x}")]
    InvalidMemoryOpSize(u8),

    /// Encountered an invalid memory operation mode when decoding
    #[error("unknown memory operation mode {0:#02x}")]
    InvalidMemoryOpMode(u8),

    /// Encountered an invalid register number when decoding
    #[error("unknown register number {0:#02x}")]
    InvalidRegisterNumber(u8),

    /// Not enough instructions to decode
    #[error("not enough instructions to decode")]
    NotEnoughInstructions,
}

pub type Result<T> = std::result::Result<T, Error>;
