use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("unknown opcode {0:#02x}")]
    InvalidOpcode(u8),

    #[error("unknown arithmetic operation {0:#02x}")]
    InvalidArithmeticOperation(u8),

    #[error("unknown jump operation {0:#02x}")]
    InvalidJumpOperation(u8),

    #[error("unknown memory operation size {0:#02x}")]
    InvalidMemoryOpSize(u8),

    #[error("unknown memory operation mode {0:#02x}")]
    InvalidMemoryOpMode(u8),

    #[error("unknown register number {0:#02x}")]
    InvalidRegisterNumber(u8),

    #[error("not enough instructions to decode")]
    NotEnoughInstructions,
}

pub type Result<T> = std::result::Result<T, Error>;
