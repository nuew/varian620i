use std::{error::Error, fmt::Display};

use crate::instruction::InstructionDecodeError;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum VarianError {
    InstructionDecodeError,
    InvalidAddressError,
}

impl Display for VarianError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        #[allow(deprecated)]
        f.write_str(Self::description(self))
    }
}

impl Error for VarianError {
    fn description(&self) -> &str {
        match self {
            Self::InstructionDecodeError => "instruction decode",
            Self::InvalidAddressError => "invalid address",
        }
    }
}

impl From<InstructionDecodeError> for VarianError {
    fn from(_value: InstructionDecodeError) -> Self {
        VarianError::InstructionDecodeError
    }
}
