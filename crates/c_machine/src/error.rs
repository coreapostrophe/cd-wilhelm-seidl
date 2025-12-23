#[derive(thiserror::Error, Debug)]
pub enum MachineError {
    #[error("Operand is not a number")]
    NonNumberOperand,
    #[error("Invalid memory layout")]
    InvalidLayout(#[from] std::alloc::LayoutError),
    #[error("Invalid memory address")]
    InvalidMemoryAddress,
    #[error("Jump resulted in overflow")]
    JumpOverflow,
    #[error("Out of memory")]
    OutOfMemory,
}
