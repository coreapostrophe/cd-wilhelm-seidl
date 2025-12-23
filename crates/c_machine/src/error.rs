#[derive(thiserror::Error, Debug)]
pub enum MachineError {
    #[error("Operand is not a number")]
    NonNumberOperand,
    #[error("Invalid memory layout")]
    InvalidLayout(#[from] std::alloc::LayoutError),
    #[error("Invalid memory address")]
    InvalidMemoryAddress,
    #[error("Out of memory")]
    OutOfMemory,
}
