use crate::value::Value;

#[derive(Debug)]
pub enum Instruction {
    LoadC(Value),

    Load,
    Store,

    Pop,
    Jump(isize),
    JumpZ(isize),

    Add,
    Mul,
    Sub,
    Div,

    Eq,
    Neq,
    Gt,
    Lt,
    Leq,
    Geq,

    Neg,
    Not,

    Halt,
}
