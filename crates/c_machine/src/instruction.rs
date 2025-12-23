use crate::value::Value;

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
