use crate::value::Value;

pub enum Instruction {
    LoadC(Value),

    Load,
    Store,

    Pop,

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
