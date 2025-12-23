use std::alloc::Layout;

use crate::{error::MachineError, instruction::Instruction, value::Value};

pub mod error;
pub mod instruction;
pub mod value;

macro_rules! binary_op {
    ($self:expr, $operation:tt) => {{
        let rhs = unsafe { &*$self.stack.add($self.stack_pointer) };
        $self.stack_pointer -= 1;
        let lhs = unsafe { &*$self.stack.add($self.stack_pointer) };

        if let (Value::Int(lhs_val), Value::Int(rhs_val)) = (lhs, rhs) {
            let result = lhs_val $operation rhs_val;
            unsafe {
                *$self.stack.add($self.stack_pointer) = Value::Int(result);
            }
            $self.stack_pointer += 1;
        } else {
            return Err(MachineError::NonNumberOperand);
        }
    }};
}

macro_rules! binary_eq {
    ($self:expr, $operation:tt) => {{
        let rhs = unsafe { &*$self.stack.add($self.stack_pointer) };
        $self.stack_pointer -= 1;
        let lhs = unsafe { &*$self.stack.add($self.stack_pointer) };

        if let (Value::Int(lhs_val), Value::Int(rhs_val)) = (lhs, rhs) {
            let result = if lhs_val $operation rhs_val { 1 } else { 0 };
            unsafe {
                *$self.stack.add($self.stack_pointer) = Value::Int(result);
            }
            $self.stack_pointer += 1;
        } else {
            return Err(MachineError::NonNumberOperand);
        }
    }};
}

pub struct VM {
    stack: *mut Value,
    stack_pointer: usize,
    program_store: *mut Instruction,
    program_counter: usize,
}

impl VM {
    pub const MAX_STACK_SIZE: usize = 1024;
    pub const MAX_PROGRAM_SIZE: usize = 1024;

    pub fn interpret(program: Vec<Instruction>) -> Result<Self, MachineError> {
        let stack_layout = Layout::array::<Value>(Self::MAX_STACK_SIZE)?;
        let stack_ptr = unsafe { std::alloc::alloc(stack_layout) as *mut Value };
        if stack_ptr.is_null() {
            return Err(MachineError::OutOfMemory);
        }

        let program_store_layout = Layout::array::<Instruction>(Self::MAX_PROGRAM_SIZE)?;
        let program_store_ptr =
            unsafe { std::alloc::alloc(program_store_layout) as *mut Instruction };
        if program_store_ptr.is_null() {
            unsafe { std::alloc::dealloc(stack_ptr as *mut u8, stack_layout) };
            return Err(MachineError::OutOfMemory);
        }
        unsafe {
            for (i, instruction) in program.into_iter().enumerate() {
                *program_store_ptr.add(i) = instruction;
            }
        }

        let mut vm = Self {
            stack: stack_ptr,
            stack_pointer: 0,
            program_store: program_store_ptr,
            program_counter: 0,
        };

        vm.run()?;

        Ok(vm)
    }

    pub fn run(&mut self) -> Result<(), MachineError> {
        loop {
            let instruction = unsafe { &*self.program_store.add(self.program_counter) };

            match instruction {
                Instruction::LoadC(value) => {
                    self.stack_pointer += 1;
                    unsafe {
                        *self.stack.add(self.stack_pointer) = value.clone();
                    }
                }
                Instruction::Add => binary_op!(self, +),
                Instruction::Sub => binary_op!(self, -),
                Instruction::Mul => binary_op!(self, *),
                Instruction::Div => binary_op!(self, /),

                Instruction::Eq => binary_eq!(self, ==),
                Instruction::Neq => binary_eq!(self, !=),
                Instruction::Gt => binary_eq!(self, >),
                Instruction::Lt => binary_eq!(self, <),
                Instruction::Leq => binary_eq!(self, <=),
                Instruction::Geq => binary_eq!(self, >=),

                Instruction::Neg => {
                    let val = unsafe { &*self.stack.add(self.stack_pointer) };
                    if let Value::Int(int_val) = val {
                        unsafe {
                            *self.stack.add(self.stack_pointer) = Value::Int(-int_val);
                        }
                    } else {
                        return Err(MachineError::NonNumberOperand);
                    }
                }
                Instruction::Not => {
                    let val = unsafe { &*self.stack.add(self.stack_pointer) };
                    if let Value::Int(int_val) = val {
                        let result = if *int_val == 0 { 1 } else { 0 };
                        unsafe {
                            *self.stack.add(self.stack_pointer) = Value::Int(result);
                        }
                    } else {
                        return Err(MachineError::NonNumberOperand);
                    }
                }

                Instruction::Load => {
                    let addr = unsafe { &*self.stack.add(self.stack_pointer) };
                    if let Value::Address(load_addr) = addr {
                        let value = unsafe { &*self.stack.add(*load_addr) };
                        self.stack_pointer += 1;
                        unsafe {
                            *self.stack.add(self.stack_pointer) = value.clone();
                        }
                    } else {
                        return Err(MachineError::InvalidMemoryAddress);
                    }
                }
                Instruction::Store => {
                    let addr = unsafe { &*self.stack.add(self.stack_pointer) };
                    self.stack_pointer -= 1;
                    let value = unsafe { &*self.stack.add(self.stack_pointer) };
                    if let Value::Address(store_addr) = addr {
                        unsafe {
                            *self.stack.add(*store_addr) = value.clone();
                        }
                    } else {
                        return Err(MachineError::InvalidMemoryAddress);
                    }
                }

                Instruction::Pop => {
                    if self.stack_pointer > 0 {
                        self.stack_pointer -= 1;
                    }
                }
                Instruction::Jump(offset) => {
                    if *offset < 0 {
                        self.program_counter = self
                            .program_counter
                            .checked_sub((-*offset) as usize)
                            .ok_or(MachineError::JumpOverflow)?;
                        continue;
                    } else {
                        self.program_counter = self
                            .program_counter
                            .checked_add(*offset as usize)
                            .ok_or(MachineError::JumpOverflow)?;
                        continue;
                    }
                }
                Instruction::JumpZ(offset) => {
                    let val = unsafe { &*self.stack.add(self.stack_pointer) };
                    if let Value::Int(int_val) = val {
                        if *int_val == 0 {
                            if *offset < 0 {
                                self.program_counter = self
                                    .program_counter
                                    .checked_sub((-*offset) as usize)
                                    .ok_or(MachineError::JumpOverflow)?;
                                continue;
                            } else {
                                self.program_counter = self
                                    .program_counter
                                    .checked_add(*offset as usize)
                                    .ok_or(MachineError::JumpOverflow)?;
                                continue;
                            }
                        }
                    } else {
                        return Err(MachineError::NonNumberOperand);
                    }
                }

                Instruction::Halt => break,
            }

            self.program_counter += 1;
        }

        Ok(())
    }
}

#[cfg(test)]
mod vm_tests {
    use super::*;

    #[test]
    fn load_operation_interprets() {
        let program = vec![
            Instruction::LoadC(Value::Int(42)),
            Instruction::LoadC(Value::Int(7)),
            Instruction::Halt,
        ];

        let vm = VM::interpret(program);

        assert!(vm.is_ok());

        let vm = vm.expect("Failed to interpret program");

        let stack_value_1 = unsafe { &*vm.stack.add(1) };
        let stack_value_2 = unsafe { &*vm.stack.add(2) };

        assert_eq!(stack_value_1, &Value::Int(42));
        assert_eq!(stack_value_2, &Value::Int(7));
    }

    fn binary_helper(op: Instruction, lhs: i64, rhs: i64, expected: i64) {
        let program = vec![
            Instruction::LoadC(Value::Int(lhs)),
            Instruction::LoadC(Value::Int(rhs)),
            op,
            Instruction::Halt,
        ];

        let vm = VM::interpret(program);

        assert!(vm.is_ok());

        let vm = vm.expect("Failed to interpret program");

        let stack_value = unsafe { &*vm.stack.add(1) };

        assert_eq!(stack_value, &Value::Int(expected));
    }

    #[test]
    fn binary_operations_interpret() {
        binary_helper(Instruction::Add, 40, 2, 42);
        binary_helper(Instruction::Sub, 50, 8, 42);
        binary_helper(Instruction::Mul, 6, 7, 42);
        binary_helper(Instruction::Div, 84, 2, 42);

        binary_helper(Instruction::Eq, 42, 42, 1);
        binary_helper(Instruction::Neq, 42, 7, 1);
        binary_helper(Instruction::Gt, 50, 42, 1);
        binary_helper(Instruction::Lt, 7, 42, 1);
        binary_helper(Instruction::Leq, 42, 42, 1);
        binary_helper(Instruction::Geq, 50, 42, 1);
    }

    fn unary_helper(op: Instruction, value: i64, expected: i64) {
        let program = vec![Instruction::LoadC(Value::Int(value)), op, Instruction::Halt];

        let vm = VM::interpret(program);

        assert!(vm.is_ok());

        let vm = vm.expect("Failed to interpret program");

        let stack_value = unsafe { &*vm.stack.add(1) };

        assert_eq!(stack_value, &Value::Int(expected));
    }

    #[test]
    fn unary_operations_interpret() {
        unary_helper(Instruction::Neg, 42, -42);
        unary_helper(Instruction::Not, 0, 1);
        unary_helper(Instruction::Not, 1, 0);
    }

    #[test]
    fn load_instruction_interprets() {
        let program = vec![
            Instruction::LoadC(Value::Int(42)),    // stack[1] = 42
            Instruction::LoadC(Value::Address(1)), // stack[2] = 1 (address)
            Instruction::Load,                     // stack[3] = stack[1] = 42
            Instruction::Halt,
        ];

        let vm = VM::interpret(program);

        assert!(vm.is_ok());

        let vm = vm.expect("Failed to interpret program");

        let stack_value = unsafe { &*vm.stack.add(3) };

        assert_eq!(stack_value, &Value::Int(42));
    }

    #[test]
    fn store_instruction_interprets() {
        let program = vec![
            Instruction::LoadC(Value::Int(42)),    // stack[1] = 42
            Instruction::LoadC(Value::Address(2)), // stack[2] = 2 (address)
            Instruction::Store,                    // stack[2] -> stack[2] = 42
            Instruction::Halt,
        ];

        let vm = VM::interpret(program);

        assert!(vm.is_ok());

        let vm = vm.expect("Failed to interpret program");

        let stack_value = unsafe { &*vm.stack.add(2) };

        assert_eq!(stack_value, &Value::Int(42));
    }

    #[test]
    fn jump_instruction_interprets() {
        let program = vec![
            Instruction::Jump(2),               // jump to instruction 3
            Instruction::LoadC(Value::Int(0)),  // skipped
            Instruction::LoadC(Value::Int(42)), // stack[1] = 42
            Instruction::Halt,
        ];

        let vm = VM::interpret(program);

        assert!(vm.is_ok());

        let vm = vm.expect("Failed to interpret program");

        let stack_value = unsafe { &*vm.stack.add(1) };

        assert_eq!(stack_value, &Value::Int(42));
    }

    #[test]
    fn jumpz_instruction_interprets() {
        let program = vec![
            Instruction::LoadC(Value::Int(0)),  // stack[1] = 0
            Instruction::JumpZ(2),              // jump to instruction 4
            Instruction::LoadC(Value::Int(0)),  // skipped
            Instruction::LoadC(Value::Int(42)), // stack[2] = 42
            Instruction::Halt,
        ];

        let vm = VM::interpret(program);

        assert!(vm.is_ok());

        let vm = vm.expect("Failed to interpret program");

        let stack_value = unsafe { &*vm.stack.add(2) };

        assert_eq!(stack_value, &Value::Int(42));
    }
}
