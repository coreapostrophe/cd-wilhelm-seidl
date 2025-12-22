use std::alloc::Layout;

#[derive(thiserror::Error, Debug)]
pub enum MachineError {
    #[error("Invalid memory layout")]
    InvalidLayout(#[from] std::alloc::LayoutError),
    #[error("Out of memory")]
    OutOfMemory,
}

#[derive(Debug, PartialEq)]
pub enum Value {
    Int(i64),
}

pub enum Instruction {
    Load(i64),
    Halt,
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
                Instruction::Load(value) => {
                    unsafe {
                        *self.stack.add(self.stack_pointer) = Value::Int(*value);
                    }
                    self.stack_pointer += 1;
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
            Instruction::Load(42),
            Instruction::Load(7),
            Instruction::Halt,
        ];

        let vm = VM::interpret(program);

        assert!(vm.is_ok());

        let vm = vm.expect("Failed to interpret program");

        let stack_value_1 = unsafe { &*vm.stack.add(0) };
        let stack_value_2 = unsafe { &*vm.stack.add(1) };

        assert_eq!(stack_value_1, &Value::Int(42));
        assert_eq!(stack_value_2, &Value::Int(7));
    }
}
