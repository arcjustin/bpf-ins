use crate::Instruction;

pub struct Program {
    pub instructions: Vec<u64>,
}

impl From<&[Instruction]> for Program {
    fn from(instructions: &[Instruction]) -> Self {
        let mut program = vec![];
        for instruction in instructions {
            let n = instruction.encode();
            program.push(n.0);
            if let Some(x) = n.1 {
                program.push(x);
            }
        }

        Self {
            instructions: program,
        }
    }
}

impl<const N: usize> From<[Instruction; N]> for Program {
    fn from(instructions: [Instruction; N]) -> Self {
        instructions.as_ref().into()
    }
}

impl From<Vec<Instruction>> for Program {
    fn from(instructions: Vec<Instruction>) -> Self {
        instructions[0..].as_ref().into()
    }
}

impl From<&Vec<Instruction>> for Program {
    fn from(instructions: &Vec<Instruction>) -> Self {
        instructions[0..].as_ref().into()
    }
}
