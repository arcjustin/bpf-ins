pub mod display;
pub mod instruction;

pub use display::*;
pub use instruction::*;

#[cfg(test)]
mod tests {
    use crate::instruction::{Instruction, MemoryOpLoadType, MemoryOpSize, Register};

    fn decode_encode_compare(instruction: &Instruction) {
        let encoded = instruction.encode();

        let mut raw_instructions = vec![encoded.0];
        if let Some(n) = encoded.1 {
            raw_instructions.push(n);
        }

        let decoded = Instruction::decode(&raw_instructions);
        if let Ok(new_instruction) = decoded {
            let reencoded = new_instruction.encode();
            assert_eq!(encoded, reencoded);
        } else {
            panic!("failed to reencode instruction");
        }
    }

    #[test]
    fn arithmetic_add32() {
        for i in 0..10 {
            let reg = Register::from_num(i).unwrap();

            let ins = Instruction::add32(reg, i32::min_value());
            decode_encode_compare(&ins);

            let ins = Instruction::add32(reg, 0);
            decode_encode_compare(&ins);

            let ins = Instruction::add32(reg, i32::max_value());
            decode_encode_compare(&ins);
        }
    }

    #[test]
    fn arithmetic_add64() {
        for i in 0..10 {
            let reg = Register::from_num(i).unwrap();

            let ins = Instruction::add64(reg, i32::min_value());
            decode_encode_compare(&ins);

            let ins = Instruction::add64(reg, 0);
            decode_encode_compare(&ins);

            let ins = Instruction::add64(reg, i32::max_value());
            decode_encode_compare(&ins);
        }
    }

    #[test]
    fn arithmetic_addx32() {
        for i in 0..10 {
            for j in 0..10 {
                let dst_reg = Register::from_num(i).unwrap();
                let src_reg = Register::from_num(j).unwrap();

                let ins = Instruction::addx32(dst_reg, src_reg);
                decode_encode_compare(&ins);
            }
        }
    }

    #[test]
    fn arithmetic_addx64() {
        for i in 0..10 {
            for j in 0..10 {
                let dst_reg = Register::from_num(i).unwrap();
                let src_reg = Register::from_num(j).unwrap();

                let ins = Instruction::addx64(dst_reg, src_reg);
                decode_encode_compare(&ins);
            }
        }
    }

    #[test]
    fn arithmetic_mov32() {
        for i in 0..10 {
            let reg = Register::from_num(i).unwrap();

            let ins = Instruction::mov32(reg, i32::min_value());
            decode_encode_compare(&ins);

            let ins = Instruction::mov32(reg, 0);
            decode_encode_compare(&ins);

            let ins = Instruction::mov32(reg, i32::max_value());
            decode_encode_compare(&ins);
        }
    }

    #[test]
    fn arithmetic_mov64() {
        for i in 0..10 {
            let reg = Register::from_num(i).unwrap();

            let ins = Instruction::mov64(reg, i32::min_value());
            decode_encode_compare(&ins);

            let ins = Instruction::mov64(reg, 0);
            decode_encode_compare(&ins);

            let ins = Instruction::mov64(reg, i32::max_value());
            decode_encode_compare(&ins);
        }
    }

    #[test]
    fn arithmetic_movx32() {
        for i in 0..10 {
            for j in 0..10 {
                let dst_reg = Register::from_num(i).unwrap();
                let src_reg = Register::from_num(j).unwrap();

                let ins = Instruction::movx32(dst_reg, src_reg);
                decode_encode_compare(&ins);
            }
        }
    }

    #[test]
    fn arithmetic_movx64() {
        for i in 0..10 {
            for j in 0..10 {
                let dst_reg = Register::from_num(i).unwrap();
                let src_reg = Register::from_num(j).unwrap();

                let ins = Instruction::movx64(dst_reg, src_reg);
                decode_encode_compare(&ins);
            }
        }
    }

    #[test]
    fn memory_load() {
        for i in 0..10 {
            let reg = Register::from_num(i).unwrap();

            let ins = Instruction::load(reg, i64::min_value(), MemoryOpSize::Byte);
            decode_encode_compare(&ins);

            let ins = Instruction::load(reg, i64::max_value(), crate::MemoryOpSize::HalfWord);
            decode_encode_compare(&ins);

            let ins = Instruction::load(reg, 0, MemoryOpSize::Word);
            decode_encode_compare(&ins);

            let ins = Instruction::load(reg, 1, MemoryOpSize::DoubleWord);
            decode_encode_compare(&ins);
        }
    }

    #[test]
    fn memory_loadx() {
        for i in 0..10 {
            for j in 0..10 {
                let dst_reg = Register::from_num(i).unwrap();
                let src_reg = Register::from_num(j).unwrap();

                let ins = Instruction::loadx8(dst_reg, src_reg, i16::min_value());
                decode_encode_compare(&ins);

                let ins = Instruction::loadx8(dst_reg, src_reg, 0);
                decode_encode_compare(&ins);

                let ins = Instruction::loadx8(dst_reg, src_reg, i16::max_value());
                decode_encode_compare(&ins);

                let ins = Instruction::loadx16(dst_reg, src_reg, i16::min_value());
                decode_encode_compare(&ins);

                let ins = Instruction::loadx16(dst_reg, src_reg, 0);
                decode_encode_compare(&ins);

                let ins = Instruction::loadx16(dst_reg, src_reg, i16::max_value());
                decode_encode_compare(&ins);

                let ins = Instruction::loadx32(dst_reg, src_reg, i16::min_value());
                decode_encode_compare(&ins);

                let ins = Instruction::loadx32(dst_reg, src_reg, 0);
                decode_encode_compare(&ins);

                let ins = Instruction::loadx32(dst_reg, src_reg, i16::max_value());
                decode_encode_compare(&ins);

                let ins = Instruction::loadx64(dst_reg, src_reg, i16::min_value());
                decode_encode_compare(&ins);

                let ins = Instruction::loadx64(dst_reg, src_reg, 0);
                decode_encode_compare(&ins);

                let ins = Instruction::loadx64(dst_reg, src_reg, i16::max_value());
                decode_encode_compare(&ins);
            }
        }
    }

    #[test]
    fn memory_store() {
        for i in 0..10 {
            let reg = Register::from_num(i).unwrap();

            let ins = Instruction::store8(reg, i16::min_value(), i8::min_value());
            decode_encode_compare(&ins);

            let ins = Instruction::store8(reg, 0, 0);
            decode_encode_compare(&ins);

            let ins = Instruction::store8(reg, i16::max_value(), i8::max_value());
            decode_encode_compare(&ins);

            let ins = Instruction::store16(reg, i16::min_value(), i16::min_value());
            decode_encode_compare(&ins);

            let ins = Instruction::store16(reg, 0, 0);
            decode_encode_compare(&ins);

            let ins = Instruction::store16(reg, i16::max_value(), i16::max_value());
            decode_encode_compare(&ins);

            let ins = Instruction::store32(reg, i16::min_value(), i32::min_value());
            decode_encode_compare(&ins);

            let ins = Instruction::store32(reg, 0, 0);
            decode_encode_compare(&ins);

            let ins = Instruction::store32(reg, i16::max_value(), i32::max_value());
            decode_encode_compare(&ins);

            let ins = Instruction::store64(reg, i16::min_value(), i64::min_value());
            decode_encode_compare(&ins);

            let ins = Instruction::store64(reg, 0, 0);
            decode_encode_compare(&ins);

            let ins = Instruction::store64(reg, i16::max_value(), i64::max_value());
            decode_encode_compare(&ins);
        }
    }

    #[test]
    fn memory_storex() {
        for i in 0..10 {
            for j in 0..10 {
                let dst_reg = Register::from_num(i).unwrap();
                let src_reg = Register::from_num(j).unwrap();

                let ins = Instruction::storex8(dst_reg, i16::min_value(), src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex8(dst_reg, 0, src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex8(dst_reg, i16::max_value(), src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex16(dst_reg, i16::min_value(), src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex16(dst_reg, 0, src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex16(dst_reg, i16::max_value(), src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex32(dst_reg, i16::min_value(), src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex32(dst_reg, 0, src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex32(dst_reg, i16::max_value(), src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex64(dst_reg, i16::min_value(), src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex64(dst_reg, 0, src_reg);
                decode_encode_compare(&ins);

                let ins = Instruction::storex64(dst_reg, i16::max_value(), src_reg);
                decode_encode_compare(&ins);
            }
        }
    }

    #[test]
    fn loadtype() {
        for i in 0..10 {
            let reg = Register::from_num(i).unwrap();

            let ins = Instruction::loadtype(reg, i64::min_value(), MemoryOpLoadType::Void);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, 0, MemoryOpLoadType::Void);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::max_value(), MemoryOpLoadType::Void);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::min_value(), MemoryOpLoadType::Map);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, 0, MemoryOpLoadType::Map);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::max_value(), MemoryOpLoadType::Map);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::min_value(), MemoryOpLoadType::MapValue);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, 0, MemoryOpLoadType::MapValue);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::max_value(), MemoryOpLoadType::MapValue);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::min_value(), MemoryOpLoadType::BtfId);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, 0, MemoryOpLoadType::BtfId);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::max_value(), MemoryOpLoadType::BtfId);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::min_value(), MemoryOpLoadType::Function);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, 0, MemoryOpLoadType::Function);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::max_value(), MemoryOpLoadType::Function);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::min_value(), MemoryOpLoadType::MapIndex);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, 0, MemoryOpLoadType::MapIndex);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::max_value(), MemoryOpLoadType::MapIndex);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::min_value(), MemoryOpLoadType::MapIndexValue);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, 0, MemoryOpLoadType::MapIndexValue);
            decode_encode_compare(&ins);

            let ins = Instruction::loadtype(reg, i64::max_value(), MemoryOpLoadType::MapIndexValue);
            decode_encode_compare(&ins);
        }
    }

    #[test]
    fn call() {
        let ins = Instruction::call(0);
        decode_encode_compare(&ins);

        let ins = Instruction::call(u32::max_value());
        decode_encode_compare(&ins);
    }

    #[test]
    fn exit() {
        let ins = Instruction::exit();
        decode_encode_compare(&ins);
    }
}
