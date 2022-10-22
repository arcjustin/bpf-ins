# BPF Instructions

## Description
Parsing library for working with eBPF instructions and programs.

## Example Usage
```rust
let instructions = [ Instruction::mov32(Register::R0, 0), Instruction::exit() ];
let program: Program = instructions.into();
attach_program(program.instructions)
```

## TODO
- Replace `anyhow` with own Result/Error definitions.
