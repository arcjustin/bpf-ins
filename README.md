# BPF Instructions

## Description
Parsing library for working with eBPF instructions and programs.

## Example Usage
```rust
/*
 * mov R0, 0
 * exit
 */
let instructions = [ Instruction::mov32(Register::R0, 0), Instruction::exit() ];
```

## TODO
- Replace `anyhow` with own Result/Error definitions.
