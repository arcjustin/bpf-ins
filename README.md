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
- Improve the `Program` interface or eliminate it entirely. `Program` is a bit awkward right now; it's basically a container for `&[u64]` that makes converting a list of instructions to a list of bytecodes easier.
- Replace `anyhow` with own Result/Error definitions.
