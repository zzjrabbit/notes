# Tyle

This project is served for collecting personal mathematical notes.

## Directories
`lean/` holds all lean sources for proofs in `typ/`.
Each file in `typ/` has a coresponding file in `lean/` with the same relative path.
These two directories should have the same structure.
Note that Main.lean is reserved and is not in use.

`models/` holds computational mathematical notes. Each direct child is a Rust crate
whose Typst note, Rust implementation, and example parameter file are colocated.
Typst files under `models/` do not require corresponding Lean files.
The repository root is the Cargo workspace for these crates.

## Checking
This project do not use `lake build` to check the proofs.
You should only check your main work file.
For example, if you need to check Main.lean, you should:
``` shell
lake env lean lean/Main.lean
```

## Editing
1. No backward compability is allowed. Keep the code base fresh.
2. You should tell me my mistakes if they exist.
3. If a theorem exists but it is not contained in mathlib, reserve it as a interface and tell me in the final report.
4. Never edit files which are not related to your work.

