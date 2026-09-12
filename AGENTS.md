# Tyle

This project collects personal mathematical notes.

## Language
Use English for all repository-maintained prose, including notes, documentation,
source comments, user-facing messages, and configuration or build-script descriptions.
Preserve mathematical notation, proper names, and external identifiers.
Do not translate third-party dependencies or generated artifacts by hand.

## Directories
`lean/` holds all Lean sources for proofs in `typ/`.
Each file in `typ/` has a corresponding file in `lean/` with the same relative path.
These two directories should have the same structure.
Note that Main.lean is reserved and is not in use.

`models/` holds computational mathematical notes. Each direct child is a Rust crate
whose Typst note, Rust implementation, and example parameter file are colocated.
Typst files under `models/` do not require corresponding Lean files.
The repository root is the Cargo workspace for these crates.

## Checking
This project does not use `lake build` to check proofs.
You should only check your main work file.
For example, if you need to check Main.lean, you should:
``` shell
lake env lean lean/Main.lean
```

## Editing
1. Do not preserve backward compatibility. Keep the codebase fresh.
2. Point out any mistakes you find.
3. If a theorem exists but is not available in Mathlib, reserve it as an interface and mention it in the final report.
4. Never edit files unrelated to your work.

