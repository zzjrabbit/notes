# Tyle

This project is served for collecting personal mathematical notes.
Your job is to translate the content of the typst file I specified into lean.

## Directories
`lean/` holds all lean sources for proofs in `typ/`.
Each file in `typ/` has a coresponding file in `lean/` with the same relative path.
These two directories should have the same structure.
Note that Main.lean is reserved and is not in use.

## Checking
This project do not use `lake build` to check the proofs.
You should only check your main work file.
For example, if you need to check Main.lean, you should:
``` shell
lake env lean lean/Main.lean
```

## Editing
1. You should never edit typ/
2. You should never edit files in lean/ unless they are related to your work.
3. No backward compability is allowed. Keep the code base fresh.
4. You should tell me my mistakes if they exist.
5. If a theorem exists but it is not contained in mathlib, reserve it as a interface and tell me in the final report.

