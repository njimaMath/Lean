# NjimaLean (Lean 4)

## Prerequisites
- Install VS Code and the extension `leanprover.lean4`.
- Install `elan` (Lean toolchain manager).

### Install `elan` on Windows (winget)
```powershell
winget search elan
# Use the Id shown by `winget search` (example):
winget install --id LeanProver.Elan -e
```

### Set Lean 4 as your default toolchain
```powershell
elan default leanprover/lean4:stable
```

## Build and run this project
This repo also pins its toolchain via `lean-toolchain`, so `lake build` will download the right Lean version automatically.

```powershell
lake build
lake exe njimaLean
```
