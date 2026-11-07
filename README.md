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

## Build and run this project
The workspace pins Lean and mathlib to `v4.35.0`. Elan selects the project
toolchain from `lean-toolchain`; changing the machine's default is unnecessary.
The root `lakefile.lean` is the authoritative configuration.
Its local libraries retain the pre-4.33 elaboration behavior with
`backward.isDefEq.respectTransparency.types = false`, as described in the
[Lean migration notes](https://lean-lang.org/doc/reference/latest/releases/v4.33.0/#breaking-changes).
Kernel checking remains enabled. This avoids unnecessary proof rewrites.

Initialize the central dependency from this directory before opening or building
any consumer project. The root also exposes SYK's library and Blueprint targets,
so its independent repository must be present at `SYK_CLT` first. For a fresh
checkout where that directory is absent:

```powershell
git clone https://github.com/TokyoProbabilityGroup/SYK_CLT.git SYK_CLT
```

Then initialize and build:

```powershell
lake update
lake exe cache get
$env:LEAN_NUM_THREADS = "2"
lake build RSATMain
```

There is one physical mathlib checkout, `.lake/packages/mathlib`. Its revision is
pinned by the root configuration and resolved in `lake-manifest.json`. SYK_CLT,
its Blueprint, SpinGlass, LeanTokyo, `Research/chemical_LDP/Lemma3.9`, and
`research_public/perceptronFixed/Lean` use
relative path dependencies to this checkout and the same Lean toolchain.
Keep this workspace layout when cloning the independent repositories.

After initialization, refresh and check each consumer from its own directory:

```powershell
lake update
lake exe cache get
lake env lean --version
lake build
```

Only the root updates mathlib. Stop consumer builds before changing its revision,
then synchronize the retained `lean-toolchain` files and refresh consumer
manifests with Lake. Consumer updates must leave the canonical Git commit equal
to the root manifest's `mathlib.rev`.

The default root build covers RSATMain. For the other developments, build
`DisjointPaths`, `PerceptronFixed2`, `PerceptronGibbs`, `percolation`,
`FPP`, `KignmanSubadditiveErgodic`, `oriented_animal`, `GeneralizedLatala`, `RSAT`, and
`TAPAnnealed` explicitly. The Perceptron commands check its independent Lake
environment, keeping its `SpinGlass.*` modules distinct from GeneralizedLatala's.
The legacy `SYK`, `Model`, `CLT`,
`SuperConcentration`, `Annealed_FE`, and `Universality` commands check the
independent SYK library; `SYK` also checks its Blueprint. Standalone sources
require separate `lake env lean <file>` checks. See `Lean-migration-report.md`
for actual migration validation and remaining failures.

For direct checks of legacy root proofs, pass the package's compatibility option
explicitly: `lake env lean '-Dbackward.isDefEq.respectTransparency.types=false' <file>`.
`lake env` supplies search paths; it does not automatically pass package compiler
options to an arbitrary Lean invocation.
