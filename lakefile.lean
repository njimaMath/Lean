import Lake
open Lake DSL

package NjimaLean where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib NjimaLean

-- Auxiliary library so that files under `perceptronFixed/` can `import` each other.
lean_lib PerceptronFixed where
  srcDir := "."
  globs := #[.submodules `perceptronFixed]

@[default_target]
lean_exe njimaLean where
  root := `Main
