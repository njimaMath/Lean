import Lake
open Lake DSL

package NjimaLean where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

@[default_target]
lean_lib NjimaLean

-- Auxiliary library so that files under `perceptronFixed/` can `import` each other.
lean_lib PerceptronFixed where
  srcDir := "."
  globs := #[.submodules `perceptronFixed]

-- Library for percolation theory files
lean_lib percolation where
  srcDir := "."
  globs := #[.submodules `percolation]

-- Library for Kingman Subadditive Ergodic theorem
lean_lib KignmanSubadditiveErgodic where
  srcDir := "."
  globs := #[.submodules `KignmanSubadditiveErgodic]

-- Library for oriented animal files
lean_lib oriented_animal where
  srcDir := "."
  globs := #[.submodules `oriented_animal]

-- The SYK formalization, including the model and concentration theorem.
lean_lib SYK where
  srcDir := "."
  globs := #[.submodules `SYK]


lean_lib GeneralizedLatala where
  srcDir := "GeneralizedLatala"
  globs := #[.submodules `Proof_of_generalized_latala,
    .one `mainesult_generalized_latala]


@[default_target]
lean_exe njimaLean where
  root := `Main
