import Lake
open Lake DSL

package NjimaLean where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

@[default_target]
lean_lib NjimaLean

-- Perceptron sources live under `Research/perceptronFixed/`.
-- Building this target uses mathlib from the root project's `.lake/packages`.
lean_lib PerceptronFixed where
  srcDir := "Research"
  globs := #[.submodules `perceptronFixed]


lean_lib PerceptronFixed2 where
  srcDir := "research_public/perceptronFixed/Lean"
  globs := #[
    .one `mainresult_perceptron,
    .submodules `conditionalGaussianMoments,
    .submodules `decreasing_g,
    .submodules `derivative_of_B,
    .submodules `Millo,
    .submodules `negative_F_bound,
    .submodules `PerceptronIBP,
    .submodules `PerceptronFixed,
    .submodules `Prop_A_P,
    .submodules `rational_function_bound,
    .submodules `Theorem1,
    .submodules `uniform_bound_of_g]

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

-- Public generalized Latała formalization.
lean_lib GeneralizedLatala where
  srcDir := "research_public/generalizedLatala"
  globs := #[
    .submodules `SpinGlass,
    .submodules `Proof_of_generalized_latala,
    .one `mainresult_latala
  ]

@[default_target]
lean_exe njimaLean where
  root := `Main
