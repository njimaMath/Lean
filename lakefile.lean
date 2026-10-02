import Lake
open Lake DSL

package NjimaLean where

require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint" @ "v4.32.0"

-- Keep Mathlib last so its compatible transitive revisions take precedence.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.2"

lean_lib DisjointPaths where
  srcDir := "Research"
  roots := #[`Disjoint_paths.Main_Disjoint]

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

lean_lib percolation where
  srcDir := "."
  globs := #[.submodules `percolation]

lean_lib KignmanSubadditiveErgodic where
  srcDir := "Research"
  globs := #[.submodules `KignmanSubadditiveErgodic]

lean_lib oriented_animal where
  srcDir := "Research"
  globs := #[.submodules `oriented_animal]

-- The SYK shared infrastructure and Blueprint chapters.
lean_lib SYK where
  srcDir := "."
  globs := #[
    .submodules `SYK.Probability.GaussianConcentration,
    .one `SYK.Blueprint,
    .submodules `SYK.Chapters]

-- The shared finite-dimensional SYK model.
lean_lib Model where
  srcDir := "."
  globs := #[.submodules `SYK.Model]

-- The SYK log-partition concentration application.
lean_lib SuperConcentration where
  srcDir := "."
  globs := #[.submodules `SYK.SuperConcentration]

-- The SYK central-limit-theorem development.
lean_lib CLT where
  srcDir := "."
  globs := #[.submodules `SYK.CLT]

-- Public generalized Latała formalization.
lean_lib GeneralizedLatala where
  srcDir := "research_public/generalizedLatala"
  globs := #[
    .submodules `SpinGlass,
    .submodules `GeneralizedLatala,
    .one `mainresult_latala
  ]

-- RSAT sources use the root project's shared mathlib in `.lake/packages`.
lean_lib RSAT where
  srcDir := "research_public/RSAT"
  globs := #[.submodules `Lemmas]

-- Give the public endpoint its own module name, separate from the root Main.
@[default_target]
lean_lib RSATMain where
  srcDir := "research_public"
  roots := #[`RSAT.Main]
