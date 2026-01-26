import Mathlib
open scoped Topology
example : (𝓝[<] (1:ℝ)) = nhdsWithin (1:ℝ) (Set.Iio 1) := by
  rfl
