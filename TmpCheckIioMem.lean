import Mathlib
open scoped Topology
open Filter
open Set
example : (Set.Iio (1:ℝ)) ∈ (𝓝[<] (1:ℝ)) := by
  -- Should be true by definition of `𝓝[<]`.
  simpa using (self_mem_nhdsWithin : (Set.Iio (1:ℝ)) ∈ nhdsWithin (1:ℝ) (Set.Iio (1:ℝ)))
