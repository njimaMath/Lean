import Mathlib
open scoped Topology
open Filter
example : (∀ᶠ q in (𝓝[<] (1:ℝ)), q < 1) := by
  refine Filter.eventually_of_mem (U := Set.Iio (1:ℝ)) (by
    simpa using (self_mem_nhdsWithin : (Set.Iio (1:ℝ)) ∈ nhdsWithin (1:ℝ) (Set.Iio (1:ℝ)))) ?_
  intro q hq
  exact hq
