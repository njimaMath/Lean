import Mathlib
open scoped Topology
#check (𝓝[<] (1:ℝ))
#check (by
  change (𝓝[<] (1:ℝ)) = (nhdsWithin (1:ℝ) (Set.Iio 1))
  rfl)
