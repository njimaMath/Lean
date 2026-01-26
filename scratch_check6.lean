import Mathlib

example (q0 δ : ℝ) (hq : q0 < q0 + δ) : (∀ᶠ q in nhds q0, q < q0 + δ) := by
  have : Set.Iio (q0 + δ) ∈ nhds q0 := Iio_mem_nhds hq
  simpa [Filter.Eventually, Set.mem_Iio] using this

