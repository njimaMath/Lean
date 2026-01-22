import Mathlib
open scoped NNReal
#check (by
  have : (1:ℝ≥0) * (1:ℝ≥0) = (1:ℝ≥0) := by simp
  exact this
  )
