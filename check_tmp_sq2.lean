import Mathlib
#check (by
  have h : (0:ℝ) ≤ 3 := by nlinarith
  have : (0:ℝ) ≤ (3:ℝ) ^ 2 := by
    simpa using (sq_nonneg (3:ℝ))
  exact this)
