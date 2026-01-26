import Mathlib

open scoped BigOperators

#check Real.sqrt_le_iff
#check Real.sqrt_le_iff

example (q : ℝ) (hq : q ≤ 1) : Real.sqrt q ≤ (1:ℝ) := by
  have : 0 ≤ (1:ℝ) := by norm_num
  -- try
  have h : Real.sqrt q ≤ (1:ℝ) := (Real.sqrt_le_iff).2 ⟨this, by simpa using hq⟩
  exact h
