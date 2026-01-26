import Mathlib
example (x : ℝ) (hx : x ≤ (2:ℝ)) (hxn : 0 ≤ x) : x ^ 2 ≤ (4:ℝ) := by
  have h := pow_le_pow_left₀ hxn hx 2
  -- h : x^2 ≤ 2^2
  nlinarith
