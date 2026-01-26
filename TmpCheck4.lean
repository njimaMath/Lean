import Mathlib
example (hsqrt_mul : Real.sqrt (2 * Real.pi) * Real.sqrt (2 / Real.pi) = (2 : ℝ)) :
    (1 : ℝ) / (Real.sqrt (2 * Real.pi) * Real.sqrt (2 / Real.pi)) = (1 / 2 : ℝ) := by
  rw [hsqrt_mul]
  norm_num
