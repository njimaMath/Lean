import Mathlib
example (x:ℝ) : -(x^2) / 2 = (- (1/2:ℝ)) * x^2 := by
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
