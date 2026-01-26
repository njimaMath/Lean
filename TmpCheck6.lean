import Mathlib
example : Real.sqrt Real.pi / Real.sqrt 2 * ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) = (2 : ℝ)⁻¹ := by
  field_simp [div_eq_mul_inv]
