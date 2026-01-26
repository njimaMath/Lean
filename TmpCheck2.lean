import Mathlib
open Real
example : (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ / (Real.sqrt 2 / Real.sqrt Real.pi)
    = Real.sqrt Real.pi / Real.sqrt 2 * ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) := by
  field_simp [div_eq_mul_inv]
  ring
