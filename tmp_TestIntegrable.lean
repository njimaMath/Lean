import Mathlib
open MeasureTheory

noncomputable section

example : Integrable (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) := by
  -- from integrable_mul_exp_neg_mul_sq
  have h := (integrable_mul_exp_neg_mul_sq (b := (2:ℝ)⁻¹) (by norm_num : (0:ℝ) < (2:ℝ)⁻¹))
  -- h : Integrable fun x => x * exp (-(2⁻¹) * x^2)
  -- try simpa
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

end
