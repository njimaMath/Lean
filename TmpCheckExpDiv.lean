import Mathlib

open MeasureTheory

namespace Scratch

#check integrable_rpow_mul_exp_neg_mul_sq
#check integrable_exp_neg_mul_sq
#check integrable_mul_exp_neg_mul_sq

example : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
  have hb : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  -- rewrite
  simpa [div_eq_mul_inv, mul_assoc, pow_two] using (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) hb)

end Scratch
