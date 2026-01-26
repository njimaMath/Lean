import Mathlib
import perceptronFixed.Prop_A_P.Prop_A_P

open scoped NNReal

namespace Scratch

lemma abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  have h := PropAP.tanh_sq_add_sech_sq x
  have hs : 0 ≤ (PropAP.sech x) ^ 2 := by nlinarith
  have ht : (Real.tanh x) ^ 2 ≤ 1 := by linarith
  have ht' : (Real.tanh x) ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using ht
  simpa using (abs_le_of_sq_le_sq ht' (by norm_num : (0 : ℝ) ≤ 1))

end Scratch
