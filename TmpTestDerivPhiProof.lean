import Mathlib

namespace Scratch

noncomputable section

def φ (x : ℝ) : ℝ := Real.exp (-(x^2)/2) / Real.sqrt (2 * Real.pi)

lemma deriv_φ (x : ℝ) : deriv φ x = -x * φ x := by
  unfold φ
  norm_num
  ring

end

end Scratch