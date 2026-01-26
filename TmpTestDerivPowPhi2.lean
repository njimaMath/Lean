import Mathlib

namespace Scratch

noncomputable section

def φ (x : ℝ) : ℝ := Real.exp (-(x^2)/2) / Real.sqrt (2 * Real.pi)

lemma deriv_pow_sub_mul_phi (k : ℕ) (u x : ℝ) :
    deriv (fun x => (x - u) ^ k * φ x) x =
      k * (x - u) ^ (k - 1) * φ x - x * (x - u) ^ k * φ x := by
  unfold φ
  norm_num
  ring

end

end Scratch