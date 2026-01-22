import Mathlib

namespace Tmp

noncomputable section

def sech (x:ℝ) : ℝ := 1 / Real.cosh x

lemma continuous_sech : Continuous sech := by
  -- sech x = (Real.cosh x)⁻¹
  have hcosh : Continuous Real.cosh := by simpa using Real.continuous_cosh
  have h0 : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  --
  simpa [sech, one_div] using (Continuous.inv₀ hcosh h0)

end Tmp
