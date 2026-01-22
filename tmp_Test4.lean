import Mathlib

noncomputable section

def sech (x:ℝ) : ℝ := 1 / Real.cosh x

lemma continuous_sech : Continuous sech := by
  have hcosh : Continuous Real.cosh := by simpa using Real.continuous_cosh
  have h0 : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
  --
  -- show sech = fun x => (Real.cosh x)⁻¹
  have : sech = fun x : ℝ => (Real.cosh x)⁻¹ := by
    funext x
    simp [sech, one_div]
  --
  simpa [this] using (Continuous.inv₀ hcosh h0)

end
