import Mathlib

namespace Scratch

lemma sech_sq_le_one (x : ℝ) : (1 / Real.cosh x) ^ 2 ≤ 1 := by
  have hcosh : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have hpos : (0 : ℝ) < Real.cosh x := Real.cosh_pos x
  have hle : (1 / Real.cosh x) ≤ 1 := by
    -- 1 / cosh x ≤ 1 / 1
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hcosh
    simpa using this
  have hnonneg : 0 ≤ (1 / Real.cosh x) := by
    have : 0 < (1 / Real.cosh x) := by
      have : 0 < (Real.cosh x) := hpos
      simpa [one_div] using (inv_pos.2 this)
    exact this.le
  nlinarith

end Scratch
