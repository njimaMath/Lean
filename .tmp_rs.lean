import Lemmas.RSParameters

open MeasureTheory ProbabilityTheory Real BigOperators

set_option autoImplicit false

namespace SpinGlass.AT

example {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    rsR β h ≤ rsQ β h := by
  rw [rsQ_fixedPoint hβ hh]
  unfold rsR standardGaussianExpectation
  have htanh : Continuous (fun x : ℝ => Real.tanh x) := by
    simp_rw [Real.tanh_eq]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity
  apply integral_mono
  · apply Integrable.of_bound (C := 1)
    · exact (htanh.comp (by fun_prop)).pow 4 |>.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (le_of_lt (Real.abs_tanh_lt_one _))
  · apply Integrable.of_bound (C := 1)
    · exact (htanh.comp (by fun_prop)).pow 2 |>.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (le_of_lt (Real.abs_tanh_lt_one _))
  · intro z
    have ht := Real.tanh_sq_lt_one
      (h + β * √(rsQ β h) * z)
    have hn := sq_nonneg
      (Real.tanh (h + β * √(rsQ β h) * z))
    nlinarith [sq_nonneg (Real.tanh (h + β * √(rsQ β h) * z) ^ 2)]

end SpinGlass.AT
