import Lemmas.RSParameters

open MeasureTheory ProbabilityTheory Real BigOperators

example (x : ℝ) :
    1 - 2 * Real.tanh x ^ 2 + Real.tanh x ^ 4 = (Real.cosh x)⁻¹ ^ 4 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  rw [inv_pow]
  field_simp
  nlinarith [Real.cosh_sq x]

namespace SpinGlass.AT

example {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    rsA β h = standardGaussianExpectation (fun z =>
      (Real.cosh (h + β * Real.sqrt (rsQ β h) * z))⁻¹ ^ 4) := by
  have hq := rsQ_fixedPoint hβ hh
  unfold IsRSFixedPoint at hq
  unfold standardGaussianExpectation at hq
  unfold rsA rsR standardGaussianExpectation
  let X : ℝ → ℝ := fun z => h + β * √(rsQ β h) * z
  have htanh : Continuous (fun x : ℝ => Real.tanh x) := by
    simp_rw [Real.tanh_eq]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity
  have hInt2 : Integrable (fun z => Real.tanh (X z) ^ 2) (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact (htanh.comp (by fun_prop)).pow 2 |>.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (le_of_lt (Real.abs_tanh_lt_one _))
  have hInt4 : Integrable (fun z => Real.tanh (X z) ^ 4) (gaussianReal 0 1) := by
    apply Integrable.of_bound (C := 1)
    · exact (htanh.comp (by fun_prop)).pow 4 |>.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (le_of_lt (Real.abs_tanh_lt_one _))
  change 1 - 2 * rsQ β h + (∫ z, Real.tanh (X z) ^ 4 ∂gaussianReal 0 1) =
    ∫ z, Real.cosh (X z)⁻¹ ^ 4 ∂gaussianReal 0 1
  calc
    _ = 1 - 2 * (∫ z, Real.tanh (X z) ^ 2 ∂gaussianReal 0 1) +
        (∫ z, Real.tanh (X z) ^ 4 ∂gaussianReal 0 1) := by rw [hq]
    _ = ∫ z, (1 - 2 * Real.tanh (X z) ^ 2 + Real.tanh (X z) ^ 4)
        ∂gaussianReal 0 1 := by
      rw [integral_add (integrable_const.sub (hInt2.const_mul 2)) hInt4,
        integral_sub integrable_const (hInt2.const_mul 2), integral_const_mul]
      simp
    _ = _ := integral_congr_ae (ae_of_all _ fun z => by
      rw [Real.tanh_eq_sinh_div_cosh]
      have hc : Real.cosh (X z) ≠ 0 := ne_of_gt (Real.cosh_pos (X z))
      rw [inv_pow]
      field_simp
      nlinarith [Real.cosh_sq (X z)])

end SpinGlass.AT
