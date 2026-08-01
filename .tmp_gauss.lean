import Lemmas.Scalar.Semigroup
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open MeasureTheory ProbabilityTheory Real
open scoped MeasureTheory NNReal

lemma log_cosh_nonneg (x : ℝ) : 0 ≤ Real.log (Real.cosh x) :=
  Real.log_nonneg (Real.one_le_cosh x)

lemma log_cosh_le_sq (x : ℝ) : Real.log (Real.cosh x) ≤ x ^ 2 / 2 := by
  exact (Real.log_le_iff_le_exp (Real.cosh_pos x)).2 (Real.cosh_le_exp_half_sq x)

lemma integrable_log_cosh_add_gaussian (h m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => Real.log (Real.cosh (h + x))) (gaussianReal m v) := by
  have hid : Integrable (fun x : ℝ => |x| ^ 2) (gaussianReal m v) := by
    simpa only [Real.norm_eq_abs, id_eq] using
      (memLp_id_gaussianReal (μ := m) (v := v) (2 : ℝ≥0)).integrable_norm_pow'
  have hg : Integrable (fun x : ℝ => 2 * h ^ 2 + 2 * |x| ^ 2) (gaussianReal m v) := by
    exact (integrable_const (2 * h ^ 2)).add (hid.const_mul 2)
  have hcosh : Continuous (fun x : ℝ => Real.cosh (h + x)) :=
    Real.continuous_cosh.comp (continuous_const.add continuous_id)
  have hc : Continuous (fun x : ℝ => Real.log (Real.cosh (h + x))) :=
    hcosh.log fun x => (Real.cosh_pos (h + x)).ne'
  refine hg.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (log_cosh_nonneg (h + x))]
  calc
    Real.log (Real.cosh (h + x)) ≤ (h + x) ^ 2 / 2 := log_cosh_le_sq _
    _ ≤ 2 * h ^ 2 + 2 * |x| ^ 2 := by nlinarith [sq_nonneg (h - x), sq_abs x]

lemma gaussian_convolution_log_cosh (h a b c : ℝ) (hc : c ^ 2 = a ^ 2 + b ^ 2) :
    (∫ x, ∫ y, Real.log (Real.cosh (h + a * x + b * y)) ∂gaussianReal 0 1
      ∂gaussianReal 0 1) =
      ∫ z, Real.log (Real.cosh (h + c * z)) ∂gaussianReal 0 1 := by
  let va : ℝ≥0 := NNReal.mk (a ^ 2) (sq_nonneg a) * 1
  let vb : ℝ≥0 := NNReal.mk (b ^ 2) (sq_nonneg b) * 1
  let vc : ℝ≥0 := NNReal.mk (c ^ 2) (sq_nonneg c) * 1
  have hma : Measure.map (fun x : ℝ => a * x) (gaussianReal 0 1) =
      gaussianReal 0 va := by
    simpa [va] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) a)
  have hmb : Measure.map (fun x : ℝ => b * x) (gaussianReal 0 1) =
      gaussianReal 0 vb := by
    simpa [vb] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) b)
  have hmc : Measure.map (fun x : ℝ => c * x) (gaussianReal 0 1) =
      gaussianReal 0 vc := by
    simpa [vc] using (gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) c)
  have hv : va + vb = vc := by
    apply NNReal.eq
    simp [va, vb, vc, hc]
  have hf : Integrable (fun z : ℝ => Real.log (Real.cosh (h + z)))
      (gaussianReal 0 va ∗ gaussianReal 0 vb) := by
    rw [gaussianReal_conv_gaussianReal, hv]
    simpa using integrable_log_cosh_add_gaussian h 0 vc
  have hprod : Integrable (fun p : ℝ × ℝ =>
      Real.log (Real.cosh (h + (p.1 + p.2))))
      ((gaussianReal 0 va).prod (gaussianReal 0 vb)) := by
    rw [Measure.conv] at hf
    exact (integrable_map_measure hf.1 (by fun_prop)).mp hf
  have houter : AEStronglyMeasurable
      (fun x : ℝ => ∫ y, Real.log (Real.cosh (h + (x + y))) ∂gaussianReal 0 vb)
      (gaussianReal 0 va) := hprod.integral_prod_left.1
  have hinner (x : ℝ) :
      (∫ y, Real.log (Real.cosh (h + a * x + b * y)) ∂gaussianReal 0 1) =
        ∫ y, Real.log (Real.cosh (h + a * x + y)) ∂gaussianReal 0 vb := by
    have hc' : Continuous (fun y : ℝ => Real.cosh (h + a * x + y)) := by fun_prop
    have hm := (hc'.log fun y => (Real.cosh_pos (h + a * x + y)).ne').aestronglyMeasurable
    rw [← hmb, integral_map (by fun_prop) hm]
    congr with y
    ring
  have houter_map :
      (∫ x, ∫ y, Real.log (Real.cosh (h + a * x + y)) ∂gaussianReal 0 vb
        ∂gaussianReal 0 1) =
        ∫ x, ∫ y, Real.log (Real.cosh (h + x + y)) ∂gaussianReal 0 vb
          ∂gaussianReal 0 va := by
    have hm : AEStronglyMeasurable
        (fun x : ℝ => ∫ y, Real.log (Real.cosh (h + (x + y))) ∂gaussianReal 0 vb)
        (Measure.map (fun x : ℝ => a * x) (gaussianReal 0 1)) := by
      simpa [hma] using houter
    rw [← hma, integral_map (by fun_prop) hm]
  calc
    (∫ x, ∫ y, Real.log (Real.cosh (h + a * x + b * y)) ∂gaussianReal 0 1
        ∂gaussianReal 0 1) =
        ∫ x, ∫ y, Real.log (Real.cosh (h + x + y)) ∂gaussianReal 0 vb
          ∂gaussianReal 0 va := by
            rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
            exact houter_map
    _ = ∫ z, Real.log (Real.cosh (h + z))
          ∂(gaussianReal 0 va ∗ gaussianReal 0 vb) := by
            simpa only [add_assoc] using (integral_conv hf).symm
    _ = ∫ z, Real.log (Real.cosh (h + z)) ∂gaussianReal 0 vc := by
          rw [gaussianReal_conv_gaussianReal, hv, zero_add]
    _ = ∫ z, Real.log (Real.cosh (h + c * z)) ∂gaussianReal 0 1 := by
          rw [← hmc, integral_map (by fun_prop)]
          have hc' : Continuous (fun z : ℝ => Real.cosh (h + z)) := by fun_prop
          exact (hc'.log fun z => (Real.cosh_pos (h + z)).ne').aestronglyMeasurable
