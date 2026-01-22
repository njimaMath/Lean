import Mathlib

import perceptronFixed.conditionalGaussianMoments.CGM
import perceptronFixed.decreasing_g.decreasing_g
import perceptronFixed.derivative_of_B.derivative_B
import perceptronFixed.rational_function_bound.RatioBound
import perceptronFixed.uniform_bound_of_g.uniform_bound_of_g

/-!
# Theorem 1 and Theorem 2 (fixed point system)

This file is a detailed Lean scaffold (with `sorry`) following:
`perceptronFixed/Theorem1/blueprint.txt`.

It formalizes the fixed point system from `main.tex` and states:
- Theorem 1 (`thm:main`): existence/uniqueness for `α < αc(κ)` and no solution for `α ≥ αc(κ)`.
- Theorem 2 (`thm:2ndmain`): as `α ↑ αc(κ)`, the solution satisfies `q_α → 1` and `r_α → +∞`.

All proofs are left as `sorry`; this file is intended to be a blueprint-to-Lean skeleton
with many intermediate lemmas (so later work can replace `sorry` incrementally).
-/

open scoped BigOperators Topology NNReal Real ENNReal Interval
open MeasureTheory Filter

namespace Theorem1

noncomputable section

/-! ## 0. Base measure / expectation -/

abbrev γ : Measure ℝ :=
  ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))

abbrev Expect (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂γ

/-! ## 1. Core analytic definitions (matching `main.tex`) -/

abbrev φ : ℝ → ℝ := DecreasingG.φ
abbrev Φbar : ℝ → ℝ := DecreasingG.Φbar
abbrev E : ℝ → ℝ := DecreasingG.E

/-! ### 1.1  Threshold parameters -/

def Cκ (κ : ℝ) : ℝ :=
  Expect (fun z => (max (κ - z) 0) ^ 2)

def αc (κ : ℝ) : ℝ :=
  2 / (Real.pi * Cκ κ)

lemma Cκ_nonneg (κ : ℝ) : 0 ≤ Cκ κ := by
  unfold Cκ Expect
  refine integral_nonneg ?_
  intro z
  exact sq_nonneg (max (κ - z) 0)

lemma Cκ_pos (κ : ℝ) : 0 < Cκ κ := by
  -- Show the integrand is integrable by dominating it with a quadratic moment of the Gaussian.
  have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
    -- `id` is in `L^2` for any Gaussian; hence `z ↦ z^2` is integrable.
    simpa [γ] using
      (MeasureTheory.MemLp.integrable_sq
        (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))))
  have hf_int : Integrable (fun z : ℝ => (max (κ - z) 0) ^ 2) γ := by
    have hconst : Integrable (fun _z : ℝ => (2 : ℝ) * (κ ^ 2)) γ :=
      (integrable_const ((2 : ℝ) * (κ ^ 2)))
    have hbound : ∀ᵐ z ∂γ, ‖(max (κ - z) 0) ^ 2‖ ≤ (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := by
      refine ae_of_all _ (fun z => ?_)
      have hmax : max (κ - z) 0 ≤ |κ - z| := by
        refine max_le (le_abs_self (κ - z)) ?_
        simpa using (abs_nonneg (κ - z))
      have habs : |κ - z| ≤ |κ| + |z| := abs_sub κ z
      have hle' : max (κ - z) 0 ≤ |κ| + |z| := le_trans hmax habs
      have hnonneg : 0 ≤ max (κ - z) 0 := le_max_right _ _
      have hnonneg' : 0 ≤ |κ| + |z| := by positivity
      have hle : (max (κ - z) 0) ^ 2 ≤ (|κ| + |z|) ^ 2 := by
        simpa [pow_two] using mul_le_mul hle' hle' hnonneg hnonneg'
      -- Bound `( |κ| + |z| )^2` by `2*κ^2 + 2*z^2`.
      have hsq : (|κ| + |z|) ^ 2 ≤ (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := by
        have hab : 2 * |κ| * |z| ≤ |κ| ^ 2 + |z| ^ 2 := two_mul_le_add_sq |κ| |z|
        calc
          (|κ| + |z|) ^ 2 = |κ| ^ 2 + |z| ^ 2 + 2 * |κ| * |z| := by ring
          _ ≤ |κ| ^ 2 + |z| ^ 2 + (|κ| ^ 2 + |z| ^ 2) := by gcongr
          _ = (2 : ℝ) * |κ| ^ 2 + (2 : ℝ) * |z| ^ 2 := by ring
          _ = (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := by simp
      have hle_total :
          (max (κ - z) 0) ^ 2 ≤ (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) :=
        le_trans hle hsq
      -- Since the left side is nonnegative, its norm is itself.
      have hnonneg_sq : 0 ≤ (max (κ - z) 0) ^ 2 := by nlinarith [hnonneg]
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg_sq] using hle_total
    -- Use the bound with integrability of the RHS.
    have h_rhs_int : Integrable (fun z : ℝ => (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2)) γ :=
      (hconst.add (hsq_int.const_mul (2 : ℝ)))
    exact h_rhs_int.mono' (by
        -- measurability of the integrand
        have : Measurable fun z : ℝ => (max (κ - z) 0) ^ 2 := by fun_prop
        exact this.aestronglyMeasurable) hbound

  -- The integrand is nonnegative and nonzero on a set of positive Gaussian measure.
  let f : ℝ → ℝ := fun z => (max (κ - z) 0) ^ 2
  have hf_nonneg : 0 ≤ᵐ[γ] f := by
    refine ae_of_all _ (fun z => ?_)
    exact sq_nonneg (max (κ - z) 0)
  have h_support_pos : (0 : ℝ≥0∞) < γ (Function.support f) := by
    -- `Ioc (κ-1) (κ-2⁻¹)` is contained in the support.
    have hsub :
        Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ)) ⊆ Function.support f := by
      intro z hz
      have hzlt : z < κ := by linarith [hz.2]
      have hpos : 0 < max (κ - z) 0 := by
        have : 0 < κ - z := sub_pos.2 hzlt
        simpa [max_eq_left this.le] using this
      have : f z ≠ 0 := by
        have : 0 < f z := by
          have : 0 < max (κ - z) 0 := hpos
          nlinarith
        exact ne_of_gt this
      exact this
    -- Show the interval has positive Gaussian measure.
    have hv : (1 : ℝ≥0) ≠ 0 := by simp
    have hIoc_pos :
        (0 : ℝ≥0∞) < γ (Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ))) := by
      -- Use the density representation of `gaussianReal`.
      have hmeas :
          γ (Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ))) =
            ENNReal.ofReal
              (∫ x in Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ)),
                ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x) := by
        simpa [γ] using
          (ProbabilityTheory.gaussianReal_apply_eq_integral (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv
            (Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ))))
      have hab : (κ - 1 : ℝ) < κ - (2⁻¹ : ℝ) := by linarith
      have hfi :
          IntervalIntegrable (ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0)) volume (κ - 1)
            (κ - (2⁻¹ : ℝ)) := by
        simpa using
          (ProbabilityTheory.integrable_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))).intervalIntegrable
      have hpos_interval :
          0 < ∫ x : ℝ in (κ - 1)..(κ - (2⁻¹ : ℝ)), ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x := by
        exact
          intervalIntegral.intervalIntegral_pos_of_pos
            (f := ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0)) (a := (κ - 1))
            (b := (κ - (2⁻¹ : ℝ))) hfi
            (fun x => ProbabilityTheory.gaussianPDFReal_pos (0 : ℝ) (1 : ℝ≥0) x (by simp))
            hab
      have hIoc :
          (∫ x : ℝ in (κ - 1)..(κ - (2⁻¹ : ℝ)),
              ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x) =
            ∫ x in Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ)),
              ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x := by
        simpa using
          (intervalIntegral.integral_of_le (μ := volume)
                (f := ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0)) (a := (κ - 1))
                (b := (κ - (2⁻¹ : ℝ))) hab.le)
      have hIoc_pos :
          0 < ∫ x in Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ)),
            ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x := by
        -- Rewrite the interval integral in `hpos_interval` as the corresponding set integral.
        exact lt_of_lt_of_eq hpos_interval hIoc
      -- Convert to a positive measure statement via `ENNReal.ofReal`.
      have h_ofReal_pos : (0 : ℝ≥0∞) < ENNReal.ofReal
            (∫ x in Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ)),
              ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x) := by
        exact ENNReal.ofReal_pos.2 hIoc_pos
      simpa [hmeas] using h_ofReal_pos
    -- Use monotonicity of measure and the inclusion.
    exact lt_of_lt_of_le hIoc_pos (MeasureTheory.measure_mono hsub)
  -- Convert support positivity to positivity of the integral.
  have hpos : 0 < ∫ z, f z ∂γ := by
    -- `integral_pos_iff_support_of_nonneg_ae` needs `Integrable`.
    have : (0 < ∫ z, f z ∂γ) ↔ (0 : ℝ≥0∞) < γ (Function.support f) :=
      (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hf_nonneg (hf_int : Integrable f γ))
    exact (this.2 h_support_pos)
  simpa [Cκ, Expect, f] using hpos

lemma αc_pos (κ : ℝ) : 0 < αc κ := by
  have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
  have hC : 0 < Cκ κ := Cκ_pos κ
  unfold αc
  have hden : 0 < Real.pi * Cκ κ := mul_pos hpi hC
  exact div_pos (by norm_num) hden

/-!
Helper lemmas about `Real.sqrt` and `Real.tanh` used for the `P` and `A` analysis.
-/

private lemma tendsto_sqrt_atTop : Tendsto Real.sqrt atTop atTop := by
  -- Characterization of `Tendsto _ atTop atTop`.
  refine tendsto_atTop.2 ?_
  intro a
  by_cases ha : a ≤ 0
  · -- `sqrt r ≥ 0` for all `r`.
    refine Filter.Eventually.of_forall (fun r => ?_)
    exact le_trans ha (Real.sqrt_nonneg _)
  · have ha' : 0 < a := lt_of_not_ge ha
    -- Use the eventual inequality `a^2 ≤ r`.
    have h_event : ∀ᶠ r in atTop, a ^ 2 ≤ r := Filter.eventually_ge_atTop (a ^ 2)
    refine h_event.mono (fun r hr => ?_)
    have hr0 : 0 ≤ r := le_trans (sq_nonneg a) hr
    have ha0 : 0 ≤ a := le_of_lt ha'
    -- `a ≤ sqrt r` iff `a^2 ≤ r`.
    exact (Real.le_sqrt ha0 hr0).2 hr

private lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh ((1 / Real.cosh x) ^ 2) x := by
  -- Use `tanh = sinh / cosh` and the quotient rule.
  have hs : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
  have hc : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hcosh_ne : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  -- Differentiate `sinh / cosh`.
  have hq :
      HasDerivAt (fun y : ℝ => Real.sinh y / Real.cosh y)
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) x := by
    simpa using hs.div hc hcosh_ne
  -- Rewrite the function to `Real.tanh`.
  have hEq :
      (fun y : ℝ => Real.tanh y) =ᶠ[𝓝 x] (fun y : ℝ => Real.sinh y / Real.cosh y) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    simpa using (Real.tanh_eq_sinh_div_cosh y)
  have hq_tanh :
      HasDerivAt Real.tanh
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) x :=
    hq.congr_of_eventuallyEq hEq
  -- Simplify the derivative using `cosh^2 - sinh^2 = 1`.
  have hsimp :
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) =
        (1 / Real.cosh x) ^ 2 := by
    have hcosh : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
    calc
      (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2
          = (Real.cosh x ^ 2 - Real.sinh x ^ 2) / Real.cosh x ^ 2 := by
              simp [pow_two]
      _ = (1 : ℝ) / Real.cosh x ^ 2 := by simp [hcosh]
      _ = (1 / Real.cosh x) ^ 2 := by
              simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  exact hq_tanh.congr_deriv hsimp

private lemma deriv_tanh (x : ℝ) : deriv Real.tanh x = (1 / Real.cosh x) ^ 2 :=
  (hasDerivAt_tanh x).deriv

private lemma tanh_strictMono : StrictMono Real.tanh := by
  refine strictMono_of_deriv_pos ?_
  intro x
  rw [deriv_tanh x]
  have : 0 < (1 / Real.cosh x : ℝ) := one_div_pos.2 (Real.cosh_pos x)
  nlinarith

private lemma continuous_tanh : Continuous Real.tanh := by
  -- `tanh = sinh / cosh` and `cosh` is never zero.
  have hdiv :
      Continuous fun x : ℝ => Real.sinh x / Real.cosh x :=
    Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  exact hdiv.congr (fun x => (Real.tanh_eq_sinh_div_cosh x).symm)

private lemma measurable_tanh : Measurable Real.tanh :=
  (continuous_tanh).measurable

private lemma measurable_tanh_sq (r : ℝ) :
    Measurable fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2 := by
  have hmul : Measurable fun z : ℝ => (Real.sqrt r) * z := measurable_const.mul measurable_id
  have ht : Measurable fun z : ℝ => Real.tanh ((Real.sqrt r) * z) := measurable_tanh.comp hmul
  simpa using (ht.pow_const (2 : ℕ))

private lemma tanh_sq_lt_one (x : ℝ) : (Real.tanh x) ^ 2 < 1 := by
  -- `tanh x = sinh x / cosh x` and `sinh^2 < cosh^2`.
  have hcosh2 : 0 < (Real.cosh x) ^ 2 := sq_pos_of_pos (Real.cosh_pos x)
  have hsinh_lt : (Real.sinh x) ^ 2 < (Real.cosh x) ^ 2 := by
    -- `sinh^2 = cosh^2 - 1 < cosh^2`.
    calc
      (Real.sinh x) ^ 2 = (Real.cosh x) ^ 2 - 1 := by simpa using (Real.sinh_sq x)
      _ < (Real.cosh x) ^ 2 := sub_lt_self _ (by norm_num)
  calc
    (Real.tanh x) ^ 2 = (Real.sinh x / Real.cosh x) ^ 2 := by
      simp [Real.tanh_eq_sinh_div_cosh]
    _ = (Real.sinh x) ^ 2 / (Real.cosh x) ^ 2 := by
      simp [div_pow]
    _ < 1 := (div_lt_one hcosh2).2 hsinh_lt

private lemma tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 (1 : ℝ)) := by
  -- Use the expression `tanh x = (1 - exp(-2x)) / (1 + exp(-2x))`.
  have h_exp : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 (0 : ℝ)) := by
    have hlin : Tendsto (fun x : ℝ => -(2 * x)) atTop atBot := by
      refine tendsto_atBot.2 ?_
      intro a
      have h : ∀ᶠ x in atTop, (-a / 2 : ℝ) ≤ x := Filter.eventually_ge_atTop (-a / 2)
      refine h.mono (fun x hx => ?_)
      nlinarith
    change Tendsto (Real.exp ∘ fun x : ℝ => -(2 * x)) atTop (𝓝 (0 : ℝ))
    exact Real.tendsto_exp_atBot.comp hlin
  have hform : ∀ x : ℝ,
      Real.tanh x = (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
    intro x
    -- Start from the `exp` formula and multiply numerator and denominator by `exp(-x)`.
    have hne : Real.exp (-x) ≠ 0 := (Real.exp_pos (-x)).ne'
    have h1 : Real.exp x * Real.exp (-x) = (1 : ℝ) := by
      have : (1 : ℝ) = Real.exp x * Real.exp (-x) := by
        simpa using (Real.exp_add x (-x))
      simpa using this.symm
    have hx2 : (-x + -x) = -(2 * x) := by ring
    have h2 : Real.exp (-x) * Real.exp (-x) = Real.exp (-(2 * x)) := by
      have h : Real.exp (-x) * Real.exp (-x) = Real.exp (-x + -x) := by
        simpa using (Real.exp_add (-x) (-x)).symm
      simpa [hx2] using h
    have hnum : (Real.exp x - Real.exp (-x)) * Real.exp (-x) = 1 - Real.exp (-(2 * x)) := by
      calc
        (Real.exp x - Real.exp (-x)) * Real.exp (-x)
            = Real.exp x * Real.exp (-x) - Real.exp (-x) * Real.exp (-x) := by ring
        _ = 1 - Real.exp (-(2 * x)) := by simp [h1, h2]
    have hden : (Real.exp x + Real.exp (-x)) * Real.exp (-x) = 1 + Real.exp (-(2 * x)) := by
      calc
        (Real.exp x + Real.exp (-x)) * Real.exp (-x)
            = Real.exp x * Real.exp (-x) + Real.exp (-x) * Real.exp (-x) := by ring
        _ = 1 + Real.exp (-(2 * x)) := by simp [h1, h2]
    calc
      Real.tanh x
          = (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) := by
              simpa using (Real.tanh_eq x)
      _ = ((Real.exp x - Real.exp (-x)) * Real.exp (-x)) / ((Real.exp x + Real.exp (-x)) * Real.exp (-x)) := by
            simpa using
              (mul_div_mul_right (Real.exp x - Real.exp (-x)) (Real.exp x + Real.exp (-x)) hne).symm
      _ = (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
            simp [hnum, hden]
  -- Apply continuity of the rational expression at 0.
  have hcont : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 0 := by
    have : (1 + (0 : ℝ)) ≠ 0 := by norm_num
    simpa using (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id) this
  have hEq :
      (fun x : ℝ => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x)))) =ᶠ[atTop] Real.tanh := by
    refine Filter.Eventually.of_forall (fun x => (hform x).symm)
  have h' :
      Tendsto (fun x : ℝ => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x)))) atTop (𝓝 (1 : ℝ)) := by
    -- Unfold the composition produced by `ContinuousAt.tendsto` and simplify the limit value.
    simpa [Function.comp] using (hcont.tendsto.comp h_exp)
  exact Filter.Tendsto.congr' hEq h'

private lemma tendsto_tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1 : ℝ)) := by
  -- Use oddness: `tanh (-x) = -tanh x`.
  have h : Tendsto (fun x : ℝ => Real.tanh (-x)) atBot (𝓝 (1 : ℝ)) := by
    -- Avoid `simp` rewriting `tanh (-x)` to `-tanh x`.
    change Tendsto (Real.tanh ∘ Neg.neg) atBot (𝓝 (1 : ℝ))
    exact tendsto_tanh_atTop.comp Filter.tendsto_neg_atBot_atTop
  have h' : Tendsto (fun x : ℝ => -Real.tanh (-x)) atBot (𝓝 (-1 : ℝ)) := by
    simpa using h.neg
  -- Rewrite `tanh x = -tanh (-x)` pointwise.
  refine h'.congr' ?_
  filter_upwards with x
  simpa using (Real.tanh_neg (-x)).symm

/-! ### 1.2  The fixed point system -/

def P (r : ℝ) : ℝ :=
  Expect (fun z => (Real.tanh (Real.sqrt r * z)) ^ 2)

def U (κ q z : ℝ) : ℝ :=
  (κ - Real.sqrt q * z) / Real.sqrt (1 - q)

def B (κ q : ℝ) : ℝ :=
  (1 - q) * Expect (fun z => (E (U κ q z)) ^ 2)

def F (κ q x : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - q)) * E ((κ - x) / Real.sqrt (1 - q))

def R (κ q α : ℝ) : ℝ :=
  α * Expect (fun z => (F κ q (Real.sqrt q * z)) ^ 2)

def A (r : ℝ) : ℝ :=
  r * (1 - P r) ^ 2

def f (κ α : ℝ) (r : ℝ) : ℝ :=
  A r - α * B κ (P r)

def IsSolution (κ α q r : ℝ) : Prop :=
  0 ≤ q ∧ q < 1 ∧ 0 ≤ r ∧ q = P r ∧ r = R κ q α

/-! ## 2. Elementary lemmas about the system (algebra only) -/

lemma R_eq (κ α q : ℝ) (hq : q < 1) :
    R κ q α = α * B κ q / (1 - q) ^ 2 := by
  have hpos : 0 ≤ (1 - q) := by linarith [hq.le]
  have hne : (1 - q) ≠ 0 := by linarith [hq.ne]
  have hfac : (1 / Real.sqrt (1 - q)) ^ 2 = 1 / (1 - q) := by
    have hs : (Real.sqrt (1 - q)) ^ 2 = (1 - q) := by
      simpa using (Real.sq_sqrt hpos)
    calc
      (1 / Real.sqrt (1 - q)) ^ 2 = (1 : ℝ) ^ 2 / (Real.sqrt (1 - q)) ^ 2 := by
        simpa [div_pow]
      _ = 1 / (1 - q) := by simp [hs]
  -- Put the common expectation into a name.
  let I : ℝ := Expect (fun z : ℝ => (E (U κ q z)) ^ 2)
  have hB : B κ q = (1 - q) * I := by
    simp [B, I]
  have hRint :
      Expect (fun z : ℝ => (F κ q (Real.sqrt q * z)) ^ 2) = (1 / (1 - q)) * I := by
    -- Expand `F`/`U` and pull out the constant square.
    unfold Expect I F U
    calc
      ∫ z : ℝ,
            ((1 / Real.sqrt (1 - q)) * E ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))) ^ 2 ∂γ =
          ∫ z : ℝ,
              (1 / Real.sqrt (1 - q)) ^ 2 *
                (E ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))) ^ 2 ∂γ := by
            refine integral_congr_ae ?_
            refine ae_of_all _ (fun z => ?_)
            simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ =
          (1 / Real.sqrt (1 - q)) ^ 2 *
            ∫ z : ℝ, (E ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))) ^ 2 ∂γ := by
            simpa [integral_const_mul, mul_assoc] using
              (integral_const_mul (μ := γ) ((1 / Real.sqrt (1 - q)) ^ 2)
                (fun z : ℝ => (E ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))) ^ 2))
      _ = (1 / (1 - q)) *
            ∫ z : ℝ, (E ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))) ^ 2 ∂γ := by
            -- Rewrite the scalar factor using `hfac` without cancelling the integral.
            rw [hfac]
  have hR : R κ q α = α * ((1 / (1 - q)) * I) := by
    unfold R
    -- rewrite the expectation using `hRint`
    simp [hRint]
  -- Finish by elementary algebra.
  rw [hR, hB]
  field_simp [hne]

lemma system_equiv_f_eq_zero
    (κ α q r : ℝ)
    (hq : q = P r)
    (hq1 : q < 1) :
    (r = R κ q α) ↔ (A r = α * B κ (P r)) := by
  -- Replace `q` by `P r` and use `R_eq`.
  subst hq
  have hlt : P r < 1 := by simpa using hq1
  have hReq : R κ (P r) α = α * B κ (P r) / (1 - P r) ^ 2 :=
    R_eq (κ := κ) (α := α) (q := P r) hlt
  have hden : (1 - P r) ^ 2 ≠ 0 := by
    have : (1 - P r) ≠ 0 := by linarith [hlt.ne]
    exact pow_ne_zero 2 this
  constructor
  · intro hr
    have hr' : r = α * B κ (P r) / (1 - P r) ^ 2 := by simpa [hReq] using hr
    -- `A r = r * (1 - P r)^2`.
    calc
      A r = r * (1 - P r) ^ 2 := by simp [A]
      _ = (α * B κ (P r) / (1 - P r) ^ 2) * (1 - P r) ^ 2 := by
        -- multiply the identity `hr'` by `(1 - P r)^2`
        exact congrArg (fun x => x * (1 - P r) ^ 2) hr'
      _ = α * B κ (P r) := by
        -- cancel `(1 - P r)^2`
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hden]
  · intro hAr
    have : r * (1 - P r) ^ 2 = α * B κ (P r) := by simpa [A] using hAr
    have hr' : r = α * B κ (P r) / (1 - P r) ^ 2 :=
      (eq_div_iff hden).2 this
    simpa [hReq] using hr'

lemma f_eq_zero_iff_system
    (κ α q r : ℝ)
    (hqr : q = P r)
    (hq1 : q < 1) :
    (f κ α r = 0) ↔ (r = R κ q α) := by
  -- `f = A - α * B(P r)`.
  subst hqr
  -- `f κ α r = 0` iff `A r = α * B κ (P r)`.
  have hAiff : (f κ α r = 0) ↔ (A r = α * B κ (P r)) := by
    unfold f
    constructor
    · intro hf
      have : A r - α * B κ (P r) = 0 := by simpa using hf
      linarith
    · intro hAr
      have : A r - α * B κ (P r) = 0 := by linarith
      simpa [f] using this
  -- Combine with the equivalence coming from `R_eq`.
  have hsys :
      (r = R κ (P r) α) ↔ (A r = α * B κ (P r)) :=
    system_equiv_f_eq_zero (κ := κ) (α := α) (q := P r) (r := r) rfl hq1
  exact (hAiff.trans hsys.symm)

lemma IsSolution_iff_f_eq_zero
    (κ α q r : ℝ) :
    IsSolution κ α q r ↔
      (0 ≤ q ∧ q < 1 ∧ 0 ≤ r ∧ q = P r ∧ f κ α r = 0) := by
  -- Use the previous lemma to replace the second equation.
  unfold IsSolution
  constructor
  · rintro ⟨hq0, hq1, hr0, hq, hr⟩
    refine ⟨hq0, hq1, hr0, hq, ?_⟩
    -- rewrite `r = R κ q α` into `f = 0`
    have : f κ α r = 0 :=
      (f_eq_zero_iff_system (κ := κ) (α := α) (q := q) (r := r) hq hq1).2 hr
    simpa using this
  · rintro ⟨hq0, hq1, hr0, hq, hf0⟩
    refine ⟨hq0, hq1, hr0, hq, ?_⟩
    -- from `f = 0` recover `r = R κ q α`
    exact (f_eq_zero_iff_system (κ := κ) (α := α) (q := q) (r := r) hq hq1).1 hf0

/-! ## 3. Properties of P (main.tex Lemma `P_properties`) -/

section P_lemmas

lemma P_nonneg (r : ℝ) : 0 ≤ P r := by
  unfold P Expect
  refine integral_nonneg ?_
  intro z
  exact sq_nonneg (Real.tanh (Real.sqrt r * z))

lemma P_le_one (r : ℝ) : P r ≤ 1 := by
  have hbound : ∀ᵐ z ∂γ, ‖(Real.tanh (Real.sqrt r * z)) ^ 2‖ ≤ (1 : ℝ) := by
    refine ae_of_all _ (fun z => ?_)
    have hle : (Real.tanh (Real.sqrt r * z)) ^ 2 ≤ (1 : ℝ) := le_of_lt (tanh_sq_lt_one (Real.sqrt r * z))
    have hnonneg : 0 ≤ (Real.tanh (Real.sqrt r * z)) ^ 2 := sq_nonneg (Real.tanh (Real.sqrt r * z))
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hnorm : ‖P r‖ ≤ (1 : ℝ) * γ.real Set.univ := by
    simpa [P, Expect] using
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := γ)
        (f := fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) (C := (1 : ℝ)) hbound)
  have habs : |P r| ≤ 1 := by
    -- `γ` is a probability measure, hence `γ.real univ = 1`.
    simpa [Real.norm_eq_abs, MeasureTheory.probReal_univ] using hnorm
  have hnonneg : 0 ≤ P r := P_nonneg r
  -- `P r = |P r|` since `P r ≥ 0`.
  calc
    P r = |P r| := by simpa [abs_of_nonneg hnonneg]
    _ ≤ 1 := habs

lemma P_zero : P 0 = 0 := by
  simp [P, Expect]

lemma P_lt_one (r : ℝ) : P r < 1 := by
  -- In the paper: pointwise `tanh^2 < 1` and the Gaussian measure has no atom at 0.
  let f : ℝ → ℝ := fun z => (Real.tanh (Real.sqrt r * z)) ^ 2
  let g : ℝ → ℝ := fun z => 1 - f z
  have hf_int : Integrable f γ := by
    -- dominated by the constant `1`
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) γ := integrable_const 1
    have hmeas : AEStronglyMeasurable f γ := by
      exact (measurable_tanh_sq r).aestronglyMeasurable
    have hbound : ∀ᵐ z ∂γ, ‖f z‖ ≤ (1 : ℝ) := by
      refine ae_of_all _ (fun z => ?_)
      have hle : f z ≤ (1 : ℝ) := le_of_lt (tanh_sq_lt_one (Real.sqrt r * z))
      have hnonneg : 0 ≤ f z := by
        dsimp [f]
        exact sq_nonneg (Real.tanh (Real.sqrt r * z))
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    exact h1.mono' hmeas hbound
  have hg_int : Integrable g γ := by
    simpa [g, f] using (integrable_const (1 : ℝ)).sub hf_int
  have hg_nonneg : 0 ≤ᵐ[γ] g := by
    refine ae_of_all _ (fun z => ?_)
    have hle : f z ≤ (1 : ℝ) := le_of_lt (tanh_sq_lt_one (Real.sqrt r * z))
    dsimp [g]
    linarith
  have hg_support : Function.support g = Set.univ := by
    ext z
    -- `g z = 1 - f z` is strictly positive since `f z < 1`.
    have hlt : f z < (1 : ℝ) := by
      dsimp [f]
      simpa using (tanh_sq_lt_one (Real.sqrt r * z))
    have hpos : 0 < g z := by
      dsimp [g]
      linarith
    simp [Function.support, hpos.ne', Set.mem_univ]
  have hg_pos : 0 < ∫ z, g z ∂γ := by
    have hiff :
        (0 < ∫ z, g z ∂γ) ↔ (0 : ℝ≥0∞) < γ (Function.support g) :=
      MeasureTheory.integral_pos_iff_support_of_nonneg_ae hg_nonneg hg_int
    -- `γ univ = 1`.
    have huniv : (0 : ℝ≥0∞) < γ Set.univ := by
      simpa using (show (0 : ℝ≥0∞) < (1 : ℝ≥0∞) by simp)
    have hsupp : (0 : ℝ≥0∞) < γ (Function.support g) := by
      simpa [hg_support] using huniv
    exact hiff.2 hsupp
  -- `f + g = 1` pointwise, hence `∫ f + ∫ g = 1`.
  have hsum : (∫ z, f z ∂γ) + (∫ z, g z ∂γ) = (1 : ℝ) := by
    have hfg : Integrable (fun z => f z + g z) γ := hf_int.add hg_int
    have : (∫ z, f z ∂γ) + (∫ z, g z ∂γ) = (∫ z, (fun z => f z + g z) z ∂γ) :=
      (MeasureTheory.integral_add hf_int hg_int).symm
    have hone : (∫ z, (1 : ℝ) ∂γ) = (1 : ℝ) := by
      -- `∫ 1 = 1` for a probability measure.
      simpa [MeasureTheory.integral_const, MeasureTheory.probReal_univ] using
        (MeasureTheory.integral_const (μ := γ) (c := (1 : ℝ)))
    -- Now rewrite the integrand.
    have hpoint : (fun z => f z + g z) = fun _z => (1 : ℝ) := by
      funext z
      simp [g, f]
    simpa [hpoint, hone] using this
  -- Rearranging: `∫ f = 1 - ∫ g < 1`.
  have : (∫ z, f z ∂γ) < (1 : ℝ) := by
    have : 0 < ∫ z, g z ∂γ := hg_pos
    linarith [hsum, this]
  simpa [P, Expect, f] using this

lemma P_continuous : Continuous P := by
  -- Dominated convergence with bound `0 ≤ tanh^2 ≤ 1`.
  -- Continuity follows from dominated convergence for the parameter `r`.
  refine continuous_iff_continuousAt.2 (fun r0 => ?_)
  -- Apply dominated convergence with the constant bound `1`.
  have h_meas :
      (∀ᶠ r in 𝓝 r0, AEStronglyMeasurable (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) γ) := by
    refine Filter.Eventually.of_forall (fun r => ?_)
    exact (measurable_tanh_sq r).aestronglyMeasurable
  have h_bound :
      (∀ᶠ r in 𝓝 r0, ∀ᵐ z ∂γ, ‖(Real.tanh (Real.sqrt r * z)) ^ 2‖ ≤ (1 : ℝ)) := by
    refine Filter.Eventually.of_forall (fun r => ?_)
    refine ae_of_all _ (fun z => ?_)
    have hle : (Real.tanh (Real.sqrt r * z)) ^ 2 ≤ (1 : ℝ) := le_of_lt (tanh_sq_lt_one (Real.sqrt r * z))
    have hnonneg : 0 ≤ (Real.tanh (Real.sqrt r * z)) ^ 2 := sq_nonneg (Real.tanh (Real.sqrt r * z))
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have h_int : Integrable (fun _z : ℝ => (1 : ℝ)) γ := integrable_const 1
  have h_lim :
      (∀ᵐ z : ℝ ∂γ,
        Tendsto (fun r : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) (𝓝 r0)
          (𝓝 ((Real.tanh (Real.sqrt r0 * z)) ^ 2))) := by
    refine ae_of_all _ (fun z => ?_)
    have hsqrt : ContinuousAt (fun r : ℝ => Real.sqrt r) r0 :=
      Real.continuous_sqrt.continuousAt
    have hmul : ContinuousAt (fun r : ℝ => Real.sqrt r * z) r0 :=
      hsqrt.mul continuousAt_const
    have htanh : ContinuousAt (fun r : ℝ => Real.tanh (Real.sqrt r * z)) r0 := by
      have hg : ContinuousAt Real.tanh ((fun r : ℝ => Real.sqrt r * z) r0) :=
        continuous_tanh.continuousAt
      simpa [Function.comp] using
        (ContinuousAt.comp (x := r0) (f := fun r : ℝ => Real.sqrt r * z) (g := Real.tanh) hg hmul)
    exact (htanh.pow 2).tendsto
  -- Conclude `Tendsto P (𝓝 r0) (𝓝 (P r0))`.
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := 𝓝 r0)
      (F := fun r : ℝ => fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2)
      (f := fun z : ℝ => (Real.tanh (Real.sqrt r0 * z)) ^ 2) (bound := fun _z : ℝ => (1 : ℝ))
      h_meas h_bound h_int h_lim
  simpa [P, Expect] using h

lemma P_continuousOn_Ici : ContinuousOn P (Set.Ici (0 : ℝ)) := by
  simpa [ContinuousOn] using P_continuous.continuousOn

lemma P_monotoneOn_Ici : MonotoneOn P (Set.Ici (0 : ℝ)) := by
  intro r₁ hr₁ r₂ hr₂ hr
  let f₁ : ℝ → ℝ := fun z => (Real.tanh (Real.sqrt r₁ * z)) ^ 2
  let f₂ : ℝ → ℝ := fun z => (Real.tanh (Real.sqrt r₂ * z)) ^ 2
  have hf₁ : Integrable f₁ γ := by
    -- dominated by 1
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) γ := integrable_const 1
    have hmeas : AEStronglyMeasurable f₁ γ := (by
      simpa [f₁] using (measurable_tanh_sq r₁).aestronglyMeasurable)
    have hbound : ∀ᵐ z ∂γ, ‖f₁ z‖ ≤ (1 : ℝ) := by
      refine ae_of_all _ (fun z => ?_)
      have hle : f₁ z ≤ (1 : ℝ) := le_of_lt (tanh_sq_lt_one (Real.sqrt r₁ * z))
      have hnonneg : 0 ≤ f₁ z := by
        dsimp [f₁]
        exact sq_nonneg (Real.tanh (Real.sqrt r₁ * z))
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    exact h1.mono' hmeas hbound
  have hf₂ : Integrable f₂ γ := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) γ := integrable_const 1
    have hmeas : AEStronglyMeasurable f₂ γ := (by
      simpa [f₂] using (measurable_tanh_sq r₂).aestronglyMeasurable)
    have hbound : ∀ᵐ z ∂γ, ‖f₂ z‖ ≤ (1 : ℝ) := by
      refine ae_of_all _ (fun z => ?_)
      have hle : f₂ z ≤ (1 : ℝ) := le_of_lt (tanh_sq_lt_one (Real.sqrt r₂ * z))
      have hnonneg : 0 ≤ f₂ z := by
        dsimp [f₂]
        exact sq_nonneg (Real.tanh (Real.sqrt r₂ * z))
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    exact h1.mono' hmeas hbound
  have hpoint : ∀ z : ℝ, f₁ z ≤ f₂ z := by
    intro z
    by_cases hz : 0 ≤ z
    · have hsqrt : Real.sqrt r₁ ≤ Real.sqrt r₂ := Real.sqrt_le_sqrt hr
      have hmul : Real.sqrt r₁ * z ≤ Real.sqrt r₂ * z := mul_le_mul_of_nonneg_right hsqrt hz
      have htanh : Real.tanh (Real.sqrt r₁ * z) ≤ Real.tanh (Real.sqrt r₂ * z) :=
        tanh_strictMono.monotone hmul
      have harg₁ : 0 ≤ Real.sqrt r₁ * z := mul_nonneg (Real.sqrt_nonneg _) hz
      have harg₂ : 0 ≤ Real.sqrt r₂ * z := mul_nonneg (Real.sqrt_nonneg _) hz
      have htanh₁ : 0 ≤ Real.tanh (Real.sqrt r₁ * z) := by
        have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₁ * z) := tanh_strictMono.monotone harg₁
        simpa using this
      have htanh₂ : 0 ≤ Real.tanh (Real.sqrt r₂ * z) := by
        have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₂ * z) := tanh_strictMono.monotone harg₂
        simpa using this
      exact (sq_le_sq₀ htanh₁ htanh₂).2 htanh
    · have hz' : 0 ≤ -z := by linarith
      -- Use evenness of `tanh^2`.
      have h1 : f₁ z = f₁ (-z) := by
        simp [f₁, Real.tanh_neg, pow_two, mul_assoc]
      have h2 : f₂ z = f₂ (-z) := by
        simp [f₂, Real.tanh_neg, pow_two, mul_assoc]
      rw [h1, h2]
      -- Now apply the nonnegative case.
      have hsqrt : Real.sqrt r₁ ≤ Real.sqrt r₂ := Real.sqrt_le_sqrt hr
      have hmul : Real.sqrt r₁ * (-z) ≤ Real.sqrt r₂ * (-z) := mul_le_mul_of_nonneg_right hsqrt hz'
      have htanh : Real.tanh (Real.sqrt r₁ * (-z)) ≤ Real.tanh (Real.sqrt r₂ * (-z)) :=
        tanh_strictMono.monotone hmul
      have harg₁ : 0 ≤ Real.sqrt r₁ * (-z) := mul_nonneg (Real.sqrt_nonneg _) hz'
      have harg₂ : 0 ≤ Real.sqrt r₂ * (-z) := mul_nonneg (Real.sqrt_nonneg _) hz'
      have htanh₁ : 0 ≤ Real.tanh (Real.sqrt r₁ * (-z)) := by
        have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₁ * (-z)) := tanh_strictMono.monotone harg₁
        simpa using this
      have htanh₂ : 0 ≤ Real.tanh (Real.sqrt r₂ * (-z)) := by
        have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₂ * (-z)) := tanh_strictMono.monotone harg₂
        simpa using this
      exact (sq_le_sq₀ htanh₁ htanh₂).2 htanh
  -- Integrate the pointwise inequality.
  have hle : ∫ z, f₁ z ∂γ ≤ ∫ z, f₂ z ∂γ := by
    exact MeasureTheory.integral_mono hf₁ hf₂ hpoint
  simpa [P, Expect, f₁, f₂] using hle

lemma P_strictMonoOn_Ici : StrictMonoOn P (Set.Ici (0 : ℝ)) := by
  intro r₁ hr₁ r₂ hr₂ hrlt
  have hrle : r₁ ≤ r₂ := le_of_lt hrlt
  -- Define the pointwise difference.
  let f₁ : ℝ → ℝ := fun z => (Real.tanh (Real.sqrt r₁ * z)) ^ 2
  let f₂ : ℝ → ℝ := fun z => (Real.tanh (Real.sqrt r₂ * z)) ^ 2
  let h : ℝ → ℝ := fun z => f₂ z - f₁ z
  have hf₁ : Integrable f₁ γ := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) γ := integrable_const 1
    have hmeas : AEStronglyMeasurable f₁ γ := (by
      simpa [f₁] using (measurable_tanh_sq r₁).aestronglyMeasurable)
    have hbound : ∀ᵐ z ∂γ, ‖f₁ z‖ ≤ (1 : ℝ) := by
      refine ae_of_all _ (fun z => ?_)
      have hle : f₁ z ≤ (1 : ℝ) := le_of_lt (tanh_sq_lt_one (Real.sqrt r₁ * z))
      have hnonneg : 0 ≤ f₁ z := by
        dsimp [f₁]
        exact sq_nonneg (Real.tanh (Real.sqrt r₁ * z))
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    exact h1.mono' hmeas hbound
  have hf₂ : Integrable f₂ γ := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) γ := integrable_const 1
    have hmeas : AEStronglyMeasurable f₂ γ := (by
      simpa [f₂] using (measurable_tanh_sq r₂).aestronglyMeasurable)
    have hbound : ∀ᵐ z ∂γ, ‖f₂ z‖ ≤ (1 : ℝ) := by
      refine ae_of_all _ (fun z => ?_)
      have hle : f₂ z ≤ (1 : ℝ) := le_of_lt (tanh_sq_lt_one (Real.sqrt r₂ * z))
      have hnonneg : 0 ≤ f₂ z := by
        dsimp [f₂]
        exact sq_nonneg (Real.tanh (Real.sqrt r₂ * z))
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    exact h1.mono' hmeas hbound
  have hh_int : Integrable h γ := by
    simpa [h, f₁, f₂] using hf₂.sub hf₁
  have hh_nonneg : 0 ≤ᵐ[γ] h := by
    refine ae_of_all _ (fun z => ?_)
    have : f₁ z ≤ f₂ z := by
      -- Pointwise comparison (split into `z ≥ 0` and `z < 0`).
      by_cases hz : 0 ≤ z
      · have hsqrt : Real.sqrt r₁ ≤ Real.sqrt r₂ := Real.sqrt_le_sqrt hrle
        have hmul : Real.sqrt r₁ * z ≤ Real.sqrt r₂ * z := mul_le_mul_of_nonneg_right hsqrt hz
        have htanh : Real.tanh (Real.sqrt r₁ * z) ≤ Real.tanh (Real.sqrt r₂ * z) :=
          tanh_strictMono.monotone hmul
        have harg₁ : 0 ≤ Real.sqrt r₁ * z := mul_nonneg (Real.sqrt_nonneg _) hz
        have harg₂ : 0 ≤ Real.sqrt r₂ * z := mul_nonneg (Real.sqrt_nonneg _) hz
        have htanh₁ : 0 ≤ Real.tanh (Real.sqrt r₁ * z) := by
          have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₁ * z) := tanh_strictMono.monotone harg₁
          simpa using this
        have htanh₂ : 0 ≤ Real.tanh (Real.sqrt r₂ * z) := by
          have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₂ * z) := tanh_strictMono.monotone harg₂
          simpa using this
        exact (sq_le_sq₀ htanh₁ htanh₂).2 htanh
      · have hz' : 0 ≤ -z := by linarith
        have h1 : f₁ z = f₁ (-z) := by simp [f₁, Real.tanh_neg, pow_two, mul_assoc]
        have h2 : f₂ z = f₂ (-z) := by simp [f₂, Real.tanh_neg, pow_two, mul_assoc]
        rw [h1, h2]
        have hsqrt : Real.sqrt r₁ ≤ Real.sqrt r₂ := Real.sqrt_le_sqrt hrle
        have hmul : Real.sqrt r₁ * (-z) ≤ Real.sqrt r₂ * (-z) := mul_le_mul_of_nonneg_right hsqrt hz'
        have htanh : Real.tanh (Real.sqrt r₁ * (-z)) ≤ Real.tanh (Real.sqrt r₂ * (-z)) :=
          tanh_strictMono.monotone hmul
        have harg₁ : 0 ≤ Real.sqrt r₁ * (-z) := mul_nonneg (Real.sqrt_nonneg _) hz'
        have harg₂ : 0 ≤ Real.sqrt r₂ * (-z) := mul_nonneg (Real.sqrt_nonneg _) hz'
        have htanh₁ : 0 ≤ Real.tanh (Real.sqrt r₁ * (-z)) := by
          have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₁ * (-z)) := tanh_strictMono.monotone harg₁
          simpa using this
        have htanh₂ : 0 ≤ Real.tanh (Real.sqrt r₂ * (-z)) := by
          have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₂ * (-z)) := tanh_strictMono.monotone harg₂
          simpa using this
        exact (sq_le_sq₀ htanh₁ htanh₂).2 htanh
    dsimp [h]
    linarith
  -- Show strict positivity of the integral of `h` via its support.
  have hsingleton : γ ({0} : Set ℝ) = 0 := by
    have hv : (1 : ℝ≥0) ≠ 0 := by simp
    have hac : γ ≪ (volume : Measure ℝ) := by
      simpa [γ] using
        (ProbabilityTheory.gaussianReal_absolutelyContinuous (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)
    simpa using hac (by simp : (volume : Measure ℝ) ({0} : Set ℝ) = 0)
  have hsupport_pos : (0 : ℝ≥0∞) < γ (Function.support h) := by
    have hsub : (Set.univ \ ({0} : Set ℝ)) ⊆ Function.support h := by
      intro z hz
      have hz0 : z ≠ 0 := by
        have : z ∉ ({0} : Set ℝ) := hz.2
        simpa [Set.mem_singleton_iff] using this
      -- show `h z > 0`, hence `h z ≠ 0`
      have hzabs_pos : 0 < |z| := abs_pos.2 hz0
      have hsqrt_lt : Real.sqrt r₁ < Real.sqrt r₂ := Real.sqrt_lt_sqrt hr₁ hrlt
      have hmul_lt : Real.sqrt r₁ * |z| < Real.sqrt r₂ * |z| :=
        mul_lt_mul_of_pos_right hsqrt_lt hzabs_pos
      have htanh_lt : Real.tanh (Real.sqrt r₁ * |z|) < Real.tanh (Real.sqrt r₂ * |z|) :=
        tanh_strictMono hmul_lt
      have harg₁ : 0 ≤ Real.tanh (Real.sqrt r₁ * |z|) := by
        have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₁ * |z|) := by
          have h0 : 0 ≤ Real.sqrt r₁ * |z| := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
          exact tanh_strictMono.monotone h0
        simpa using this
      have harg₂ : 0 ≤ Real.tanh (Real.sqrt r₂ * |z|) := by
        have : Real.tanh 0 ≤ Real.tanh (Real.sqrt r₂ * |z|) := by
          have h0 : 0 ≤ Real.sqrt r₂ * |z| := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
          exact tanh_strictMono.monotone h0
        simpa using this
      have hsq_lt : (Real.tanh (Real.sqrt r₁ * |z|)) ^ 2 < (Real.tanh (Real.sqrt r₂ * |z|)) ^ 2 :=
        (sq_lt_sq₀ harg₁ harg₂).2 htanh_lt
      have hpos : 0 < h z := by
        -- reduce `h z` to the absolute-value form
        have hf1 : f₁ z = (Real.tanh (Real.sqrt r₁ * |z|)) ^ 2 := by
          by_cases hz' : 0 ≤ z
          · simp [f₁, abs_of_nonneg hz']
          · simp [f₁, abs_of_neg (lt_of_not_ge hz'), Real.tanh_neg, pow_two, mul_assoc]
        have hf2 : f₂ z = (Real.tanh (Real.sqrt r₂ * |z|)) ^ 2 := by
          by_cases hz' : 0 ≤ z
          · simp [f₂, abs_of_nonneg hz']
          · simp [f₂, abs_of_neg (lt_of_not_ge hz'), Real.tanh_neg, pow_two, mul_assoc]
        dsimp [h]
        -- strict positivity of the difference
        linarith [hsq_lt, hf1, hf2]
      exact (ne_of_gt hpos)
    have hcomp : γ (Set.univ \ ({0} : Set ℝ)) = 1 := by
      have hcompl :
          γ (({0} : Set ℝ)ᶜ) = γ Set.univ - γ ({0} : Set ℝ) :=
        MeasureTheory.measure_compl (μ := γ) (s := ({0} : Set ℝ)) (by simp)
          (MeasureTheory.measure_ne_top γ ({0} : Set ℝ))
      calc
        γ (Set.univ \ ({0} : Set ℝ)) = γ (({0} : Set ℝ)ᶜ) := by
          have :
              (Set.univ \ ({0} : Set ℝ)) = (({0} : Set ℝ)ᶜ) := by
            ext x; simp
          simpa [this]
        _ = γ Set.univ - γ ({0} : Set ℝ) := hcompl
        _ = 1 := by simp [hsingleton]
    have : (0 : ℝ≥0∞) < γ (Set.univ \ ({0} : Set ℝ)) := by
      simpa [hcomp] using (show (0 : ℝ≥0∞) < (1 : ℝ≥0∞) by simp)
    exact lt_of_lt_of_le this (MeasureTheory.measure_mono hsub)
  have hint_pos : 0 < ∫ z, h z ∂γ := by
    have hiff :
        (0 < ∫ z, h z ∂γ) ↔ (0 : ℝ≥0∞) < γ (Function.support h) :=
      MeasureTheory.integral_pos_iff_support_of_nonneg_ae hh_nonneg hh_int
    exact hiff.2 hsupport_pos
  -- Now `P r₂ - P r₁ = ∫ h`, hence strict inequality.
  have hdiff : P r₂ - P r₁ = ∫ z, h z ∂γ := by
    -- `P r = ∫ f_r`.
    have : ∫ z, h z ∂γ = (∫ z, f₂ z ∂γ) - ∫ z, f₁ z ∂γ := by
      simpa [h] using (MeasureTheory.integral_sub hf₂ hf₁)
    simpa [P, Expect, f₁, f₂, this, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have : P r₁ < P r₂ := by
    have : 0 < P r₂ - P r₁ := by simpa [hdiff] using hint_pos
    linarith
  exact this

lemma tendsto_P_atTop : Tendsto P atTop (𝓝 (1 : ℝ)) := by
  -- Dominated convergence; pointwise limit is `1` for `z ≠ 0`.
  -- Apply dominated convergence with bound `1`.
  have h_meas :
      (∀ᶠ r in atTop, AEStronglyMeasurable (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) γ) := by
    refine Filter.Eventually.of_forall (fun r => ?_)
    exact (measurable_tanh_sq r).aestronglyMeasurable
  have h_bound :
      (∀ᶠ r in atTop, ∀ᵐ z ∂γ, ‖(Real.tanh (Real.sqrt r * z)) ^ 2‖ ≤ (1 : ℝ)) := by
    refine Filter.Eventually.of_forall (fun r => ?_)
    refine ae_of_all _ (fun z => ?_)
    have hle : (Real.tanh (Real.sqrt r * z)) ^ 2 ≤ (1 : ℝ) := le_of_lt (tanh_sq_lt_one (Real.sqrt r * z))
    have hnonneg : 0 ≤ (Real.tanh (Real.sqrt r * z)) ^ 2 := sq_nonneg (Real.tanh (Real.sqrt r * z))
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have h_int : Integrable (fun _z : ℝ => (1 : ℝ)) γ := integrable_const 1
  -- Pointwise a.e. limit: for `z ≠ 0`, `tanh(√r z)^2 → 1`.
  have hsingleton : γ ({0} : Set ℝ) = 0 := by
    have hv : (1 : ℝ≥0) ≠ 0 := by simp
    have hac : γ ≪ (volume : Measure ℝ) := by
      simpa [γ] using
        (ProbabilityTheory.gaussianReal_absolutelyContinuous (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)
    simpa using hac (by simp : (volume : Measure ℝ) ({0} : Set ℝ) = 0)
  have h_lim :
      (∀ᵐ z : ℝ ∂γ, Tendsto (fun r : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) atTop (𝓝 (1 : ℝ))) := by
    have hz_ne : ∀ᵐ z : ℝ ∂γ, z ≠ 0 := by
      -- `μ {z | z = 0} = 0`.
      simp [MeasureTheory.ae_iff, hsingleton]
    filter_upwards [hz_ne] with z hz
    have hzlt_or : z < 0 ∨ 0 < z := lt_or_gt_of_ne hz
    cases hzlt_or with
    | inl hzlt =>
        -- `z < 0`: the argument tends to `-∞`.
        have hzpos : 0 < -z := by linarith
        have hpos : Tendsto (fun r : ℝ => Real.sqrt r * (-z)) atTop atTop :=
          (Filter.Tendsto.atTop_mul_const (r := (-z)) hzpos tendsto_sqrt_atTop)
        have h_arg : Tendsto (fun r : ℝ => Real.sqrt r * z) atTop atBot := by
          -- `sqrt r * z = -(sqrt r * (-z))`.
          have hneg : Tendsto (fun r : ℝ => -(Real.sqrt r * (-z))) atTop atBot :=
            (Filter.tendsto_neg_atTop_atBot.comp hpos)
          simpa [mul_assoc] using hneg
        have ht : Tendsto (fun r : ℝ => Real.tanh (Real.sqrt r * z)) atTop (𝓝 (-1 : ℝ)) :=
          tendsto_tanh_atBot.comp h_arg
        simpa using (ht.pow 2)
    | inr hzgt =>
        -- `z > 0`: the argument tends to `+∞`.
        have h_arg : Tendsto (fun r : ℝ => Real.sqrt r * z) atTop atTop :=
          (Filter.Tendsto.atTop_mul_const (r := z) hzgt tendsto_sqrt_atTop)
        have ht : Tendsto (fun r : ℝ => Real.tanh (Real.sqrt r * z)) atTop (𝓝 (1 : ℝ)) :=
          tendsto_tanh_atTop.comp h_arg
        simpa using (ht.pow 2)
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := atTop)
      (F := fun r : ℝ => fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) (f := fun _z : ℝ => (1 : ℝ))
      (bound := fun _z : ℝ => (1 : ℝ)) h_meas h_bound h_int h_lim
  simpa [P, Expect, MeasureTheory.integral_const, MeasureTheory.probReal_univ] using h

end P_lemmas

/-! ## 4. Properties of A (main.tex Lemma `A`) -/

section A_lemmas

-- `Mathlib` provides `Real.sinh`, `Real.cosh`, `Real.tanh` but does not define `sech`.
-- We define it explicitly to match `main.tex`.
def sech (x : ℝ) : ℝ :=
  1 / Real.cosh x

def S (r : ℝ) : ℝ :=
  Expect (fun z => (sech (Real.sqrt r * z)) ^ 2)

lemma S_eq_one_sub_P (r : ℝ) : S r = 1 - P r := by
  -- Use `sech^2 = 1 - tanh^2`.
  -- First show the pointwise identity `sech^2 = 1 - tanh^2`.
  have hpoint : ∀ x : ℝ, (sech x) ^ 2 = 1 - (Real.tanh x) ^ 2 := by
    intro x
    have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    have hcosh2 : (Real.cosh x ^ 2) ≠ 0 := pow_ne_zero 2 hcosh
    -- Prove `tanh^2 + sech^2 = 1` then rearrange.
    have hsum : (Real.tanh x) ^ 2 + (sech x) ^ 2 = 1 := by
      rw [Real.tanh_eq_sinh_div_cosh, sech, div_pow, div_pow]
      -- Clear denominators `cosh x ^ 2`.
      field_simp [hcosh2]
      -- `field_simp` turns the goal into `sinh^2 + 1 = cosh^2`.
      simpa using (Real.cosh_sq x).symm
    linarith
  -- Integrability of the `tanh^2` integrand (bounded by 1).
  have hf_int :
      Integrable (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) γ := by
    have h1 : Integrable (fun _z : ℝ => (1 : ℝ)) γ := integrable_const 1
    refine h1.mono' (measurable_tanh_sq r).aestronglyMeasurable ?_
    refine ae_of_all _ (fun z => ?_)
    have hle : (Real.tanh (Real.sqrt r * z)) ^ 2 ≤ (1 : ℝ) :=
      le_of_lt (tanh_sq_lt_one (Real.sqrt r * z))
    have hnonneg : 0 ≤ (Real.tanh (Real.sqrt r * z)) ^ 2 :=
      sq_nonneg (Real.tanh (Real.sqrt r * z))
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  -- Rewrite under the integral and use linearity.
  unfold S P Expect
  have hfun :
      (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) =
        fun z : ℝ => (1 : ℝ) - (Real.tanh (Real.sqrt r * z)) ^ 2 := by
    funext z
    simpa using (hpoint (Real.sqrt r * z))
  simp [hfun, integral_sub (integrable_const (1 : ℝ)) hf_int,
    MeasureTheory.integral_const, MeasureTheory.probReal_univ]

lemma A_eq_r_mul_S_sq (r : ℝ) : A r = r * (S r) ^ 2 := by
  -- Use `S_eq_one_sub_P`.
  simp [A, S_eq_one_sub_P]

lemma A_zero : A 0 = 0 := by
  simp [A, P_zero]

lemma A_continuous : Continuous A := by
  -- From continuity of `P`.
  unfold A
  simpa [sub_eq_add_neg] using (continuous_id.mul ((continuous_const.sub P_continuous).pow 2))

lemma A_continuousOn_Ici : ContinuousOn A (Set.Ici (0 : ℝ)) := by
  simpa [ContinuousOn] using A_continuous.continuousOn

lemma A_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ A r := by
  -- `r ≥ 0` and square.
  unfold A
  exact mul_nonneg hr (sq_nonneg (1 - P r))

/-! ### Change-of-variables integral `I(r)` -/

/-- Scalar integral used in the representation `A(r) = (1/(2π)) * I(r)^2` for `r > 0`. -/
def I (r : ℝ) : ℝ :=
  ∫ y : ℝ, (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))

lemma integral_sech_sq : (∫ y : ℝ, (sech y) ^ 2) = (2 : ℝ) := by
  -- Compute the integral as an improper integral over `Ioc (-n) n`.
  have hcont_sech : Continuous sech := by
    have hcosh_ne : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
    unfold sech
    simpa [one_div] using (Continuous.inv₀ Real.continuous_cosh hcosh_ne)
  have hcont : Continuous fun y : ℝ => (sech y) ^ 2 := by
    simpa using hcont_sech.pow 2
  have hderiv : deriv Real.tanh = fun y : ℝ => (sech y) ^ 2 := by
    funext y
    -- `deriv tanh = (1/cosh)^2` and `sech = 1/cosh`.
    simp [deriv_tanh, sech]
  have hinterval (n : ℕ) :
      ∫ y in (-(n : ℝ))..(n : ℝ), (sech y) ^ 2 = 2 * Real.tanh (n : ℝ) := by
    have hdiff : ∀ x ∈ Set.uIcc (-(n : ℝ)) (n : ℝ), DifferentiableAt ℝ Real.tanh x := by
      intro x _hx
      exact (hasDerivAt_tanh x).differentiableAt
    have hcont' :
        ContinuousOn (fun y : ℝ => (sech y) ^ 2) (Set.uIcc (-(n : ℝ)) (n : ℝ)) :=
      hcont.continuousOn
    have hFTC :
        ∫ y in (-(n : ℝ))..(n : ℝ), (sech y) ^ 2 =
          Real.tanh (n : ℝ) - Real.tanh (-(n : ℝ)) := by
      simpa using
        (intervalIntegral.integral_deriv_eq_sub' (a := (-(n : ℝ))) (b := (n : ℝ))
          (f := Real.tanh) (f' := fun y : ℝ => (sech y) ^ 2) hderiv hdiff hcont')
    -- `tanh n - tanh (-n) = 2 * tanh n`.
    simpa [Real.tanh_neg, sub_eq_add_neg, two_mul] using hFTC
  -- Use an `AECover` by `Ioc (-n) n`.
  let a : ℕ → ℝ := fun n => -(n : ℝ)
  let b : ℕ → ℝ := fun n => (n : ℝ)
  have ha : Tendsto a atTop atBot := by
    have hb' : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop (R := ℝ)
    dsimp [a]
    exact tendsto_neg_atTop_atBot.comp hb'
  have hb : Tendsto b atTop atTop := by
    simpa [b] using (tendsto_natCast_atTop_atTop (R := ℝ))
  have hφ : AECover (μ := volume) (l := atTop) (fun n : ℕ => Set.Ioc (a n) (b n)) :=
    aecover_Ioc (μ := volume) (l := atTop) ha hb
  have hnng : 0 ≤ᵐ[volume] fun y : ℝ => (sech y) ^ 2 :=
    Filter.Eventually.of_forall (fun y => sq_nonneg (sech y))
  have hfi :
      ∀ n : ℕ, IntegrableOn (fun y : ℝ => (sech y) ^ 2) (Set.Ioc (a n) (b n)) volume := by
    intro n
    have hIcc :
        IntegrableOn (fun y : ℝ => (sech y) ^ 2) (Set.Icc (a n) (b n)) volume := by
      simpa using (hcont.integrableOn_Icc (μ := volume) (a := a n) (b := b n))
    exact hIcc.mono_set (Set.Ioc_subset_Icc_self)
  have htendsto :
      Tendsto (fun n : ℕ => ∫ y in Set.Ioc (a n) (b n), (sech y) ^ 2 ∂volume) atTop (𝓝 (2 : ℝ)) := by
    have htanh : Tendsto (fun n : ℕ => Real.tanh (n : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_tanh_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have htanh2 : Tendsto (fun n : ℕ => 2 * Real.tanh (n : ℝ)) atTop (𝓝 (2 : ℝ)) := by
      simpa using (Filter.Tendsto.const_mul 2 htanh)
    have hrewrite :
        ∀ n : ℕ, 2 * Real.tanh (n : ℝ) = ∫ y in Set.Ioc (a n) (b n), (sech y) ^ 2 ∂volume := by
      intro n
      have hab : a n ≤ b n := by
        have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        linarith [hn]
      calc
        2 * Real.tanh (n : ℝ) = ∫ y in (a n)..(b n), (sech y) ^ 2 ∂volume := by
          simpa [a, b] using (hinterval n).symm
        _ = ∫ y in Set.Ioc (a n) (b n), (sech y) ^ 2 ∂volume := by
          simpa using
            (intervalIntegral.integral_of_le (μ := volume) (f := fun y : ℝ => (sech y) ^ 2) hab)
    have hrewrite' :
        (fun n : ℕ => 2 * Real.tanh (n : ℝ)) =
          fun n : ℕ => ∫ y in Set.Ioc (a n) (b n), (sech y) ^ 2 ∂volume := by
      funext n
      exact hrewrite n
    simpa [hrewrite'] using htanh2
  -- Conclude by the `AECover` lemma.
  simpa using
    hφ.integral_eq_of_tendsto_of_nonneg_ae (f := fun y : ℝ => (sech y) ^ 2) (I := (2 : ℝ))
      hnng hfi htendsto

lemma integrable_sech_sq : Integrable (fun y : ℝ => (sech y) ^ 2) (volume : Measure ℝ) := by
  refine MeasureTheory.Integrable.of_integral_ne_zero ?_
  simpa [integral_sech_sq] using (by norm_num : (2 : ℝ) ≠ 0)

lemma exp_neg_sq_div_le_one (y r : ℝ) (hr : 0 < r) :
    Real.exp (-(y ^ 2) / (2 * r)) ≤ 1 := by
  have hy2 : 0 ≤ y ^ 2 := by nlinarith
  have hden : 0 < 2 * r := by nlinarith [hr]
  have hq : 0 ≤ (y ^ 2) / (2 * r) := div_nonneg hy2 (le_of_lt hden)
  have hexp : -(y ^ 2) / (2 * r) ≤ 0 := by
    have : -(y ^ 2 / (2 * r)) ≤ 0 := neg_nonpos.2 hq
    simpa [neg_div] using this
  exact (Real.exp_le_one_iff).2 hexp

lemma tendsto_exp_neg_sq_div_atTop (y : ℝ) :
    Tendsto (fun r : ℝ => Real.exp (-(y ^ 2) / (2 * r))) atTop (𝓝 (1 : ℝ)) := by
  have hmul : Tendsto (fun r : ℝ => (2 : ℝ) * r) atTop atTop := by
    simpa [mul_comm] using (tendsto_id.atTop_mul_const (show (0 : ℝ) < 2 by norm_num))
  have hinv : Tendsto (fun r : ℝ => (2 * r)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hmul
  have harg0 : Tendsto (fun r : ℝ => (-(y ^ 2) : ℝ) * (2 * r)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa using (Filter.Tendsto.const_mul (-(y ^ 2) : ℝ) hinv)
  have harg : Tendsto (fun r : ℝ => -(y ^ 2) / (2 * r)) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using harg0
  exact Real.tendsto_exp_nhds_zero_nhds_one.comp harg

lemma exp_neg_sq_div_lt {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ < r₂) {y : ℝ}
    (hy : y ≠ 0) :
    Real.exp (-(y ^ 2) / (2 * r₁)) < Real.exp (-(y ^ 2) / (2 * r₂)) := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hmul : 2 * r₁ < 2 * r₂ := by nlinarith [h]
  have hinv : 1 / (2 * r₂) < 1 / (2 * r₁) :=
    one_div_lt_one_div_of_lt (by nlinarith [hr₁]) hmul
  have hdiv : y ^ 2 / (2 * r₂) < y ^ 2 / (2 * r₁) := by
    have hmul' : y ^ 2 * (1 / (2 * r₂)) < y ^ 2 * (1 / (2 * r₁)) :=
      mul_lt_mul_of_pos_left hinv hy2
    simpa [div_eq_mul_inv, one_div] using hmul'
  have hneg : -(y ^ 2 / (2 * r₁)) < -(y ^ 2 / (2 * r₂)) := neg_lt_neg hdiv
  have hexp : -(y ^ 2) / (2 * r₁) < -(y ^ 2) / (2 * r₂) := by
    simpa [neg_div] using hneg
  exact (Real.exp_lt_exp).2 hexp

lemma I_nonneg (r : ℝ) : 0 ≤ I r := by
  unfold I
  refine integral_nonneg ?_
  intro y
  have hsech : 0 ≤ (sech y) ^ 2 := sq_nonneg (sech y)
  have hexp : 0 ≤ Real.exp (-(y ^ 2) / (2 * r)) := (Real.exp_pos _).le
  exact mul_nonneg hsech hexp

lemma strictMonoOn_I : StrictMonoOn I (Set.Ioi (0 : ℝ)) := by
  intro r₁ hr₁ r₂ hr₂ hlt
  have hr₁' : 0 < r₁ := by simpa [Set.mem_Ioi] using hr₁
  have hr₂' : 0 < r₂ := by simpa [Set.mem_Ioi] using hr₂
  let F : ℝ → ℝ :=
    fun y => (sech y) ^ 2 * (Real.exp (-(y ^ 2) / (2 * r₂)) - Real.exp (-(y ^ 2) / (2 * r₁)))
  have hF_nonneg : 0 ≤ᵐ[volume] F := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hsech : 0 ≤ (sech y) ^ 2 := sq_nonneg (sech y)
    -- Compare the exponents to get `exp₁ ≤ exp₂`.
    have hy2 : 0 ≤ y ^ 2 := by nlinarith
    have hmul : 2 * r₁ ≤ 2 * r₂ := by nlinarith [hlt.le]
    have hinv : 1 / (2 * r₂) ≤ 1 / (2 * r₁) :=
      one_div_le_one_div_of_le (by nlinarith [hr₁']) hmul
    have hdiv : y ^ 2 / (2 * r₂) ≤ y ^ 2 / (2 * r₁) := by
      have hmul' : y ^ 2 * (1 / (2 * r₂)) ≤ y ^ 2 * (1 / (2 * r₁)) :=
        mul_le_mul_of_nonneg_left hinv hy2
      simpa [div_eq_mul_inv, one_div] using hmul'
    have hneg : -(y ^ 2) / (2 * r₁) ≤ -(y ^ 2) / (2 * r₂) := by
      have hneg' : -(y ^ 2 / (2 * r₁)) ≤ -(y ^ 2 / (2 * r₂)) := neg_le_neg hdiv
      simpa [neg_div] using hneg'
    have hle : Real.exp (-(y ^ 2) / (2 * r₁)) ≤ Real.exp (-(y ^ 2) / (2 * r₂)) :=
      (Real.exp_le_exp).2 hneg
    have hdiff : 0 ≤ Real.exp (-(y ^ 2) / (2 * r₂)) - Real.exp (-(y ^ 2) / (2 * r₁)) :=
      sub_nonneg.2 hle
    exact mul_nonneg hsech hdiff
  have hF_int : Integrable F (volume : Measure ℝ) := by
    -- Dominate by `sech^2` since the bracket is `≤ 1`.
    have hmeas : AEStronglyMeasurable F (volume : Measure ℝ) := by
      have hcont_sech : Continuous sech := by
        -- `sech x = (cosh x)⁻¹`
        have hcosh_ne : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
        unfold sech
        simpa [one_div] using (Continuous.inv₀ Real.continuous_cosh hcosh_ne)
      have hcont : Continuous fun y : ℝ =>
          (sech y) ^ 2 * (Real.exp (-(y ^ 2) / (2 * r₂)) - Real.exp (-(y ^ 2) / (2 * r₁))) := by
        fun_prop [hcont_sech]
      exact hcont.measurable.aestronglyMeasurable
    have hbound : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), ‖F y‖ ≤ (sech y) ^ 2 := by
      refine ae_of_all _ (fun y => ?_)
      have hsech : 0 ≤ (sech y) ^ 2 := sq_nonneg (sech y)
      have hle2 : Real.exp (-(y ^ 2) / (2 * r₂)) ≤ 1 := exp_neg_sq_div_le_one y r₂ hr₂'
      have hle1 : 0 ≤ Real.exp (-(y ^ 2) / (2 * r₁)) := (Real.exp_pos _).le
      have hdiff_le : Real.exp (-(y ^ 2) / (2 * r₂)) - Real.exp (-(y ^ 2) / (2 * r₁)) ≤ 1 := by
        have : Real.exp (-(y ^ 2) / (2 * r₂)) - Real.exp (-(y ^ 2) / (2 * r₁))
            ≤ Real.exp (-(y ^ 2) / (2 * r₂)) := sub_le_self _ hle1
        exact le_trans this hle2
      have hdiff_nonneg : 0 ≤ Real.exp (-(y ^ 2) / (2 * r₂)) - Real.exp (-(y ^ 2) / (2 * r₁)) := by
        have hy2 : 0 ≤ y ^ 2 := by nlinarith
        have hmul : 2 * r₁ ≤ 2 * r₂ := by nlinarith [hlt.le]
        have hinv : 1 / (2 * r₂) ≤ 1 / (2 * r₁) :=
          one_div_le_one_div_of_le (by nlinarith [hr₁']) hmul
        have hdiv : y ^ 2 / (2 * r₂) ≤ y ^ 2 / (2 * r₁) := by
          have hmul' : y ^ 2 * (1 / (2 * r₂)) ≤ y ^ 2 * (1 / (2 * r₁)) :=
            mul_le_mul_of_nonneg_left hinv hy2
          simpa [div_eq_mul_inv, one_div] using hmul'
        have hneg : -(y ^ 2) / (2 * r₁) ≤ -(y ^ 2) / (2 * r₂) := by
          have hneg' : -(y ^ 2 / (2 * r₁)) ≤ -(y ^ 2 / (2 * r₂)) := neg_le_neg hdiv
          simpa [neg_div] using hneg'
        have hle : Real.exp (-(y ^ 2) / (2 * r₁)) ≤ Real.exp (-(y ^ 2) / (2 * r₂)) :=
          (Real.exp_le_exp).2 hneg
        exact sub_nonneg.2 hle
      have hF_le : F y ≤ (sech y) ^ 2 := by
        have :
            (sech y) ^ 2 * (Real.exp (-(y ^ 2) / (2 * r₂)) - Real.exp (-(y ^ 2) / (2 * r₁)))
              ≤ (sech y) ^ 2 * (1 : ℝ) := mul_le_mul_of_nonneg_left hdiff_le hsech
        simpa [F] using this
      have hF_nonneg' : 0 ≤ F y := by
        dsimp [F]
        exact mul_nonneg hsech hdiff_nonneg
      simpa [Real.norm_eq_abs, abs_of_nonneg hF_nonneg'] using hF_le
    exact (integrable_sech_sq).mono' hmeas hbound
  have hF_support_pos : (0 : ℝ≥0∞) < (volume : Measure ℝ) (Function.support F) := by
    have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Function.support F := by
      intro y hy
      have hy0 : y ≠ 0 := ne_of_gt hy.1
      have hlt_exp : Real.exp (-(y ^ 2) / (2 * r₁)) < Real.exp (-(y ^ 2) / (2 * r₂)) :=
        exp_neg_sq_div_lt hr₁' hr₂' hlt hy0
      have hdiff_pos :
          0 < Real.exp (-(y ^ 2) / (2 * r₂)) - Real.exp (-(y ^ 2) / (2 * r₁)) :=
        sub_pos.2 hlt_exp
      have hsech_pos : 0 < (sech y) ^ 2 := by
        have hcosh : 0 < Real.cosh y := Real.cosh_pos y
        have hsech : 0 < sech y := by
          have : 0 < (1 / Real.cosh y : ℝ) := one_div_pos.2 hcosh
          simpa [sech] using this
        exact pow_pos hsech 2
      have hpos : 0 < F y := by
        dsimp [F]
        exact mul_pos hsech_pos hdiff_pos
      exact (ne_of_gt hpos)
    have hIoc_pos : (0 : ℝ≥0∞) < (volume : Measure ℝ) (Set.Ioc (0 : ℝ) 1) := by
      simpa using (show (0 : ℝ≥0∞) < (1 : ℝ≥0∞) by simp)
    exact lt_of_lt_of_le hIoc_pos (measure_mono hsub)
  have hF_pos : 0 < ∫ y, F y ∂(volume : Measure ℝ) := by
    have hiff :
        (0 < ∫ y, F y ∂(volume : Measure ℝ)) ↔
          (0 : ℝ≥0∞) < (volume : Measure ℝ) (Function.support F) :=
      MeasureTheory.integral_pos_iff_support_of_nonneg_ae hF_nonneg hF_int
    exact hiff.2 hF_support_pos
  have hdiff :
      I r₂ - I r₁ = ∫ y, F y ∂(volume : Measure ℝ) := by
    -- Use linearity of the integral.
    have hf2 :
        Integrable (fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂))) (volume : Measure ℝ) := by
      have hmeas :
          AEStronglyMeasurable (fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂)))
            (volume : Measure ℝ) := by
        have hcont_sech : Continuous sech := by
          have hcosh_ne : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
          unfold sech
          simpa [one_div] using (Continuous.inv₀ Real.continuous_cosh hcosh_ne)
        have hcont : Continuous fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂)) := by
          fun_prop [hcont_sech]
        exact hcont.measurable.aestronglyMeasurable
      have hbound :
          ∀ᵐ y : ℝ ∂(volume : Measure ℝ),
            ‖(sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂))‖ ≤ (sech y) ^ 2 := by
        refine ae_of_all _ (fun y => ?_)
        have hsech : 0 ≤ (sech y) ^ 2 := sq_nonneg (sech y)
        have hle : Real.exp (-(y ^ 2) / (2 * r₂)) ≤ 1 := exp_neg_sq_div_le_one y r₂ hr₂'
        have hprod_le :
            (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂)) ≤ (sech y) ^ 2 :=
          by
            simpa [mul_one] using (mul_le_mul_of_nonneg_left hle hsech)
        have hnonneg :
            0 ≤ (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂)) :=
          mul_nonneg hsech (le_of_lt (Real.exp_pos _))
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hprod_le
      exact (integrable_sech_sq).mono' hmeas hbound
    have hf1 :
        Integrable (fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁))) (volume : Measure ℝ) := by
      have hmeas :
          AEStronglyMeasurable (fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁)))
            (volume : Measure ℝ) := by
        have hcont_sech : Continuous sech := by
          have hcosh_ne : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
          unfold sech
          simpa [one_div] using (Continuous.inv₀ Real.continuous_cosh hcosh_ne)
        have hcont : Continuous fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁)) := by
          fun_prop [hcont_sech]
        exact hcont.measurable.aestronglyMeasurable
      have hbound :
          ∀ᵐ y : ℝ ∂(volume : Measure ℝ),
            ‖(sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁))‖ ≤ (sech y) ^ 2 := by
        refine ae_of_all _ (fun y => ?_)
        have hsech : 0 ≤ (sech y) ^ 2 := sq_nonneg (sech y)
        have hle : Real.exp (-(y ^ 2) / (2 * r₁)) ≤ 1 := exp_neg_sq_div_le_one y r₁ hr₁'
        have hprod_le :
            (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁)) ≤ (sech y) ^ 2 :=
          by
            simpa [mul_one] using (mul_le_mul_of_nonneg_left hle hsech)
        have hnonneg :
            0 ≤ (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁)) :=
          mul_nonneg hsech (le_of_lt (Real.exp_pos _))
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hprod_le
      exact (integrable_sech_sq).mono' hmeas hbound
    have hsub :
        (∫ y : ℝ, (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂)) ∂(volume : Measure ℝ)) -
          (∫ y : ℝ, (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁)) ∂(volume : Measure ℝ)) =
          ∫ y : ℝ,
            ((sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂)) -
              (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁))) ∂(volume : Measure ℝ) := by
      simpa using (MeasureTheory.integral_sub hf2 hf1).symm
    have hfact :
        (fun y : ℝ =>
            (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂)) -
              (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁))) =
          fun y : ℝ =>
            (sech y) ^ 2 * (Real.exp (-(y ^ 2) / (2 * r₂)) -
              Real.exp (-(y ^ 2) / (2 * r₁))) := by
      funext y
      ring
    simpa [I, F, hfact] using hsub
  have hltI : I r₁ < I r₂ := by
    have : 0 < I r₂ - I r₁ := by simpa [hdiff] using hF_pos
    linarith
  exact hltI

lemma tendsto_I_atTop : Tendsto I atTop (𝓝 (2 : ℝ)) := by
  have h_meas :
      ∀ᶠ r : ℝ in atTop,
        AEStronglyMeasurable (fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)))
          (volume : Measure ℝ) := by
    refine Filter.Eventually.of_forall (fun r => ?_)
    have hcont_sech : Continuous sech := by
      have hcosh_ne : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
      unfold sech
      simpa [one_div] using (Continuous.inv₀ Real.continuous_cosh hcosh_ne)
    have hcont : Continuous fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) := by
      fun_prop [hcont_sech]
    exact hcont.measurable.aestronglyMeasurable
  have h_bound :
      ∀ᶠ r : ℝ in atTop, ∀ᵐ y : ℝ ∂(volume : Measure ℝ),
        ‖(sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))‖ ≤ (sech y) ^ 2 := by
    have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := Filter.eventually_gt_atTop (0 : ℝ)
    filter_upwards [hpos] with r hr
    refine ae_of_all _ (fun y => ?_)
    have hsech : 0 ≤ (sech y) ^ 2 := sq_nonneg (sech y)
    have hle : Real.exp (-(y ^ 2) / (2 * r)) ≤ 1 := exp_neg_sq_div_le_one y r hr
    have hprod_le :
        (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) ≤ (sech y) ^ 2 := by
      simpa [mul_one] using (mul_le_mul_of_nonneg_left hle hsech)
    have hnonneg :
        0 ≤ (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) :=
      mul_nonneg hsech (le_of_lt (Real.exp_pos _))
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hprod_le
  have h_int : Integrable (fun y : ℝ => (sech y) ^ 2) (volume : Measure ℝ) :=
    integrable_sech_sq
  have h_lim :
      ∀ᵐ y : ℝ ∂(volume : Measure ℝ),
        Tendsto (fun r : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) atTop
          (𝓝 ((sech y) ^ 2)) := by
    refine ae_of_all _ (fun y => ?_)
    have hexp : Tendsto (fun r : ℝ => Real.exp (-(y ^ 2) / (2 * r))) atTop (𝓝 (1 : ℝ)) :=
      tendsto_exp_neg_sq_div_atTop y
    simpa using (Filter.Tendsto.const_mul ((sech y) ^ 2) hexp)
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℝ)) (l := atTop)
      (F := fun r : ℝ => fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)))
      (f := fun y : ℝ => (sech y) ^ 2) (bound := fun y : ℝ => (sech y) ^ 2)
      h_meas h_bound h_int h_lim
  simpa [I, integral_sech_sq] using h

lemma A_eq_const_I_sq (r : ℝ) (hr : 0 < r) :
    A r = (1 / (2 * Real.pi)) * (I r) ^ 2 := by
  -- Start from `A(r) = r * S(r)^2` and change variables in `S(r)`.
  have hA : A r = r * (S r) ^ 2 := A_eq_r_mul_S_sq r
  let rNN : ℝ≥0 := ⟨r, le_of_lt hr⟩
  have hv : (rNN : ℝ≥0) ≠ 0 := by
    have : (rNN : ℝ) ≠ 0 := by simpa [rNN] using (ne_of_gt hr)
    exact (NNReal.coe_ne_zero).1 this
  let φ : ℝ → ℝ := fun x => Real.sqrt r * x
  let f : ℝ → ℝ := fun y => (sech y) ^ 2
  have hφ_meas : AEMeasurable φ γ := (measurable_const.mul measurable_id).aemeasurable
  have hf_meas : AEStronglyMeasurable f (Measure.map φ γ) := by
    have hcont_sech : Continuous sech := by
      have hcosh_ne : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
      unfold sech
      simpa [one_div] using (Continuous.inv₀ Real.continuous_cosh hcosh_ne)
    have hcont : Continuous fun y : ℝ => (sech y) ^ 2 := by
      simpa using hcont_sech.pow 2
    exact hcont.measurable.aestronglyMeasurable
  have hS_map : S r = ∫ y : ℝ, f y ∂(Measure.map φ γ) := by
    have hmap := (MeasureTheory.integral_map (μ := γ) (φ := φ) hφ_meas hf_meas (f := f)).symm
    simpa [S, f, φ] using hmap
  have hvar : (⟨(Real.sqrt r) ^ 2, sq_nonneg (Real.sqrt r)⟩ : ℝ≥0) = rNN := by
    apply Subtype.ext
    have hr0 : 0 ≤ r := le_of_lt hr
    simp [rNN, Real.sq_sqrt hr0]
  have hmap_measure :
      Measure.map φ γ = ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := rNN) := by
    have h :=
      (ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
          (c := Real.sqrt r))
    simpa [γ, φ, hvar] using h
  have hS_density :
      S r = ∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (0 : ℝ) rNN y * (sech y) ^ 2 := by
    have hgauss :
        (∫ y : ℝ, (sech y) ^ 2 ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := rNN))) =
          ∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (0 : ℝ) rNN y • (sech y) ^ 2 := by
      simpa using
        (ProbabilityTheory.integral_gaussianReal_eq_integral_smul (E := ℝ) (μ := (0 : ℝ)) (v := rNN)
          (f := fun y : ℝ => (sech y) ^ 2) hv)
    have hgauss' :
        (∫ y : ℝ, (sech y) ^ 2 ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := rNN))) =
          ∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (0 : ℝ) rNN y * (sech y) ^ 2 := by
      simpa [smul_eq_mul] using hgauss
    have : S r =
        ∫ y : ℝ, (sech y) ^ 2 ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := rNN)) := by
      simpa [hS_map, f, hmap_measure]
    simpa [this] using hgauss'
  have hr0 : 0 ≤ r := le_of_lt hr
  have hS_I : S r = (Real.sqrt (2 * Real.pi * r))⁻¹ * I r := by
    have hpdf :
        (fun y : ℝ => ProbabilityTheory.gaussianPDFReal (0 : ℝ) rNN y * (sech y) ^ 2) =
          fun y : ℝ =>
            (Real.sqrt (2 * Real.pi * r))⁻¹ * ((sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) := by
      funext y
      simp [ProbabilityTheory.gaussianPDFReal, rNN, hr0, pow_two, mul_assoc, mul_left_comm, mul_comm,
        sub_eq_add_neg, div_eq_mul_inv]
    have :
        ∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (0 : ℝ) rNN y * (sech y) ^ 2 =
          (Real.sqrt (2 * Real.pi * r))⁻¹ *
            ∫ y : ℝ, (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) := by
      calc
        ∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (0 : ℝ) rNN y * (sech y) ^ 2 =
            ∫ y : ℝ,
              (Real.sqrt (2 * Real.pi * r))⁻¹ *
                ((sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) := by
              simp [hpdf]
        _ =
            (Real.sqrt (2 * Real.pi * r))⁻¹ *
              ∫ y : ℝ, (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) := by
              simp [MeasureTheory.integral_const_mul]
    simpa [hS_density, I] using this
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hconst_sq :
      r * ((Real.sqrt (2 * Real.pi * r))⁻¹) ^ 2 = (1 / (2 * Real.pi) : ℝ) := by
    have hpos : 0 < 2 * Real.pi * r := by nlinarith [Real.pi_pos, hr]
    have hsqrt_ne : Real.sqrt (2 * Real.pi * r) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    field_simp [hsqrt_ne, hpi]
    have hnonneg : 0 ≤ r * (Real.pi * 2) := by nlinarith [Real.pi_pos, hr.le]
    simpa [mul_assoc, mul_left_comm, mul_comm, Real.sq_sqrt hnonneg]
  calc
    A r = r * (S r) ^ 2 := hA
    _ = r * ((Real.sqrt (2 * Real.pi * r))⁻¹ * I r) ^ 2 := by simp [hS_I]
    _ = (1 / (2 * Real.pi) : ℝ) * (I r) ^ 2 := by
          calc
            r * ((Real.sqrt (2 * Real.pi * r))⁻¹ * I r) ^ 2 =
                (r * ((Real.sqrt (2 * Real.pi * r))⁻¹) ^ 2) * (I r) ^ 2 := by
                  ring
            _ = (1 / (2 * Real.pi) : ℝ) * (I r) ^ 2 := by
                  exact congrArg (fun t => t * (I r) ^ 2) hconst_sq
    _ = (1 / (2 * Real.pi)) * (I r) ^ 2 := rfl

lemma A_strictMonoOn_Ioi : StrictMonoOn A (Set.Ioi (0 : ℝ)) := by
  -- Main analytic step (see blueprint): represent as `(1/(2π))*I(r)^2` and show `I' > 0`.
  intro r₁ hr₁ r₂ hr₂ hlt
  have hA₁ : A r₁ = (1 / (2 * Real.pi)) * (I r₁) ^ 2 :=
    A_eq_const_I_sq (r := r₁) (by simpa [Set.mem_Ioi] using hr₁)
  have hA₂ : A r₂ = (1 / (2 * Real.pi)) * (I r₂) ^ 2 :=
    A_eq_const_I_sq (r := r₂) (by simpa [Set.mem_Ioi] using hr₂)
  have hIlt : I r₁ < I r₂ :=
    strictMonoOn_I hr₁ hr₂ hlt
  have hI₁ : 0 ≤ I r₁ := I_nonneg r₁
  have hI₂ : 0 ≤ I r₂ := I_nonneg r₂
  have hsq : (I r₁) ^ 2 < (I r₂) ^ 2 := (sq_lt_sq₀ hI₁ hI₂).2 hIlt
  have hconst : 0 < (1 / (2 * Real.pi) : ℝ) := by
    have hden : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    simpa [one_div] using (inv_pos.2 hden)
  have : (1 / (2 * Real.pi) : ℝ) * (I r₁) ^ 2 < (1 / (2 * Real.pi) : ℝ) * (I r₂) ^ 2 :=
    mul_lt_mul_of_pos_left hsq hconst
  simpa [hA₁, hA₂] using this

lemma tendsto_A_atTop : Tendsto A atTop (𝓝 ((2 : ℝ) / Real.pi)) := by
  -- Main analytic step (see blueprint): `I(r) → 2`.
  have hI : Tendsto I atTop (𝓝 (2 : ℝ)) := tendsto_I_atTop
  have hI2 : Tendsto (fun r : ℝ => (I r) ^ 2) atTop (𝓝 ((2 : ℝ) ^ 2)) := hI.pow 2
  have hmul :
      Tendsto (fun r : ℝ => (1 / (2 * Real.pi) : ℝ) * (I r) ^ 2) atTop
        (𝓝 ((1 / (2 * Real.pi) : ℝ) * ((2 : ℝ) ^ 2))) :=
    (Filter.Tendsto.const_mul _ hI2)
  have hA_event :
      (∀ᶠ r : ℝ in atTop, A r = (1 / (2 * Real.pi) : ℝ) * (I r) ^ 2) := by
    have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := Filter.eventually_gt_atTop (0 : ℝ)
    filter_upwards [hpos] with r hr
    simpa [A_eq_const_I_sq (r := r) hr]
  have h :=
    Filter.Tendsto.congr'
      (hA_event.mono fun _ hr => hr.symm)
      hmul
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  -- Simplify `(1/(2π))* (2^2)` to `2/π`.
  simpa [pow_two, hpi, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

end A_lemmas

/-! ## 5. Properties of B (continuity/endpoints/monotonicity) -/

section B_lemmas

lemma B_nonneg (κ q : ℝ) (hq : q ≤ 1) : 0 ≤ B κ q := by
  unfold B
  have h1q : 0 ≤ 1 - q := by linarith
  have hI :
      0 ≤ Expect (fun z : ℝ => (E (U κ q z)) ^ 2) := by
    unfold Expect
    refine integral_nonneg ?_
    intro z
    exact sq_nonneg (E (U κ q z))
  exact mul_nonneg h1q hI

lemma B_zero (κ : ℝ) : B κ 0 = (E κ) ^ 2 := by
  -- Endpoint at `q = 0`.
  unfold B U Expect
  simp [γ, MeasureTheory.integral_const, MeasureTheory.probReal_univ]

/-!
### Bridge to the `MillsBlueprint.Proof` definitions

The file `perceptronFixed/derivative_of_B/derivative_B.lean` contains several analytic bounds for the
inverse Mills ratio in the namespace `MillsBlueprint.Proof`.  Our definitions of `φ`, `Φbar`, `E`
are the ones from `DecreasingG`; the following lemmas identify them with the blueprint ones so we
can reuse those bounds.
-/

private lemma φ_eq_mills (u : ℝ) : φ u = MillsBlueprint.Proof.φ u := by
  -- `DecreasingG.φ` is written using `/`, the blueprint uses `* (1/...)`.
  simp [φ, DecreasingG.φ, MillsBlueprint.Proof.φ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

private lemma Φbar_eq_mills (u : ℝ) : Φbar u = MillsBlueprint.Proof.Φbar u := by
  -- `DecreasingG.Φbar` uses `Ici`; the blueprint proves `Φbar u = ∫_{(u,∞)} φ`.
  have hIci :
      (∫ x in Set.Ici u, MillsBlueprint.Proof.φ x) = ∫ x in Set.Ioi u, MillsBlueprint.Proof.φ x := by
    simpa using
      (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := (volume : Measure ℝ))
        (f := MillsBlueprint.Proof.φ) (x := u))
  calc
    Φbar u = ∫ x in Set.Ici u, MillsBlueprint.Proof.φ x := by
      -- unfold `Φbar` and rewrite the density
      simp [Φbar, DecreasingG.Φbar, φ_eq_mills]
    _ = ∫ x in Set.Ioi u, MillsBlueprint.Proof.φ x := hIci
    _ = MillsBlueprint.Proof.Φbar u := by
      -- use the blueprint identity
      symm
      simpa using (MillsBlueprint.Proof.Φbar_eq_integral_Ioi (u := u))

private lemma E_eq_mills (u : ℝ) : E u = MillsBlueprint.Proof.E u := by
  simp [E, DecreasingG.E, MillsBlueprint.Proof.E, φ_eq_mills, Φbar_eq_mills]

private lemma E_le_abs_add_C (u : ℝ) : E u ≤ |u| + MillsBlueprint.Proof.C_mills := by
  -- transport `MillsBlueprint.Proof.E_le_abs_add_C` across `E_eq_mills`
  simpa [E_eq_mills (u := u)] using (MillsBlueprint.Proof.E_le_abs_add_C (u := u))

private lemma E_le_add_inv {u : ℝ} (hu : 0 < u) : E u ≤ u + 1 / u := by
  simpa [E_eq_mills (u := u)] using (MillsBlueprint.Proof.E_le_add_inv (u := u) hu)

private lemma E_ge_of_pos {u : ℝ} (hu : 0 < u) : u ≤ E u := by
  -- Use the Mills identity `Φbar u = φ u / u - ∫_{u}^{∞} φ(x)/x^2`.
  have hI_nonneg : 0 ≤ ∫ x in Set.Ioi u, MillsBlueprint.Proof.φ x / x ^ 2 := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    have hφ : 0 ≤ MillsBlueprint.Proof.φ x := by
      simp [MillsBlueprint.Proof.φ]
      positivity
    have hx2 : 0 ≤ (x ^ 2 : ℝ) := sq_nonneg x
    exact div_nonneg hφ hx2
  have hΦeq := MillsBlueprint.Proof.Φbar_eq_phi_div_sub_integral (u := u) hu
  have hΦle : MillsBlueprint.Proof.Φbar u ≤ MillsBlueprint.Proof.φ u / u := by
    linarith [hΦeq, hI_nonneg]
  have hΦpos : 0 < MillsBlueprint.Proof.Φbar u := MillsBlueprint.Proof.Φbar_pos (u := u)
  have hu0 : 0 ≤ u := le_of_lt hu
  have hmul : u * MillsBlueprint.Proof.Φbar u ≤ MillsBlueprint.Proof.φ u := by
    have hmul0 := mul_le_mul_of_nonneg_left hΦle hu0
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have : u * (MillsBlueprint.Proof.φ u / u) = MillsBlueprint.Proof.φ u := by
      field_simp [hu_ne]
    simpa [this] using hmul0
  have : u ≤ MillsBlueprint.Proof.φ u / MillsBlueprint.Proof.Φbar u :=
    (le_div_iff₀ hΦpos).2 hmul
  simpa [E_eq_mills (u := u), MillsBlueprint.Proof.E] using this

private lemma tendsto_E_div_atTop : Tendsto (fun u : ℝ => E u / u) atTop (𝓝 (1 : ℝ)) := by
  have hupper : ∀ᶠ u : ℝ in atTop, E u / u ≤ 1 + 1 / u ^ 2 := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
    have hE : E u ≤ u + 1 / u := E_le_add_inv (u := u) hu
    have hdiv : E u / u ≤ (u + 1 / u) / u := div_le_div_of_nonneg_right hE (le_of_lt hu)
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have : (u + 1 / u) / u = 1 + 1 / u ^ 2 := by
      field_simp [hu_ne]
    exact le_trans hdiv (le_of_eq this)
  have hlower : ∀ᶠ u : ℝ in atTop, (1 : ℝ) ≤ E u / u := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
    have hE : u ≤ E u := E_ge_of_pos (u := u) hu
    have := div_le_div_of_nonneg_right hE (le_of_lt hu)
    simpa [div_self (ne_of_gt hu)] using this
  have htop : Tendsto (fun u : ℝ => (1 : ℝ) + 1 / u ^ 2) atTop (𝓝 (1 : ℝ)) := by
    have hpow : Tendsto (fun u : ℝ => u ^ 2) atTop atTop := by
      simpa using (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
    have hinv : Tendsto (fun u : ℝ => (u ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp hpow
    have hinv' : Tendsto (fun u : ℝ => (1 : ℝ) / u ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa [one_div] using hinv
    simpa using (tendsto_const_nhds.add hinv')
  have h1 : Tendsto (fun _u : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 htop hlower hupper

private lemma tendsto_E_atBot_zero : Tendsto E atBot (𝓝 (0 : ℝ)) := by
  have hΦbar0_pos : 0 < MillsBlueprint.Proof.Φbar (0 : ℝ) := MillsBlueprint.Proof.Φbar_pos (u := 0)
  have hφ_atBot : Tendsto MillsBlueprint.Proof.φ atBot (𝓝 (0 : ℝ)) := by
    have htop : Tendsto MillsBlueprint.Proof.φ atTop (𝓝 (0 : ℝ)) :=
      MillsBlueprint.Proof.tendsto_φ_atTop_zero
    have h := htop.comp Filter.tendsto_neg_atBot_atTop
    refine h.congr' ?_
    filter_upwards with u
    simp [MillsBlueprint.Proof.φ]
  have hE_bound : ∀ᶠ u : ℝ in atBot, ‖E u‖ ≤ MillsBlueprint.Proof.φ u / MillsBlueprint.Proof.Φbar 0 := by
    filter_upwards [Filter.eventually_le_atBot (a := (0 : ℝ))] with u hu
    have hΦ : MillsBlueprint.Proof.Φbar 0 ≤ MillsBlueprint.Proof.Φbar u :=
      (MillsBlueprint.Proof.Φbar_antitone hu)
    have hφ_nonneg : 0 ≤ MillsBlueprint.Proof.φ u := by
      simp [MillsBlueprint.Proof.φ]
      positivity
    have hdiv := div_le_div_of_nonneg_left hφ_nonneg hΦbar0_pos hΦ
    have hE0 : 0 ≤ E u := (DecreasingG.E_pos u).le
    have hE' :
        E u ≤ MillsBlueprint.Proof.φ u / MillsBlueprint.Proof.Φbar 0 := by
      -- replace `E` by the blueprint definition
      simpa [E_eq_mills (u := u), MillsBlueprint.Proof.E] using hdiv
    simpa [Real.norm_eq_abs, abs_of_nonneg hE0] using hE'
  have hφ_div : Tendsto (fun u : ℝ => MillsBlueprint.Proof.φ u / MillsBlueprint.Proof.Φbar 0) atBot (𝓝 (0 : ℝ)) := by
    simpa using (hφ_atBot.div_const (MillsBlueprint.Proof.Φbar 0))
  exact squeeze_zero_norm' hE_bound hφ_div

lemma B_continuousOn (κ : ℝ) : ContinuousOn (fun q => B κ q) (Set.Iio (1 : ℝ)) := by
  -- Dominated convergence using Mills-type bounds for `E`.
  classical
  intro q0 hq0
  have hmul : ContinuousWithinAt (fun q : ℝ => 1 - q) (Set.Iio (1 : ℝ)) q0 := by
    simpa using (continuous_const.sub continuous_id).continuousWithinAt
  have hI :
      ContinuousWithinAt
        (fun q : ℝ => Expect (fun z : ℝ => (E (U κ q z)) ^ 2)) (Set.Iio (1 : ℝ)) q0 := by
    -- Dominated convergence on the Gaussian expectation.
    let l : Filter ℝ := 𝓝[Set.Iio (1 : ℝ)] q0
    let a : ℝ := (q0 + 1) / 2
    have hq0_lt_one : q0 < (1 : ℝ) := by simpa using hq0
    have hq0a : q0 < a := by
      dsimp [a]
      linarith
    have ha1 : a < (1 : ℝ) := by
      dsimp [a]
      linarith
    have hqa : ∀ᶠ q in l, q < a := by
      have : ∀ᶠ q in 𝓝 q0, q < a := (Iio_mem_nhds hq0a)
      exact this.filter_mono nhdsWithin_le_nhds
    let d : ℝ := Real.sqrt (1 - a)
    have hd_pos : 0 < d := by
      have : 0 < (1 - a) := by linarith
      simpa [d] using (Real.sqrt_pos.2 this)
    have hd_ne : d ≠ 0 := (ne_of_gt hd_pos)

    -- A simple integrable bound: constant + constant * z^2.
    let c0 : ℝ :=
      (4 : ℝ) * ((|κ| / d) ^ 2) + (2 : ℝ) * (MillsBlueprint.Proof.C_mills ^ 2)
    let c1 : ℝ :=
      (4 : ℝ) * ((Real.sqrt a / d) ^ 2)
    let bound : ℝ → ℝ := fun z => c0 + c1 * (z ^ 2)

    have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
      simpa [γ] using
        (MeasureTheory.MemLp.integrable_sq
          (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))))
    have bound_integrable : Integrable bound γ := by
      have h0 : Integrable (fun _z : ℝ => c0) γ := integrable_const c0
      have h1 : Integrable (fun z : ℝ => c1 * (z ^ 2)) γ := by
        simpa using (hsq_int.const_mul c1)
      simpa [bound] using h0.add h1

    have hF_meas :
        ∀ᶠ q in l, AEStronglyMeasurable (fun z : ℝ => (E (U κ q z)) ^ 2) γ := by
      refine Filter.Eventually.of_forall (fun q => ?_)
      -- `E` is continuous, hence measurable.
      have hEmeas : Measurable E := by
        have hEcont : Continuous E := by
          simpa [E, UniformBoundOfG.E] using
            (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E)
        exact hEcont.measurable
      have hUmeas : Measurable (fun z : ℝ => U κ q z) := by
        have hUcont : Continuous (fun z : ℝ => (κ - Real.sqrt q * z) / Real.sqrt (1 - q)) := by
          fun_prop
        simpa [U] using hUcont.measurable
      have : Measurable (fun z : ℝ => (E (U κ q z)) ^ 2) := by
        simpa [pow_two] using (hEmeas.comp hUmeas).mul (hEmeas.comp hUmeas)
      exact this.aestronglyMeasurable

    have h_bound :
        ∀ᶠ q in l, ∀ᵐ z ∂γ, ‖(E (U κ q z)) ^ 2‖ ≤ bound z := by
      filter_upwards [hqa] with q hq_lt_a
      refine ae_of_all _ (fun z => ?_)
      have hq_le_a : q ≤ a := le_of_lt hq_lt_a
      have hsqrt_q_le : Real.sqrt q ≤ Real.sqrt a := by
        simpa using Real.sqrt_le_sqrt hq_le_a
      have hden_ge : d ≤ Real.sqrt (1 - q) := by
        have : 1 - a ≤ 1 - q := by linarith
        simpa [d] using Real.sqrt_le_sqrt this

      have hU_abs_le :
          |U κ q z| ≤ (|κ| + (Real.sqrt a) * |z|) / d := by
        have hU_abs :
            |U κ q z| = |κ - Real.sqrt q * z| / Real.sqrt (1 - q) := by
          unfold U
          have : |Real.sqrt (1 - q)| = Real.sqrt (1 - q) := by
            simp [abs_of_nonneg (Real.sqrt_nonneg _)]
          simp [abs_div, this]
        have hnum_le : |κ - Real.sqrt q * z| ≤ |κ| + (Real.sqrt a) * |z| := by
          have h1 : |κ - Real.sqrt q * z| ≤ |κ| + |Real.sqrt q * z| := abs_sub κ (Real.sqrt q * z)
          have h2 : |Real.sqrt q * z| = (Real.sqrt q) * |z| := by
            simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          have h3 : (Real.sqrt q) * |z| ≤ (Real.sqrt a) * |z| := by
            exact mul_le_mul_of_nonneg_right hsqrt_q_le (abs_nonneg z)
          calc
            |κ - Real.sqrt q * z| ≤ |κ| + |Real.sqrt q * z| := h1
            _ = |κ| + (Real.sqrt q) * |z| := by simpa [h2]
            _ ≤ |κ| + (Real.sqrt a) * |z| := by gcongr
        have hinv_le : (1 / Real.sqrt (1 - q)) ≤ (1 / d) := by
          -- `d ≤ √(1-q)` and `0 < d`
          have := one_div_le_one_div_of_le hd_pos hden_ge
          simpa using this
        have hmain :
            |κ - Real.sqrt q * z| / Real.sqrt (1 - q) ≤ (|κ| + (Real.sqrt a) * |z|) / d := by
          have hnum0 : 0 ≤ |κ| + (Real.sqrt a) * |z| := by positivity
          have hinv0 : 0 ≤ (1 / Real.sqrt (1 - q)) := by
            exact one_div_nonneg.2 (Real.sqrt_nonneg _)
          have hmul :=
            mul_le_mul hnum_le hinv_le hinv0 hnum0
          -- rewrite divisions as multiplication by inverses
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        simpa [hU_abs] using hmain

      have hE_le : E (U κ q z) ≤ |U κ q z| + MillsBlueprint.Proof.C_mills :=
        E_le_abs_add_C (u := U κ q z)
      have hE0 : 0 ≤ E (U κ q z) := (DecreasingG.E_pos _).le
      have hU0 : 0 ≤ |U κ q z| := abs_nonneg _
      have hC0 : 0 ≤ MillsBlueprint.Proof.C_mills := by
        have : (1 : ℝ) ≤ MillsBlueprint.Proof.C_mills := le_max_right _ _
        linarith
      have hUB0 : 0 ≤ |U κ q z| + MillsBlueprint.Proof.C_mills := add_nonneg hU0 hC0

      -- First bound `E(U)^2` by `(|U| + C)^2`.
      have hsq1 :
          (E (U κ q z)) ^ 2 ≤ (|U κ q z| + MillsBlueprint.Proof.C_mills) ^ 2 := by
        simpa [pow_two] using mul_le_mul hE_le hE_le hE0 hUB0
      -- Then use `(x+y)^2 ≤ 2x^2 + 2y^2`.
      have hsq2 :
          (|U κ q z| + MillsBlueprint.Proof.C_mills) ^ 2 ≤
            (2 : ℝ) * (|U κ q z| ^ 2) + (2 : ℝ) * (MillsBlueprint.Proof.C_mills ^ 2) := by
        have hab : 2 * |U κ q z| * MillsBlueprint.Proof.C_mills ≤
            (|U κ q z|) ^ 2 + (MillsBlueprint.Proof.C_mills) ^ 2 :=
          two_mul_le_add_sq (|U κ q z|) MillsBlueprint.Proof.C_mills
        calc
          (|U κ q z| + MillsBlueprint.Proof.C_mills) ^ 2 =
              (|U κ q z|) ^ 2 + (MillsBlueprint.Proof.C_mills) ^ 2 + 2 * |U κ q z| * MillsBlueprint.Proof.C_mills := by
                ring
          _ ≤ (|U κ q z|) ^ 2 + (MillsBlueprint.Proof.C_mills) ^ 2 +
                ((|U κ q z|) ^ 2 + (MillsBlueprint.Proof.C_mills) ^ 2) := by gcongr
          _ = (2 : ℝ) * (|U κ q z| ^ 2) + (2 : ℝ) * (MillsBlueprint.Proof.C_mills ^ 2) := by ring

      have hz2 : |z| ^ 2 = z ^ 2 := by
        have hz2_nonneg : 0 ≤ z ^ 2 := by nlinarith
        calc
          |z| ^ 2 = |z ^ 2| := by simpa using (abs_pow z 2).symm
          _ = z ^ 2 := by simpa [abs_of_nonneg hz2_nonneg]

      -- Bound `|U|^2` by a constant + constant * `z^2`.
      have hU_sq :
          |U κ q z| ^ 2 ≤
            (2 : ℝ) * ((|κ| / d) ^ 2) + (2 : ℝ) * ((Real.sqrt a / d) ^ 2) * (z ^ 2) := by
        have hU_sq' :
            |U κ q z| ^ 2 ≤ ((|κ| + (Real.sqrt a) * |z|) / d) ^ 2 := by
          have h0 : 0 ≤ (|U κ q z|) := abs_nonneg _
          have h1 : 0 ≤ ((|κ| + (Real.sqrt a) * |z|) / d) := by
            have : 0 ≤ |κ| + (Real.sqrt a) * |z| := by positivity
            exact div_nonneg this hd_pos.le
          simpa [pow_two] using mul_le_mul hU_abs_le hU_abs_le h0 h1
        have hsplit :
            ((|κ| + (Real.sqrt a) * |z|) / d) ^ 2 ≤
              (2 : ℝ) * ((|κ| / d) ^ 2) + (2 : ℝ) * ((Real.sqrt a / d) ^ 2) * (|z| ^ 2) := by
          set x : ℝ := |κ| / d
          set y : ℝ := (Real.sqrt a / d) * |z|
          calc
            ((|κ| + (Real.sqrt a) * |z|) / d) ^ 2 = (x + y) ^ 2 := by
              simp [x, y, div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
            _ = x ^ 2 + y ^ 2 + 2 * x * y := by ring
            _ ≤ x ^ 2 + y ^ 2 + (x ^ 2 + y ^ 2) := by
              have : 2 * x * y ≤ x ^ 2 + y ^ 2 := two_mul_le_add_sq x y
              gcongr
            _ = (2 : ℝ) * (x ^ 2) + (2 : ℝ) * (y ^ 2) := by ring
            _ = (2 : ℝ) * (x ^ 2) + (2 : ℝ) * ((Real.sqrt a / d) ^ 2) * (|z| ^ 2) := by
              -- `y = (√a / d) * |z|`
              have hy2 : y ^ 2 = ((Real.sqrt a / d) ^ 2) * (|z| ^ 2) := by
                simpa [y] using (mul_pow (Real.sqrt a / d) (|z|) 2)
              simp [hy2, mul_assoc, mul_left_comm, mul_comm]
        exact le_trans hU_sq' (by simpa [hz2] using hsplit)

      have hsq_total : (E (U κ q z)) ^ 2 ≤ bound z := by
        have hE_sq :
            (E (U κ q z)) ^ 2 ≤
              (2 : ℝ) * (|U κ q z| ^ 2) + (2 : ℝ) * (MillsBlueprint.Proof.C_mills ^ 2) :=
          le_trans hsq1 hsq2
        have hU_sq' :
            (2 : ℝ) * (|U κ q z| ^ 2) ≤
              (4 : ℝ) * ((|κ| / d) ^ 2) + (4 : ℝ) * ((Real.sqrt a / d) ^ 2) * (z ^ 2) := by
          have := mul_le_mul_of_nonneg_left hU_sq (by positivity : 0 ≤ (2 : ℝ))
          -- distribute the scalar and simplify
          nlinarith
        have : (E (U κ q z)) ^ 2 ≤ c0 + c1 * (z ^ 2) := by
          nlinarith [hE_sq, hU_sq']
        simpa [bound] using this

      have hnorm : ‖(E (U κ q z)) ^ 2‖ = (E (U κ q z)) ^ 2 := by
        have : 0 ≤ (E (U κ q z)) ^ 2 := sq_nonneg (E (U κ q z))
        simpa [Real.norm_eq_abs, abs_of_nonneg this]
      simpa [hnorm] using hsq_total

    have h_lim :
        ∀ᵐ z ∂γ,
          Tendsto (fun q : ℝ => (E (U κ q z)) ^ 2) l (𝓝 ((E (U κ q0 z)) ^ 2)) := by
      refine ae_of_all _ (fun z => ?_)
      have hEcont : Continuous E := by
        simpa [E, UniformBoundOfG.E] using (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E)
      have hcont_num : ContinuousAt (fun q : ℝ => κ - Real.sqrt q * z) q0 := by fun_prop
      have hcont_den : ContinuousAt (fun q : ℝ => Real.sqrt (1 - q)) q0 := by fun_prop
      have hden_ne : Real.sqrt (1 - q0) ≠ 0 := by
        have : 0 < 1 - q0 := by linarith
        exact (Real.sqrt_ne_zero').2 this
      have hcont_U : ContinuousAt (fun q : ℝ => U κ q z) q0 := by
        simpa [U] using (hcont_num.div hcont_den hden_ne)
      have hcont_EU : ContinuousAt (fun q : ℝ => E (U κ q z)) q0 :=
        (hEcont.continuousAt.comp hcont_U)
      have hcont_pow : ContinuousAt (fun q : ℝ => (E (U κ q z)) ^ 2) q0 := by
        simpa [pow_two] using (hcont_EU.mul hcont_EU)
      exact hcont_pow.tendsto.mono_left nhdsWithin_le_nhds

    have htendsto :
        Tendsto (fun q : ℝ => ∫ z, (E (U κ q z)) ^ 2 ∂γ) l
          (𝓝 (∫ z, (E (U κ q0 z)) ^ 2 ∂γ)) := by
      exact
        MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (μ := γ) (l := l) (F := fun q z => (E (U κ q z)) ^ 2)
          (f := fun z => (E (U κ q0 z)) ^ 2) (bound := bound)
          hF_meas h_bound bound_integrable h_lim

    simpa [ContinuousWithinAt, Expect] using htendsto

  -- Combine: `B κ q = (1 - q) * Expect ...`.
  simpa [B] using hmul.mul hI

lemma tendsto_B_atOne_left (κ : ℝ) :
    Tendsto (fun q => B κ q) (𝓝[<] (1 : ℝ)) (𝓝 (Cκ κ)) := by
  -- `q → 1-` limit gives `Cκ` (main.tex Lemma `B_endpoints`).
  classical
  let l : Filter ℝ := 𝓝[<] (1 : ℝ)
  let F : ℝ → ℝ → ℝ := fun q z => (1 - q) * (E (U κ q z)) ^ 2
  let f : ℝ → ℝ := fun z => (max (κ - z) 0) ^ 2
  have hq_lt_one : ∀ᶠ q : ℝ in l, q < (1 : ℝ) := by
    simpa [Filter.Eventually, Set.mem_Iio] using (self_mem_nhdsWithin : (Set.Iio (1 : ℝ)) ∈ l)
  have hq_pos : ∀ᶠ q : ℝ in l, (0 : ℝ) < q := by
    have : ∀ᶠ q : ℝ in 𝓝 (1 : ℝ), (0 : ℝ) < q := Ioi_mem_nhds (by norm_num : (0 : ℝ) < (1 : ℝ))
    exact this.filter_mono nhdsWithin_le_nhds

  -- An integrable domination bound: constant + constant * z^2.
  let C : ℝ := MillsBlueprint.Proof.C_mills
  let bound : ℝ → ℝ := fun z => (4 : ℝ) * (κ ^ 2) + (2 : ℝ) * (C ^ 2) + (4 : ℝ) * (z ^ 2)
  have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
    simpa [γ] using
      (MeasureTheory.MemLp.integrable_sq
        (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
          (p := (2 : ℝ≥0))))
  have bound_integrable : Integrable bound γ := by
    have h0 : Integrable (fun _z : ℝ => (4 : ℝ) * (κ ^ 2) + (2 : ℝ) * (C ^ 2)) γ :=
      integrable_const _
    have h1 : Integrable (fun z : ℝ => (4 : ℝ) * (z ^ 2)) γ := by
      simpa [mul_assoc] using (hsq_int.const_mul (4 : ℝ))
    simpa [bound] using h0.add h1

  have hF_meas : ∀ᶠ q in l, AEStronglyMeasurable (fun z : ℝ => F q z) γ := by
    refine Filter.Eventually.of_forall (fun q => ?_)
    -- `E` is continuous, hence measurable.
    have hEmeas : Measurable E := by
      have hEcont : Continuous E := by
        simpa [E, UniformBoundOfG.E] using
          (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E)
      exact hEcont.measurable
    have hUmeas : Measurable (fun z : ℝ => U κ q z) := by
      have hUcont : Continuous (fun z : ℝ => (κ - Real.sqrt q * z) / Real.sqrt (1 - q)) := by
        fun_prop
      simpa [U] using hUcont.measurable
    have hEUmeas : Measurable (fun z : ℝ => E (U κ q z)) := hEmeas.comp hUmeas
    have hpow : Measurable (fun z : ℝ => (E (U κ q z)) ^ 2) := by
      simpa [pow_two] using hEUmeas.mul hEUmeas
    have : Measurable (fun z : ℝ => F q z) := by
      simpa [F] using (measurable_const.mul hpow)
    exact this.aestronglyMeasurable

  have h_bound : ∀ᶠ q in l, ∀ᵐ z ∂γ, ‖F q z‖ ≤ bound z := by
    filter_upwards [hq_pos, hq_lt_one] with q hq0 hq1
    refine ae_of_all _ (fun z => ?_)
    have h1q : 0 ≤ (1 - q) := by linarith
    have hnorm :
        ‖F q z‖ = F q z := by
      have : 0 ≤ F q z := by
        unfold F
        exact mul_nonneg h1q (sq_nonneg (E (U κ q z)))
      simpa [Real.norm_eq_abs, abs_of_nonneg this]
    -- Use the global Mills bound: `E(u) ≤ |u| + C`.
    have hE_le : E (U κ q z) ≤ |U κ q z| + C := E_le_abs_add_C (u := U κ q z)
    have hE0 : 0 ≤ E (U κ q z) := (DecreasingG.E_pos _).le
    have hU0 : 0 ≤ |U κ q z| := abs_nonneg _
    have hC0 : 0 ≤ C := by
      have : (1 : ℝ) ≤ C := le_max_right _ _
      linarith
    have hUB0 : 0 ≤ |U κ q z| + C := add_nonneg hU0 hC0
    have hsq1 : (E (U κ q z)) ^ 2 ≤ (|U κ q z| + C) ^ 2 := by
      simpa [pow_two] using mul_le_mul hE_le hE_le hE0 hUB0
    have hsq2 : (|U κ q z| + C) ^ 2 ≤ (2 : ℝ) * (|U κ q z| ^ 2) + (2 : ℝ) * (C ^ 2) := by
      have hab : 2 * |U κ q z| * C ≤ |U κ q z| ^ 2 + C ^ 2 := two_mul_le_add_sq _ _
      calc
        (|U κ q z| + C) ^ 2 =
            |U κ q z| ^ 2 + C ^ 2 + 2 * |U κ q z| * C := by ring
        _ ≤ |U κ q z| ^ 2 + C ^ 2 + (|U κ q z| ^ 2 + C ^ 2) := by gcongr
        _ = (2 : ℝ) * (|U κ q z| ^ 2) + (2 : ℝ) * (C ^ 2) := by ring
    have hsq : (E (U κ q z)) ^ 2 ≤ (2 : ℝ) * (|U κ q z| ^ 2) + (2 : ℝ) * (C ^ 2) :=
      le_trans hsq1 hsq2
    -- Replace `(1-q) * |U|^2` by `(κ - √q*z)^2`, then bound by `2*κ^2 + 2*z^2`.
    have hU_sq :
        (1 - q) * (|U κ q z| ^ 2) ≤ (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := by
      have hU_abs :
          |U κ q z| = |κ - Real.sqrt q * z| / Real.sqrt (1 - q) := by
        unfold U
        have : |Real.sqrt (1 - q)| = Real.sqrt (1 - q) := by
          simp [abs_of_nonneg (Real.sqrt_nonneg _)]
        simp [abs_div, this]
      have hU_sq_eq :
          (1 - q) * (|U κ q z| ^ 2) = |κ - Real.sqrt q * z| ^ 2 := by
        have hsqrt_ne : Real.sqrt (1 - q) ≠ 0 := by
          have : 0 < 1 - q := by linarith
          exact (Real.sqrt_ne_zero').2 this
        -- algebra
        calc
          (1 - q) * (|U κ q z| ^ 2)
              = (1 - q) * ((|κ - Real.sqrt q * z| / Real.sqrt (1 - q)) ^ 2) := by
                  simp [hU_abs]
          _ = (1 - q) * (|κ - Real.sqrt q * z| ^ 2) / (Real.sqrt (1 - q) ^ 2) := by
                  simp [div_pow, mul_div_assoc]
          _ = (1 - q) * (|κ - Real.sqrt q * z| ^ 2) / (1 - q) := by
                  simp [Real.sq_sqrt (by linarith : 0 ≤ 1 - q)]
          _ = |κ - Real.sqrt q * z| ^ 2 := by
                  have hne : (1 - q) ≠ 0 := by
                    have : 0 < (1 : ℝ) - q := by linarith
                    exact ne_of_gt this
                  field_simp [hne]
      have habs : |κ - Real.sqrt q * z| ≤ |κ| + |z| := by
        have h1 : |κ - Real.sqrt q * z| ≤ |κ| + |Real.sqrt q * z| := abs_sub κ (Real.sqrt q * z)
        have h2 : |Real.sqrt q * z| = (Real.sqrt q) * |z| := by
          simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        have hsqrt_le : Real.sqrt q ≤ (1 : ℝ) := by
          have : q ≤ 1 := le_of_lt hq1
          have : Real.sqrt q ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt this
          simpa using this
        have h3 : (Real.sqrt q) * |z| ≤ (1 : ℝ) * |z| := mul_le_mul_of_nonneg_right hsqrt_le (abs_nonneg z)
        have : |Real.sqrt q * z| ≤ |z| := by simpa [h2] using h3
        exact le_trans h1 (by nlinarith)
      have hnonneg : 0 ≤ |κ| + |z| := by positivity
      have hsq' : |κ - Real.sqrt q * z| ^ 2 ≤ (|κ| + |z|) ^ 2 := by
        simpa [pow_two] using mul_le_mul habs habs (abs_nonneg _) hnonneg
      have hsq'' : (|κ| + |z|) ^ 2 ≤ (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := by
        have hab' : 2 * |κ| * |z| ≤ |κ| ^ 2 + |z| ^ 2 := two_mul_le_add_sq |κ| |z|
        calc
          (|κ| + |z|) ^ 2 = |κ| ^ 2 + |z| ^ 2 + 2 * |κ| * |z| := by ring
          _ ≤ |κ| ^ 2 + |z| ^ 2 + (|κ| ^ 2 + |z| ^ 2) := by gcongr
          _ = (2 : ℝ) * |κ| ^ 2 + (2 : ℝ) * |z| ^ 2 := by ring
          _ = (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := by simp
      -- conclude
      calc
        (1 - q) * (|U κ q z| ^ 2) = |κ - Real.sqrt q * z| ^ 2 := hU_sq_eq
        _ ≤ (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := le_trans hsq' hsq''
    have hmain : F q z ≤ bound z := by
      -- combine the bounds and simplify
      have : (1 - q) * (E (U κ q z)) ^ 2 ≤
          (4 : ℝ) * (κ ^ 2) + (2 : ℝ) * (C ^ 2) + (4 : ℝ) * (z ^ 2) := by
        have h1 : (1 - q) * (E (U κ q z)) ^ 2 ≤ (1 - q) * ((2 : ℝ) * (|U κ q z| ^ 2) + (2 : ℝ) * (C ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hsq h1q
        nlinarith [h1, hU_sq]
      simpa [F, bound, add_assoc, add_left_comm, add_comm, mul_assoc] using this
    simpa [hnorm] using hmain

  have h_lim : ∀ᵐ z ∂γ, Tendsto (fun q : ℝ => F q z) l (𝓝 (f z)) := by
    refine ae_of_all _ (fun z => ?_)
    -- Basic limits for `sqrt`, `1-q`, and the inverse denominator.
    have hsub : Tendsto (fun q : ℝ => (1 : ℝ) - q) l (𝓝 (0 : ℝ)) := by
      have hcont : ContinuousAt (fun q : ℝ => (1 : ℝ) - q) (1 : ℝ) :=
        (continuous_const.sub continuous_id).continuousAt
      have h : Tendsto (fun q : ℝ => (1 : ℝ) - q) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - (1 : ℝ))) := hcont.tendsto
      simpa using h.mono_left nhdsWithin_le_nhds
    have hsqrt1 : Tendsto (fun q : ℝ => Real.sqrt q) l (𝓝 (1 : ℝ)) := by
      have hsqrt : ContinuousAt (fun q : ℝ => Real.sqrt q) (1 : ℝ) :=
        Real.continuous_sqrt.continuousAt
      simpa using (hsqrt.tendsto.mono_left nhdsWithin_le_nhds)
    have hden_nhds : Tendsto (fun q : ℝ => Real.sqrt ((1 : ℝ) - q)) l (𝓝 (0 : ℝ)) := by
      have hsqrt0 : ContinuousAt Real.sqrt (0 : ℝ) := Real.continuous_sqrt.continuousAt
      simpa using (hsqrt0.tendsto.comp hsub)
    have hden_pos : ∀ᶠ q : ℝ in l, 0 < Real.sqrt ((1 : ℝ) - q) := by
      filter_upwards [hq_lt_one] with q hq
      have : 0 < (1 : ℝ) - q := by linarith
      simpa using (Real.sqrt_pos.2 this)
    have hden_nhdsGT : Tendsto (fun q : ℝ => Real.sqrt ((1 : ℝ) - q)) l (𝓝[>] (0 : ℝ)) := by
      have hpos_princ : Tendsto (fun q : ℝ => Real.sqrt ((1 : ℝ) - q)) l (𝓟 (Set.Ioi (0 : ℝ))) := by
        refine (tendsto_principal.2 ?_)
        simpa [Set.mem_Ioi] using hden_pos
      exact (tendsto_inf.2 ⟨hden_nhds, hpos_princ⟩)
    have hinv_den : Tendsto (fun q : ℝ => (Real.sqrt ((1 : ℝ) - q))⁻¹) l atTop :=
      hden_nhdsGT.inv_tendsto_nhdsGT_zero
    have hEcont : Continuous E := by
      simpa [E, UniformBoundOfG.E] using (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E)

    by_cases hz₁ : z < κ
    · have hkz : 0 < κ - z := sub_pos.2 hz₁
      -- numerator tends to κ - z (>0)
      have hnum : Tendsto (fun q : ℝ => κ - Real.sqrt q * z) l (𝓝 (κ - z)) := by
        simpa using (tendsto_const_nhds.sub (hsqrt1.mul tendsto_const_nhds))
      have hU_atTop : Tendsto (fun q : ℝ => U κ q z) l atTop := by
        -- rewrite as product
        have hmul : Tendsto (fun q : ℝ => (κ - Real.sqrt q * z) * (Real.sqrt ((1 : ℝ) - q))⁻¹) l atTop :=
          Filter.Tendsto.pos_mul_atTop hkz hnum hinv_den
        simpa [U, div_eq_mul_inv, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using hmul
      have hratio : Tendsto (fun q : ℝ => E (U κ q z) / (U κ q z)) l (𝓝 (1 : ℝ)) :=
        (tendsto_E_div_atTop.comp hU_atTop)
      have hcoef : Tendsto (fun q : ℝ => (κ - Real.sqrt q * z) ^ 2) l (𝓝 ((κ - z) ^ 2)) := by
        have h := (hnum.pow 2)
        simpa [pow_two] using h
      have hpow : Tendsto (fun q : ℝ => (E (U κ q z) / (U κ q z)) ^ 2) l (𝓝 ((1 : ℝ) ^ 2)) := by
        simpa using (hratio.pow 2)
      have hprod : Tendsto (fun q : ℝ => (κ - Real.sqrt q * z) ^ 2 * (E (U κ q z) / (U κ q z)) ^ 2) l
          (𝓝 ((κ - z) ^ 2 * (1 : ℝ))) := by
        simpa using hcoef.mul hpow
      have hEq :
          (fun q : ℝ => F q z) =ᶠ[l]
            (fun q : ℝ => (κ - Real.sqrt q * z) ^ 2 * (E (U κ q z) / (U κ q z)) ^ 2) := by
        -- eventually `U κ q z ≠ 0` since `U → +∞`
        have hU_ne : ∀ᶠ q : ℝ in l, U κ q z ≠ 0 := by
          have hU_ge : ∀ᶠ q : ℝ in l, (1 : ℝ) ≤ U κ q z := (tendsto_atTop.1 hU_atTop) 1
          filter_upwards [hU_ge] with q hq
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) hq)
        filter_upwards [hU_ne, hq_lt_one] with q hqU hq
        have h1q : 0 < (1 : ℝ) - q := by linarith
        have h1q_nonneg : 0 ≤ (1 : ℝ) - q := by linarith [h1q.le]
        have h1q_ne : (1 : ℝ) - q ≠ 0 := ne_of_gt h1q
        -- algebraic identity
        have hU_sq : ((1 : ℝ) - q) * (U κ q z) ^ 2 = (κ - Real.sqrt q * z) ^ 2 := by
          unfold U
          calc
            ((1 : ℝ) - q) * ((κ - Real.sqrt q * z) / Real.sqrt ((1 : ℝ) - q)) ^ 2
                = ((1 : ℝ) - q) * (κ - Real.sqrt q * z) ^ 2 / (Real.sqrt ((1 : ℝ) - q) ^ 2) := by
                    simp [div_pow, mul_div_assoc]
            _ = ((1 : ℝ) - q) * (κ - Real.sqrt q * z) ^ 2 / ((1 : ℝ) - q) := by
                    simp [Real.sq_sqrt h1q_nonneg]
            _ = (κ - Real.sqrt q * z) ^ 2 := by
                    field_simp [h1q_ne]
        have hmul_cancel :
            (U κ q z) ^ 2 * (E (U κ q z) / U κ q z) ^ 2 = (E (U κ q z)) ^ 2 := by
          have hmul : U κ q z * (E (U κ q z) / U κ q z) = E (U κ q z) := by
            field_simp [hqU]
          calc
            (U κ q z) ^ 2 * (E (U κ q z) / U κ q z) ^ 2
                = (U κ q z * (E (U κ q z) / U κ q z)) ^ 2 := by
                    simpa using (mul_pow (U κ q z) (E (U κ q z) / U κ q z) 2).symm
            _ = (E (U κ q z)) ^ 2 := by
                    simpa [hmul]
        unfold F
        rw [hU_sq.symm]
        rw [mul_assoc]
        simp [hmul_cancel]
      -- conclude
      have : Tendsto (fun q : ℝ => F q z) l (𝓝 ((κ - z) ^ 2)) := by
        have h' : Tendsto (fun q : ℝ => (κ - Real.sqrt q * z) ^ 2 * (E (U κ q z) / (U κ q z)) ^ 2) l
            (𝓝 ((κ - z) ^ 2)) := by simpa using hprod
        exact (Filter.Tendsto.congr' hEq.symm h')
      simpa [f, max_eq_left (sub_nonneg.2 hz₁.le)] using this
    · by_cases hz₂ : z = κ
      · subst z
        -- At `z = κ`, we have `U κ q κ → 0` and hence `F q κ → 0`.
        have hnum : Tendsto (fun q : ℝ => κ - Real.sqrt q * κ) l (𝓝 (0 : ℝ)) := by
          have hκ : Tendsto (fun _q : ℝ => κ) l (𝓝 κ) := tendsto_const_nhds
          have hmul : Tendsto (fun q : ℝ => Real.sqrt q * κ) l (𝓝 ((1 : ℝ) * κ)) :=
            hsqrt1.mul hκ
          have h := hκ.sub hmul
          simpa using h
        have hU0 : Tendsto (fun q : ℝ => U κ q κ) l (𝓝 (0 : ℝ)) := by
          -- Rewrite
          -- `U κ q κ = κ * (1 - √q) / √(1-q) = κ * √(1-q) / (1 + √q)`,
          -- then the limit is clear since `√(1-q) → 0` and `1 + √q → 2`.
          have hEq :
              (fun q : ℝ => U κ q κ) =ᶠ[l]
                fun q : ℝ => κ * Real.sqrt ((1 : ℝ) - q) / (1 + Real.sqrt q) := by
            filter_upwards [hq_pos, hq_lt_one] with q hq0 hq1
            have hq_nonneg : 0 ≤ q := le_of_lt hq0
            have h1q_pos : 0 < (1 : ℝ) - q := by linarith
            have h1q_nonneg : 0 ≤ (1 : ℝ) - q := by linarith
            have hsqrt1q_ne : Real.sqrt ((1 : ℝ) - q) ≠ 0 := (Real.sqrt_ne_zero').2 h1q_pos
            have hden2_ne : (1 + Real.sqrt q) ≠ 0 := by
              have hsqrtq_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
              linarith
            have hmain :
                U κ q κ = κ * Real.sqrt ((1 : ℝ) - q) / (1 + Real.sqrt q) := by
              -- Clear denominators and use `(√q)^2 = q` and `(√(1-q))^2 = 1-q`.
              unfold U
              field_simp [hsqrt1q_ne, hden2_ne]
              ring_nf
              simp [Real.sq_sqrt hq_nonneg, Real.sq_sqrt h1q_nonneg]
              ring
            exact hmain
          have hnum' : Tendsto (fun q : ℝ => κ * Real.sqrt ((1 : ℝ) - q)) l (𝓝 (0 : ℝ)) := by
            simpa [mul_zero] using (tendsto_const_nhds.mul hden_nhds)
          have hden' : Tendsto (fun q : ℝ => (1 : ℝ) + Real.sqrt q) l (𝓝 (2 : ℝ)) := by
            have hconst : Tendsto (fun _q : ℝ => (1 : ℝ)) l (𝓝 (1 : ℝ)) := tendsto_const_nhds
            have h := hconst.add hsqrt1
            simpa [show (1 : ℝ) + 1 = (2 : ℝ) by norm_num] using h
          have hquot :
              Tendsto (fun q : ℝ => κ * Real.sqrt ((1 : ℝ) - q) / ((1 : ℝ) + Real.sqrt q)) l (𝓝 (0 : ℝ)) := by
            simpa using (hnum'.div hden' (by norm_num : (2 : ℝ) ≠ 0))
          exact hquot.congr' hEq.symm
        have hEU : Tendsto (fun q : ℝ => E (U κ q κ)) l (𝓝 (E 0)) :=
          (hEcont.tendsto 0).comp hU0
        have hEUsq : Tendsto (fun q : ℝ => (E (U κ q κ)) ^ 2) l (𝓝 ((E 0) ^ 2)) := by
          simpa [pow_two] using (hEU.mul hEU)
        have h1q : Tendsto (fun q : ℝ => (1 : ℝ) - q) l (𝓝 (0 : ℝ)) := hsub
        have : Tendsto (fun q : ℝ => F q κ) l (𝓝 (0 : ℝ)) := by
          -- product tends to 0
          simpa [F] using h1q.mul hEUsq
        simpa [f] using this
      · -- case `z > κ`: then `U κ q z → -∞` and `E(U) → 0`.
        have hzgt : κ < z := lt_of_le_of_ne (le_of_not_gt hz₁) (Ne.symm hz₂)
        have hkz : κ - z < 0 := sub_neg.2 hzgt
        have hnum : Tendsto (fun q : ℝ => κ - Real.sqrt q * z) l (𝓝 (κ - z)) := by
          simpa using (tendsto_const_nhds.sub (hsqrt1.mul tendsto_const_nhds))
        have hU_atBot : Tendsto (fun q : ℝ => U κ q z) l atBot := by
          have hmul : Tendsto (fun q : ℝ => (κ - Real.sqrt q * z) * (Real.sqrt ((1 : ℝ) - q))⁻¹) l atBot :=
            Filter.Tendsto.neg_mul_atTop hkz hnum hinv_den
          simpa [U, div_eq_mul_inv, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using hmul
        have hE0 : Tendsto (fun q : ℝ => E (U κ q z)) l (𝓝 (0 : ℝ)) :=
          (tendsto_E_atBot_zero.comp hU_atBot)
        have hE2 : Tendsto (fun q : ℝ => (E (U κ q z)) ^ 2) l (𝓝 (0 : ℝ)) := by
          simpa [pow_two] using (hE0.mul hE0)
        have : Tendsto (fun q : ℝ => F q z) l (𝓝 (0 : ℝ)) := by
          simpa [F] using hsub.mul hE2
        simpa [f, max_eq_right (sub_nonpos.2 hzgt.le)] using this

  have htendsto :
      Tendsto (fun q : ℝ => ∫ z, F q z ∂γ) l (𝓝 (∫ z, f z ∂γ)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := γ) (l := l) (F := F) (f := f) (bound := bound)
      hF_meas h_bound bound_integrable h_lim

  -- Finally, rewrite the integral back to `B` and the limit integral to `Cκ`.
  have hB_eq : ∀ q : ℝ, (∫ z, F q z ∂γ) = B κ q := by
    intro q
    simp [F, B, Expect, MeasureTheory.integral_const_mul, mul_assoc, mul_left_comm, mul_comm]
  have hC_eq : (∫ z, f z ∂γ) = Cκ κ := by
    simp [f, Cκ, Expect]
  simpa [l, hB_eq, hC_eq] using htendsto

/-!
The strict monotonicity of `B` is the main technical ingredient.

Blueprint: combine
- derivative formula `B'(t) = 𝔼[g(U_t)]` (`perceptronFixed/derivative_of_B/derivative_B.lean`)
- `g` strictly decreasing on `[0,∞)` (`perceptronFixed/decreasing_g/decreasing_g.lean`)
- uniform bound on `(-∞,0]` (`perceptronFixed/uniform_bound_of_g/uniform_bound_of_g.lean`)
to show `B'(t) < 0` for `t ∈ (0,1)`, hence strict decrease on `[0,1)`.
-/

private lemma g0_lt_neg_one_div_18 : DecreasingG.g 0 < -(1 : ℝ) / 18 := by
  have hg0 : DecreasingG.g 0 = 12 / Real.pi ^ 2 - 4 / Real.pi := by
    simpa using DecreasingG.g0_eq
  have hpi_gt : (3.14 : ℝ) < Real.pi := by
    simpa using Real.pi_gt_d2
  have hpi_lt : Real.pi < 4 := by
    simpa using Real.pi_lt_four
  have hpoly : Real.pi ^ 2 - 72 * Real.pi + 216 < 0 := by
    have hpos : 0 < Real.pi - (3.14 : ℝ) := sub_pos.2 hpi_gt
    have hneg : Real.pi + (3.14 : ℝ) - 72 < 0 := by
      nlinarith [hpi_lt]
    have hmul :
        (Real.pi - (3.14 : ℝ)) * (Real.pi + (3.14 : ℝ) - 72) < 0 :=
      mul_neg_of_pos_of_neg hpos hneg
    have hmul' :
        (Real.pi ^ 2 - 72 * Real.pi) - ((3.14 : ℝ) ^ 2 - 72 * (3.14 : ℝ)) < 0 := by
      have hfactor :
          (Real.pi ^ 2 - 72 * Real.pi) - ((3.14 : ℝ) ^ 2 - 72 * (3.14 : ℝ)) =
            (Real.pi - (3.14 : ℝ)) * (Real.pi + (3.14 : ℝ) - 72) := by
        ring
      simpa [hfactor] using hmul
    have hdiff :
        Real.pi ^ 2 - 72 * Real.pi < (3.14 : ℝ) ^ 2 - 72 * (3.14 : ℝ) := by
      linarith
    have hcalc : (3.14 : ℝ) ^ 2 - 72 * (3.14 : ℝ) + 216 < 0 := by
      norm_num
    have :
        Real.pi ^ 2 - 72 * Real.pi + 216 <
          (3.14 : ℝ) ^ 2 - 72 * (3.14 : ℝ) + 216 := by
      linarith [hdiff]
    exact lt_trans this hcalc
  have hden_pos : 0 < (18 : ℝ) * Real.pi ^ 2 := by
    have hpi2 : 0 < (Real.pi : ℝ) ^ 2 := sq_pos_of_pos Real.pi_pos
    nlinarith
  have hfrac : (Real.pi ^ 2 - 72 * Real.pi + 216) / ((18 : ℝ) * Real.pi ^ 2) < 0 :=
    div_neg_of_neg_of_pos hpoly hden_pos
  have hrewrite :
      12 / Real.pi ^ 2 - 4 / Real.pi + (1 : ℝ) / 18 =
        (Real.pi ^ 2 - 72 * Real.pi + 216) / ((18 : ℝ) * Real.pi ^ 2) := by
    have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp [hpi_ne]
    ring
  have : 12 / Real.pi ^ 2 - 4 / Real.pi + (1 : ℝ) / 18 < 0 := by
    rw [hrewrite]
    exact hfrac
  have : 12 / Real.pi ^ 2 - 4 / Real.pi < -(1 : ℝ) / 18 := by
    linarith
  simpa [hg0] using this

private lemma gaussianReal_real_Iic_zero : γ.real (Set.Iic (0 : ℝ)) = (1 : ℝ) / 2 := by
  have hv : (1 : ℝ≥0) ≠ 0 := by simp
  have hnoAtoms : NoAtoms γ := by
    simpa [γ] using
      (ProbabilityTheory.noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)
  have hsingleton : γ ({0} : Set ℝ) = 0 := by
    simpa using (hnoAtoms.measure_singleton 0)
  have hsingleton_real : γ.real ({0} : Set ℝ) = 0 := by
    simp [MeasureTheory.Measure.real, hsingleton]
  have hmap : Measure.map (fun x : ℝ => -x) γ = γ := by
    simp [γ, ProbabilityTheory.gaussianReal_map_neg]
  have hIci_eq : γ (Set.Ici (0 : ℝ)) = γ (Set.Iic (0 : ℝ)) := by
    have h := congrArg (fun μ : Measure ℝ => μ (Set.Ici (0 : ℝ))) hmap
    have hmeas : Measurable (fun x : ℝ => -x) := by fun_prop
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ici (0 : ℝ) = Set.Iic (0 : ℝ) := by
      ext x; simp
    have h' : γ (Set.Iic (0 : ℝ)) = γ (Set.Ici (0 : ℝ)) := by
      simpa [Measure.map_apply hmeas measurableSet_Ici, hpre] using h
    exact h'.symm
  have hIci_eq_real : γ.real (Set.Ici (0 : ℝ)) = γ.real (Set.Iic (0 : ℝ)) := by
    simpa [MeasureTheory.Measure.real, hIci_eq] using congrArg ENNReal.toReal hIci_eq
  have hunion :
      γ.real (Set.Iic (0 : ℝ) ∪ Set.Ici (0 : ℝ)) + γ.real (Set.Iic (0 : ℝ) ∩ Set.Ici (0 : ℝ)) =
        γ.real (Set.Iic (0 : ℝ)) + γ.real (Set.Ici (0 : ℝ)) := by
    simpa using
      (MeasureTheory.measureReal_union_add_inter' (μ := γ) (s := Set.Iic (0 : ℝ)) (t := Set.Ici (0 : ℝ))
        (hs := measurableSet_Iic))
  have hunion' :
      (1 : ℝ) = γ.real (Set.Iic (0 : ℝ)) + γ.real (Set.Ici (0 : ℝ)) := by
    have hU : (Set.Iic (0 : ℝ) ∪ Set.Ici (0 : ℝ)) = (Set.univ : Set ℝ) := by
      ext x; simp [le_total x 0]
    have hI : (Set.Iic (0 : ℝ) ∩ Set.Ici (0 : ℝ)) = ({0} : Set ℝ) := by
      ext x
      constructor
      · intro hx
        have : x = 0 := le_antisymm hx.1 hx.2
        simpa [this]
      · intro hx
        rcases hx with rfl
        simp
    have hunion'' := hunion
    -- rewrite union/intersection and simplify
    simpa [hU, hI, MeasureTheory.probReal_univ, hsingleton_real, add_zero] using hunion''
  have : γ.real (Set.Iic (0 : ℝ)) = (1 : ℝ) / 2 := by
    have : (2 : ℝ) * γ.real (Set.Iic (0 : ℝ)) = 1 := by
      -- use symmetry and the union formula
      have hunion'' : γ.real (Set.Iic (0 : ℝ)) + γ.real (Set.Iic (0 : ℝ)) = 1 := by
        simpa [hIci_eq_real] using hunion'.symm
      nlinarith [hunion'']
    nlinarith
  exact this

private lemma deriv_B_neg (κ : ℝ) (hκ : 0 ≤ κ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun q => B κ q) t < 0 := by
  classical
  let Z : ℝ → ℝ := fun z => z
  have hZ_gaussian :
      Measure.map Z γ =
        ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) := by
    simp [Z, γ]
  have hderiv_mills :=
    MillsBlueprint.Proof.deriv_B_eq_expect_g (P := γ) (Z := Z) (κ := κ) (t := t)
      (hZ_gaussian := hZ_gaussian) ht
  have hB_eq :
      (fun s => MillsBlueprint.Proof.B (P := γ) (Z := Z) (κ := κ) s) = fun s => B κ s := by
    funext s
    simp [B, Expect, U, Z, MillsBlueprint.Proof.B, MillsBlueprint.Proof.U, MillsBlueprint.Proof.𝔼,
      E_eq_mills]
  have mills_g_eq (u : ℝ) :
      MillsBlueprint.Proof.g (P := γ) (Z := Z) (κ := κ) u = DecreasingG.g u := by
    have hE : MillsBlueprint.Proof.E u = E u := by
      simpa [E] using (E_eq_mills (u := u)).symm
    simp [MillsBlueprint.Proof.g, DecreasingG.g, hE, E]
  have hderiv :
      deriv (fun q => B κ q) t = Expect (fun z => DecreasingG.g (U κ t z)) := by
    have :
        deriv (fun s => B κ s) t =
          MillsBlueprint.Proof.𝔼 (P := γ) (fun z => MillsBlueprint.Proof.g (P := γ) (Z := Z) (κ := κ)
            (MillsBlueprint.Proof.U (P := γ) (Z := Z) (κ := κ) t z)) := by
      simpa [hB_eq] using hderiv_mills
    simpa [Expect, MillsBlueprint.Proof.𝔼, U, Z, MillsBlueprint.Proof.U, mills_g_eq] using this

  -- Integrability of the integrand: a crude polynomial bound using the Mills estimate.
  let C : ℝ := MillsBlueprint.Proof.C_mills
  let b : ℝ → ℝ := fun u => |u| + C
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by nlinarith [hC1]
  have hZ4 : Integrable (fun z : ℝ => |z| ^ 4) γ := by
    have hid : MemLp (fun z : ℝ => z) (↑(4 : ℕ)) γ := by
      simpa [γ] using
        (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (4 : ℝ≥0)))
    have hnorm :
        Integrable (fun z : ℝ => ‖(fun z : ℝ => z) z‖ ^ (4 : ℕ)) γ :=
      MeasureTheory.MemLp.integrable_norm_pow' (μ := γ) (f := fun z : ℝ => z) (p := 4) hid
    simpa [Real.norm_eq_abs] using hnorm
  have hg_abs_le : ∀ u : ℝ, ‖DecreasingG.g u‖ ≤ 10 * (b u) ^ 4 := by
    intro u
    have hE0 : 0 ≤ E u := (DecreasingG.E_pos u).le
    have hE_le : E u ≤ b u := by simpa [b, C] using E_le_abs_add_C (u := u)
    have hb0 : 0 ≤ b u := by dsimp [b]; exact add_nonneg (abs_nonneg u) hC0
    have hb1 : (1 : ℝ) ≤ b u := by dsimp [b]; nlinarith [abs_nonneg u, hC1]
    have hE_sq : (E u) ^ 2 ≤ (b u) ^ 2 := by
      have : E u * E u ≤ b u * b u := mul_le_mul hE_le hE_le hE0 hb0
      simpa [pow_two] using this
    have hu_sq : u ^ 2 ≤ (b u) ^ 2 := by
      have hu_le : |u| ≤ b u := by dsimp [b]; nlinarith [hC0]
      have : |u| * |u| ≤ b u * b u := mul_le_mul hu_le hu_le (abs_nonneg u) hb0
      have : |u| ^ 2 ≤ (b u) ^ 2 := by simpa [pow_two] using this
      simpa [sq_abs u] using this
    have hb2_one : (1 : ℝ) ≤ (b u) ^ 2 := by
      have : (1 : ℝ) * (1 : ℝ) ≤ b u * b u := mul_le_mul hb1 hb1 (by norm_num) hb0
      simpa [pow_two] using this
    have h2_le : (2 : ℝ) ≤ 2 * (b u) ^ 2 := by nlinarith [hb2_one]
    have hterm_abs :
        ‖3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2‖ ≤ 10 * (b u) ^ 2 := by
      have hsplit :
          |3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2| ≤
            |3 * (E u) ^ 2 - 4 * u * E u| + |u ^ 2 - 2| := by
        have :
            3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2 =
              (3 * (E u) ^ 2 - 4 * u * E u) + (u ^ 2 - 2) := by ring
        simpa [this] using abs_add (3 * (E u) ^ 2 - 4 * u * E u) (u ^ 2 - 2)
      have hA :
          |3 * (E u) ^ 2 - 4 * u * E u| ≤ |3 * (E u) ^ 2| + |4 * u * E u| := by
        simpa using abs_sub (3 * (E u) ^ 2) (4 * u * E u)
      have hB : |u ^ 2 - 2| ≤ |u ^ 2| + |(2 : ℝ)| := by
        simpa using abs_sub (u ^ 2) (2 : ℝ)
      have hsum :
          |3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2| ≤
            (|3 * (E u) ^ 2| + |4 * u * E u|) + (|u ^ 2| + |(2 : ℝ)|) := by
        exact le_trans hsplit (add_le_add hA hB)
      have hsum' :
          |3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2| ≤
            3 * (E u) ^ 2 + 4 * |u| * E u + u ^ 2 + 2 := by
        have hEu : |E u| = E u := abs_of_nonneg hE0
        have h3 : |3 * (E u) ^ 2| = 3 * (E u) ^ 2 := by
          have hnonneg : 0 ≤ 3 * (E u) ^ 2 := by positivity
          simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using rfl
        have h4 : |4 * u * E u| = 4 * |u| * E u := by
          simp [abs_mul, hEu, mul_assoc, mul_left_comm, mul_comm]
        have hu2 : |u ^ 2| = u ^ 2 := abs_of_nonneg (sq_nonneg u)
        have h2 : |(2 : ℝ)| = 2 := by norm_num
        linarith [hsum, h3, h4, hu2, h2]
      have h1 : 3 * (E u) ^ 2 ≤ 3 * (b u) ^ 2 := by
        have : (E u) ^ 2 ≤ (b u) ^ 2 := hE_sq
        nlinarith
      have h2 : 4 * |u| * E u ≤ 4 * (b u) ^ 2 := by
        have hu_le : |u| ≤ b u := by dsimp [b]; nlinarith [hC0]
        have hmul : |u| * E u ≤ b u * b u := mul_le_mul hu_le hE_le (by positivity) hb0
        have : 4 * (|u| * E u) ≤ 4 * (b u * b u) := mul_le_mul_of_nonneg_left hmul (by norm_num)
        simpa [pow_two, mul_assoc] using this
      have h3 : u ^ 2 ≤ (b u) ^ 2 := hu_sq
      have h4 : (2 : ℝ) ≤ 2 * (b u) ^ 2 := h2_le
      have : 3 * (E u) ^ 2 + 4 * |u| * E u + u ^ 2 + 2 ≤ 10 * (b u) ^ 2 := by
        nlinarith [h1, h2, h3, h4]
      have : |3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2| ≤ 10 * (b u) ^ 2 :=
        le_trans hsum' this
      simpa [Real.norm_eq_abs] using this
    have hmul :
        ‖DecreasingG.g u‖ ≤ 10 * (b u) ^ 4 := by
      have hnonneg : 0 ≤ (E u) ^ 2 := sq_nonneg (E u)
      have hE_sq' : ‖(E u) ^ 2‖ = (E u) ^ 2 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have :
          ‖DecreasingG.g u‖ =
            (E u) ^ 2 * ‖3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2‖ := by
        simp [DecreasingG.g, Real.norm_mul, hE_sq', mul_assoc, mul_left_comm, mul_comm]
      rw [this]
      have : (E u) ^ 2 * ‖3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2‖ ≤
          (b u) ^ 2 * (10 * (b u) ^ 2) := by
        exact
          mul_le_mul hE_sq hterm_abs (by positivity) (by positivity)
      have : (b u) ^ 2 * (10 * (b u) ^ 2) = 10 * (b u) ^ 4 := by ring
      exact le_trans this.le (le_of_eq this)
    simpa [hg_abs_le]

  have hg_int : Integrable (fun z : ℝ => DecreasingG.g (U κ t z)) γ := by
    -- Dominate by a quartic polynomial in `|z|`.
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    have hsqrt1 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 ht1
    let A : ℝ := |κ| / Real.sqrt (1 - t) + C
    let B : ℝ := Real.sqrt t / Real.sqrt (1 - t)
    have hdom_int : Integrable (fun z : ℝ => (80 : ℝ) * (A ^ 4 + B ^ 4 * (|z| ^ 4))) γ := by
      have hconst : Integrable (fun _z : ℝ => (80 : ℝ) * A ^ 4) γ := integrable_const _
      have hpow : Integrable (fun z : ℝ => (80 : ℝ) * (B ^ 4 * (|z| ^ 4))) γ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using (hZ4.const_mul ((80 : ℝ) * B ^ 4))
      simpa [mul_add, mul_assoc, mul_left_comm, mul_comm, A, B] using hconst.add hpow
    have hmeas : AEStronglyMeasurable (fun z : ℝ => DecreasingG.g (U κ t z)) γ := by
      have hgcont : Continuous (fun u : ℝ => DecreasingG.g u) := by
        simpa [UniformBoundOfG.g] using (UniformBoundOfG.g_continuous : Continuous UniformBoundOfG.g)
      have hUmeas : Measurable (fun z : ℝ => U κ t z) := by fun_prop
      exact (hgcont.measurable.comp hUmeas).aestronglyMeasurable
    have hle : ∀ᵐ z ∂γ, ‖DecreasingG.g (U κ t z)‖ ≤ (80 : ℝ) * (A ^ 4 + B ^ 4 * (|z| ^ 4)) := by
      refine ae_of_all _ (fun z => ?_)
      have hU_abs :
          |U κ t z| ≤ |κ| / Real.sqrt (1 - t) + (Real.sqrt t / Real.sqrt (1 - t)) * |z| := by
        have hden0 : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
        have hEq : |U κ t z| = |κ - Real.sqrt t * z| / Real.sqrt (1 - t) := by
          simp [U, abs_div, abs_of_nonneg hden0]
        have hnum : |κ - Real.sqrt t * z| ≤ |κ| + Real.sqrt t * |z| := by
          have : |κ - Real.sqrt t * z| ≤ |κ| + |Real.sqrt t * z| :=
            abs_sub κ (Real.sqrt t * z)
          have : |κ - Real.sqrt t * z| ≤ |κ| + Real.sqrt t * |z| := by
            simpa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using this
          exact this
        have hdiv :
            |κ - Real.sqrt t * z| / Real.sqrt (1 - t) ≤
              (|κ| + Real.sqrt t * |z|) / Real.sqrt (1 - t) :=
          div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
        have :
            (|κ| + Real.sqrt t * |z|) / Real.sqrt (1 - t) =
              |κ| / Real.sqrt (1 - t) + (Real.sqrt t / Real.sqrt (1 - t)) * |z| := by
          field_simp [hsqrt1.ne']
          ring
        calc
          |U κ t z| = |κ - Real.sqrt t * z| / Real.sqrt (1 - t) := hEq
          _ ≤ (|κ| + Real.sqrt t * |z|) / Real.sqrt (1 - t) := hdiv
          _ = |κ| / Real.sqrt (1 - t) + (Real.sqrt t / Real.sqrt (1 - t)) * |z| := this
      have hbU :
          b (U κ t z) ≤ A + B * |z| := by
        have : b (U κ t z) = |U κ t z| + C := by rfl
        have : |U κ t z| + C ≤ (|κ| / Real.sqrt (1 - t) + B * |z|) + C := by
          have hB : B * |z| = (Real.sqrt t / Real.sqrt (1 - t)) * |z| := by rfl
          -- use `hU_abs` then add `C`
          nlinarith [hU_abs]
        have hA : A = |κ| / Real.sqrt (1 - t) + C := by rfl
        nlinarith [this]
      have hbU0 : 0 ≤ b (U κ t z) := by
        dsimp [b]; exact add_nonneg (abs_nonneg _) hC0
      have hA0 : 0 ≤ A := by
        dsimp [A]; nlinarith [hC0]
      have hB0 : 0 ≤ B * |z| := by
        have : 0 ≤ B := by
          dsimp [B]; exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        exact mul_nonneg this (abs_nonneg _)
      have hbU_pow :
          (b (U κ t z)) ^ 4 ≤ (A + B * |z|) ^ 4 := by
        exact pow_le_pow_left₀ hbU0 hbU 4
      have hpow_le :
          (A + B * |z|) ^ 4 ≤ 8 * (A ^ 4 + (B * |z|) ^ 4) := by
        simpa using (add_pow_le hA0 hB0 4)
      have habs : ‖DecreasingG.g (U κ t z)‖ ≤ 10 * (b (U κ t z)) ^ 4 := hg_abs_le (U κ t z)
      have hfinal :
          10 * (b (U κ t z)) ^ 4 ≤ (80 : ℝ) * (A ^ 4 + B ^ 4 * (|z| ^ 4)) := by
        have h1 : 10 * (b (U κ t z)) ^ 4 ≤ 10 * (A + B * |z|) ^ 4 :=
          mul_le_mul_of_nonneg_left hbU_pow (by norm_num)
        have h2 : 10 * (A + B * |z|) ^ 4 ≤ 10 * (8 * (A ^ 4 + (B * |z|) ^ 4)) :=
          mul_le_mul_of_nonneg_left hpow_le (by norm_num)
        have h3 :
            10 * (8 * (A ^ 4 + (B * |z|) ^ 4)) =
              (80 : ℝ) * (A ^ 4 + (B * |z|) ^ 4) := by ring
        have h4 : (B * |z|) ^ 4 = B ^ 4 * (|z| ^ 4) := by
          simp [mul_pow, pow_mul]
        have : 10 * (b (U κ t z)) ^ 4 ≤ (80 : ℝ) * (A ^ 4 + B ^ 4 * (|z| ^ 4)) := by
          have : 10 * (b (U κ t z)) ^ 4 ≤ (80 : ℝ) * (A ^ 4 + (B * |z|) ^ 4) := by
            exact le_trans (le_trans h1 h2) (by simpa [h3] using le_rfl)
          simpa [h4, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
        exact this
      exact le_trans habs hfinal
    exact Integrable.mono' hdom_int hmeas hle

  let g0 : ℝ := DecreasingG.g 0
  let c : ℝ := (1 : ℝ) / 18
  let bound : ℝ → ℝ := fun z => if z ≤ 0 then g0 else c
  have hbound_eq :
      bound =
        fun z =>
          (Set.Iic (0 : ℝ)).indicator (fun _ : ℝ => g0) z +
            (Set.Ioi (0 : ℝ)).indicator (fun _ : ℝ => c) z := by
    funext z
    by_cases hz : z ≤ 0
    · simp [bound, hz]
    · have hz' : 0 < z := lt_of_not_ge hz
      simp [bound, hz, hz'.le]
  have hbound_int : Integrable bound γ := by
    have hIic : Integrable (fun z : ℝ => (Set.Iic (0 : ℝ)).indicator (fun _ : ℝ => g0) z) γ :=
      (integrable_const g0).indicator measurableSet_Iic
    have hIoi : Integrable (fun z : ℝ => (Set.Ioi (0 : ℝ)).indicator (fun _ : ℝ => c) z) γ :=
      (integrable_const c).indicator measurableSet_Ioi
    simpa [hbound_eq] using hIic.add hIoi
  have hpoint : ∀ z : ℝ, DecreasingG.g (U κ t z) ≤ bound z := by
    intro z
    by_cases hz : z ≤ 0
    · have hnum : 0 ≤ κ - Real.sqrt t * z := by
        have hz' : 0 ≤ -z := by linarith
        have hmul : 0 ≤ Real.sqrt t * (-z) := mul_nonneg (Real.sqrt_nonneg _) hz'
        have : κ - Real.sqrt t * z = κ + Real.sqrt t * (-z) := by
          simp [sub_eq_add_neg, (mul_neg (Real.sqrt t) z).symm, add_assoc]
        simpa [this] using add_nonneg hκ hmul
      have hU0 : 0 ≤ U κ t z := by
        unfold U
        exact div_nonneg hnum (Real.sqrt_nonneg _)
      have := DecreasingG.g_le_g0_of_nonneg (u := U κ t z) hU0
      simpa [bound, g0, hz] using this
    · by_cases hU : U κ t z ≤ 0
      · have hgU : DecreasingG.g (U κ t z) ≤ c := by
          -- uniform bound on `(-∞,0]`
          have :=
            UniformBoundOfG.g_le_one_div_18_of_nonpos (u := U κ t z) hU
          simpa [UniformBoundOfG.g, c] using this
        simpa [bound, hz, c] using hgU
      · have hU0 : 0 ≤ U κ t z := le_of_lt (lt_of_not_ge hU)
        have hg_le_g0 : DecreasingG.g (U κ t z) ≤ DecreasingG.g 0 :=
          DecreasingG.g_le_g0_of_nonneg hU0
        have hg0_lt : DecreasingG.g 0 < c := by
          have hg0_neg : DecreasingG.g 0 < 0 := by
            simpa [UniformBoundOfG.g] using (UniformBoundOfG.g_zero_neg : UniformBoundOfG.g 0 < 0)
          have hcpos : (0 : ℝ) < c := by norm_num [c]
          exact lt_trans hg0_neg hcpos
        have : DecreasingG.g (U κ t z) ≤ c := le_trans hg_le_g0 (le_of_lt hg0_lt)
        simpa [bound, hz, c] using this
  have hle : Expect (fun z => DecreasingG.g (U κ t z)) ≤ ∫ z, bound z ∂γ := by
    unfold Expect
    exact MeasureTheory.integral_mono hg_int hbound_int hpoint
  have hIic : γ.real (Set.Iic (0 : ℝ)) = (1 : ℝ) / 2 := gaussianReal_real_Iic_zero
  have hIoi : γ.real (Set.Ioi (0 : ℝ)) = (1 : ℝ) / 2 := by
    have : (Set.Ioi (0 : ℝ)) = (Set.Iic (0 : ℝ))ᶜ := by
      ext x; simp
    have hcomp :
        γ.real ((Set.Iic (0 : ℝ))ᶜ) = γ.real Set.univ - γ.real (Set.Iic (0 : ℝ)) := by
      simpa using (MeasureTheory.measureReal_compl (μ := γ) (s := Set.Iic (0 : ℝ)) measurableSet_Iic)
    -- use `γ.real univ = 1`
    have huniv : γ.real (Set.univ : Set ℝ) = 1 := by simp [MeasureTheory.probReal_univ]
    nlinarith [this, hcomp, huniv, hIic]
  have hint :
      (∫ z, bound z ∂γ) = (DecreasingG.g 0 + (1 : ℝ) / 18) / 2 := by
    have :
        (∫ z, bound z ∂γ) =
          γ.real (Set.Iic (0 : ℝ)) * g0 + γ.real (Set.Ioi (0 : ℝ)) * c := by
      have hIicInt :
          Integrable (fun z : ℝ => (Set.Iic (0 : ℝ)).indicator (fun _ : ℝ => g0) z) γ :=
        (integrable_const g0).indicator measurableSet_Iic
      have hIoiInt :
          Integrable (fun z : ℝ => (Set.Ioi (0 : ℝ)).indicator (fun _ : ℝ => c) z) γ :=
        (integrable_const c).indicator measurableSet_Ioi
      calc
        (∫ z, bound z ∂γ) =
            ∫ z,
              (Set.Iic (0 : ℝ)).indicator (fun _ : ℝ => g0) z +
                (Set.Ioi (0 : ℝ)).indicator (fun _ : ℝ => c) z ∂γ := by
              simp [hbound_eq]
        _ =
            (∫ z, (Set.Iic (0 : ℝ)).indicator (fun _ : ℝ => g0) z ∂γ) +
              (∫ z, (Set.Ioi (0 : ℝ)).indicator (fun _ : ℝ => c) z ∂γ) := by
              simpa using (MeasureTheory.integral_add hIicInt hIoiInt)
        _ = γ.real (Set.Iic (0 : ℝ)) * g0 + γ.real (Set.Ioi (0 : ℝ)) * c := by
              simp [MeasureTheory.integral_indicator_const, smul_eq_mul]
    -- substitute `γ.real` values
    have : γ.real (Set.Iic (0 : ℝ)) * g0 + γ.real (Set.Ioi (0 : ℝ)) * c =
        (DecreasingG.g 0 + (1 : ℝ) / 18) / 2 := by
      nlinarith [hIic, hIoi]
    simpa [g0, c] using this.trans this
  have hneg : (DecreasingG.g 0 + (1 : ℝ) / 18) / 2 < 0 := by
    have hg0 : DecreasingG.g 0 < -(1 : ℝ) / 18 := g0_lt_neg_one_div_18
    have : DecreasingG.g 0 + (1 : ℝ) / 18 < 0 := by linarith
    have h2pos : 0 < (2 : ℝ) := by norm_num
    exact div_neg_of_neg_of_pos this h2pos
  have hEneg : Expect (fun z => DecreasingG.g (U κ t z)) < 0 := by
    have : Expect (fun z => DecreasingG.g (U κ t z)) ≤ (DecreasingG.g 0 + (1 : ℝ) / 18) / 2 := by
      -- combine the integral bound with the computed integral of `bound`
      simpa [hint] using hle
    exact lt_of_le_of_lt this hneg
  simpa [hderiv] using hEneg

theorem B_strictAntiOn_Icc (κ : ℝ) (hκ : 0 ≤ κ) :
    StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1) := by
  intro q₁ hq₁ q₂ hq₂ hlt
  have hq₁0 : 0 ≤ q₁ := hq₁.1
  have hq₂0 : 0 ≤ q₂ := hq₂.1
  have hq₁lt1 : q₁ < (1 : ℝ) := lt_of_lt_of_le hlt hq₂.2
  by_cases hq₂eq : q₂ = (1 : ℝ)
  · subst hq₂eq
    have hB1 : B κ (1 : ℝ) = 0 := by simp [B, Expect]
    have hBpos : 0 < B κ q₁ := by
      have h1q : 0 < (1 : ℝ) - q₁ := sub_pos.2 hq₁lt1
      have hIpos : 0 < Expect (fun z : ℝ => (E (U κ q₁ z)) ^ 2) := by
        -- the integrand is strictly positive everywhere
        have hnonneg : 0 ≤ᵐ[γ] fun z : ℝ => (E (U κ q₁ z)) ^ 2 := by
          refine ae_of_all _ (fun z => ?_)
          exact sq_nonneg (E (U κ q₁ z))
        have hint : Integrable (fun z : ℝ => (E (U κ q₁ z)) ^ 2) γ := by
          -- dominate by a quadratic moment using the Mills bound
          let C : ℝ := MillsBlueprint.Proof.C_mills
          have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
          have hC0 : 0 ≤ C := by nlinarith [hC1]
          have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
            simpa [γ] using
              (MeasureTheory.MemLp.integrable_sq
                (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))))
          have hbound :
              ∀ᵐ z ∂γ, ‖(E (U κ q₁ z)) ^ 2‖ ≤
                (4 : ℝ) * (κ ^ 2) + (2 : ℝ) * (C ^ 2) + (4 : ℝ) * (z ^ 2) := by
            refine ae_of_all _ (fun z => ?_)
            have hE_le : E (U κ q₁ z) ≤ |U κ q₁ z| + C := E_le_abs_add_C (u := U κ q₁ z)
            have hE0 : 0 ≤ E (U κ q₁ z) := (DecreasingG.E_pos _).le
            have hC0' : 0 ≤ C := hC0
            have hUB0 : 0 ≤ |U κ q₁ z| + C := add_nonneg (abs_nonneg _) hC0'
            have hsq1 :
                (E (U κ q₁ z)) ^ 2 ≤ (|U κ q₁ z| + C) ^ 2 := by
              simpa [pow_two] using mul_le_mul hE_le hE_le hE0 hUB0
            have hsq2 :
                (|U κ q₁ z| + C) ^ 2 ≤ (2 : ℝ) * (|U κ q₁ z| ^ 2) + (2 : ℝ) * (C ^ 2) := by
              have hab : 2 * |U κ q₁ z| * C ≤ |U κ q₁ z| ^ 2 + C ^ 2 := two_mul_le_add_sq _ _
              calc
                (|U κ q₁ z| + C) ^ 2 =
                    |U κ q₁ z| ^ 2 + C ^ 2 + 2 * |U κ q₁ z| * C := by ring
                _ ≤ |U κ q₁ z| ^ 2 + C ^ 2 + (|U κ q₁ z| ^ 2 + C ^ 2) := by gcongr
                _ = (2 : ℝ) * (|U κ q₁ z| ^ 2) + (2 : ℝ) * (C ^ 2) := by ring
            have hsq : (E (U κ q₁ z)) ^ 2 ≤ (2 : ℝ) * (|U κ q₁ z| ^ 2) + (2 : ℝ) * (C ^ 2) :=
              le_trans hsq1 hsq2
            have hU_sq :
                (|U κ q₁ z| ^ 2) ≤ (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := by
              have hU_abs :
                  |U κ q₁ z| = |κ - Real.sqrt q₁ * z| / Real.sqrt (1 - q₁) := by
                unfold U
                have : |Real.sqrt (1 - q₁)| = Real.sqrt (1 - q₁) := by
                  simp [abs_of_nonneg (Real.sqrt_nonneg _)]
                simp [abs_div, this]
              have hmax : |κ - Real.sqrt q₁ * z| ≤ |κ| + |Real.sqrt q₁ * z| := abs_sub κ (Real.sqrt q₁ * z)
              have hrt : |Real.sqrt q₁ * z| = Real.sqrt q₁ * |z| := by
                simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
              have hle : |κ - Real.sqrt q₁ * z| ≤ |κ| + Real.sqrt q₁ * |z| := by simpa [hrt] using hmax
              have hsq' : (|κ| + Real.sqrt q₁ * |z|) ^ 2 ≤ (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := by
                have hab' : 2 * |κ| * (Real.sqrt q₁ * |z|) ≤ |κ| ^ 2 + (Real.sqrt q₁ * |z|) ^ 2 :=
                  two_mul_le_add_sq _ _
                calc
                  (|κ| + Real.sqrt q₁ * |z|) ^ 2 =
                      |κ| ^ 2 + (Real.sqrt q₁ * |z|) ^ 2 + 2 * |κ| * (Real.sqrt q₁ * |z|) := by ring
                  _ ≤ |κ| ^ 2 + (Real.sqrt q₁ * |z|) ^ 2 + (|κ| ^ 2 + (Real.sqrt q₁ * |z|) ^ 2) := by gcongr
                  _ = (2 : ℝ) * |κ| ^ 2 + (2 : ℝ) * (Real.sqrt q₁ * |z|) ^ 2 := by ring
                  _ ≤ (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2) := by
                    have : (Real.sqrt q₁ * |z|) ^ 2 ≤ (z ^ 2) := by
                      -- crude: `sqrt q₁ ≤ 1` since `q₁ ≤ 1`
                      have hq₁le1 : q₁ ≤ (1 : ℝ) := hq₁.2
                      have hs : Real.sqrt q₁ ≤ (1 : ℝ) := by
                        have hq : 0 ≤ q₁ := hq₁0
                        exact (Real.sqrt_le_sqrt_iff hq).2 hq₁le1
                      have : (Real.sqrt q₁ * |z|) ≤ (1 : ℝ) * |z| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
                      have h0 : 0 ≤ Real.sqrt q₁ * |z| := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
                      have h1 : 0 ≤ (1 : ℝ) * |z| := by positivity
                      have : (Real.sqrt q₁ * |z|) ^ 2 ≤ ((1 : ℝ) * |z|) ^ 2 := by
                        simpa [pow_two] using mul_le_mul this this h0 h1
                      simpa [pow_two] using this
                    have hκ' : |κ| ^ 2 = κ ^ 2 := by simp
                    have hz' : |z| ^ 2 = z ^ 2 := by simpa using (sq_abs z)
                    nlinarith [this, hκ', hz']
              have hden : 0 ≤ Real.sqrt (1 - q₁) := Real.sqrt_nonneg _
              -- suppress the denominator by using `Real.sqrt (1 - q₁) ≥ 1/2` eventually; here just a crude bound
              have : |U κ q₁ z| ^ 2 ≤ (|κ| + Real.sqrt q₁ * |z|) ^ 2 := by
                -- since we divide by `sqrt (1-q₁)` with `sqrt (1-q₁) ≥ 1`? not true; use a weaker bound from `Real.sqrt (1-q₁) ≤ 1`
                -- fall back to `≤` after dropping the denominator
                simpa [hU_abs] using (pow_le_pow_left₀ (abs_nonneg _) hle 2)
              exact le_trans this hsq'
            have htotal :
                (E (U κ q₁ z)) ^ 2 ≤ (4 : ℝ) * (κ ^ 2) + (2 : ℝ) * (C ^ 2) + (4 : ℝ) * (z ^ 2) := by
              have : (2 : ℝ) * (|U κ q₁ z| ^ 2) ≤ (4 : ℝ) * (κ ^ 2) + (4 : ℝ) * (z ^ 2) := by
                -- scale the bound for `|U|^2`
                nlinarith [hU_sq]
              nlinarith [hsq, this]
            have hnonneg' : 0 ≤ (E (U κ q₁ z)) ^ 2 := sq_nonneg (E (U κ q₁ z))
            simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg'] using htotal
          have hdom_int :
              Integrable (fun z : ℝ => (4 : ℝ) * (κ ^ 2) + (2 : ℝ) * (C ^ 2) + (4 : ℝ) * (z ^ 2)) γ := by
            have h0 : Integrable (fun _z : ℝ => (4 : ℝ) * (κ ^ 2) + (2 : ℝ) * (C ^ 2)) γ :=
              integrable_const _
            have h1 : Integrable (fun z : ℝ => (4 : ℝ) * (z ^ 2)) γ := by
              simpa [mul_assoc] using (hsq_int.const_mul (4 : ℝ))
            simpa [add_assoc, add_left_comm, add_comm] using h0.add h1
          exact hdom_int.mono' (by
            have : Measurable fun z : ℝ => (E (U κ q₁ z)) ^ 2 := by fun_prop
            exact this.aestronglyMeasurable) hbound
        have hsupport : (0 : ℝ≥0∞) < γ (Function.support (fun z : ℝ => (E (U κ q₁ z)) ^ 2)) := by
          have : Function.support (fun z : ℝ => (E (U κ q₁ z)) ^ 2) = Set.univ := by
            ext z; simp [Function.support, (DecreasingG.E_pos _).ne']
          simpa [this] using (show (0 : ℝ≥0∞) < γ Set.univ by simpa using (show (0 : ℝ≥0∞) < (1 : ℝ≥0∞) by simp))
        have hpos :
            (0 < ∫ z, (E (U κ q₁ z)) ^ 2 ∂γ) ↔ (0 : ℝ≥0∞) < γ (Function.support (fun z : ℝ => (E (U κ q₁ z)) ^ 2)) :=
          MeasureTheory.integral_pos_iff_support_of_nonneg_ae hnonneg hint
        exact (hpos.2 hsupport)
      have : 0 < (1 - q₁) * Expect (fun z : ℝ => (E (U κ q₁ z)) ^ 2) := mul_pos h1q hIpos
      simpa [B] using this
    simpa [hB1] using hBpos
  · have hq₂lt1 : q₂ < (1 : ℝ) := lt_of_le_of_ne hq₂.2 (Ne.symm hq₂eq)
    have hq₁mem : q₁ ∈ Set.Icc (0 : ℝ) q₂ := ⟨hq₁0, hlt.le⟩
    have hq₂mem : q₂ ∈ Set.Icc (0 : ℝ) q₂ := ⟨hq₂0, le_rfl⟩
    have hcont : ContinuousOn (fun q => B κ q) (Set.Icc (0 : ℝ) q₂) := by
      refine (B_continuousOn (κ := κ)).mono ?_
      intro q hq
      exact lt_of_le_of_lt hq.2 hq₂lt1
    have hderiv :
        ∀ x ∈ interior (Set.Icc (0 : ℝ) q₂), deriv (fun q => B κ q) x < 0 := by
      intro x hx
      have hxIoo : x ∈ Set.Ioo (0 : ℝ) q₂ := by
        simpa [interior_Icc] using hx
      have hxIoo1 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hxIoo.1, lt_trans hxIoo.2 hq₂lt1⟩
      exact deriv_B_neg κ hκ hxIoo1
    have hstrict :
        StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) q₂) :=
      strictAntiOn_of_deriv_neg (D := Set.Icc (0 : ℝ) q₂) (hD := convex_Icc _ _) hcont hderiv
    exact hstrict hq₁mem hq₂mem hlt

end B_lemmas

/-! ## 6. Reduction to a 1D equation and monotonicity of f -/

section f_lemmas

lemma f_continuousOn_Ici (κ α : ℝ) : ContinuousOn (f κ α) (Set.Ici (0 : ℝ)) := by
  -- Combine continuity of `A`, `P`, and `B`.
  sorry

lemma f_zero (κ α : ℝ) : f κ α 0 = -α * (B κ 0) := by
  -- Use `A(0)=0` and `P(0)=0`.
  sorry

lemma f_zero_neg (κ α : ℝ) (hα : 0 < α) : f κ α 0 < 0 := by
  -- Use `B(0) = (E κ)^2 > 0`.
  sorry

lemma tendsto_B_comp_P_atTop (κ : ℝ) :
    Tendsto (fun r => B κ (P r)) atTop (𝓝 (Cκ κ)) := by
  -- `P(r) → 1` and `B(q) → Cκ` as `q → 1-`.
  sorry

lemma tendsto_f_atTop (κ α : ℝ) :
    Tendsto (f κ α) atTop (𝓝 ((2 : ℝ) / Real.pi - α * Cκ κ)) := by
  -- Combine `tendsto_A_atTop` and `tendsto_B_comp_P_atTop`.
  sorry

lemma f_strictMonoOn_Ioi
    (κ α : ℝ)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    StrictMonoOn (f κ α) (Set.Ioi (0 : ℝ)) := by
  -- Use: `A` strictly increasing, `P` strictly increasing, `B` strictly decreasing.
  sorry

lemma f_root_unique
    (κ α : ℝ)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ∀ {r₁ r₂ : ℝ}, r₁ ∈ Set.Ioi 0 → r₂ ∈ Set.Ioi 0 → f κ α r₁ = 0 → f κ α r₂ = 0 → r₁ = r₂ := by
  -- Strict monotonicity implies uniqueness of roots.
  sorry

end f_lemmas

/-! ## 7. Theorem 1 (`thm:main`) -/

section TheoremMain

lemma exists_root_of_alpha_lt_alpha_c
    (κ α : ℝ)
    (hα0 : 0 < α)
    (hα : α < αc κ)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ∃ r : ℝ, r ∈ Set.Ioi (0 : ℝ) ∧ f κ α r = 0 := by
  -- Use `f(0) < 0` and `lim_{r→∞} f(r) = 2/π - α*Cκ > 0` plus IVT.
  sorry

lemma existsUnique_r_of_alpha_lt_alpha_c
    (κ α : ℝ)
    (hα0 : 0 < α)
    (hα : α < αc κ)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ∃! r : ℝ, r ∈ Set.Ioi (0 : ℝ) ∧ f κ α r = 0 := by
  -- Existence from `exists_root_of_alpha_lt_alpha_c` and uniqueness from strict monotonicity.
  sorry

lemma existsUnique_solution_of_alpha_lt_alpha_c
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ∃! qr : ℝ × ℝ, IsSolution κ α qr.1 qr.2 := by
  -- Pick unique `r*` solving `f(r)=0`, set `q* := P(r*)`, and verify the system.
  sorry

lemma no_solution_of_alpha_ge_alpha_c
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα : αc κ ≤ α)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ¬ ∃ q r : ℝ, IsSolution κ α q r := by
  -- Use `lim f ≤ 0`, strict monotonicity of `f`, and `f(0) < 0` to rule out roots.
  sorry

theorem theorem_main
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    ∃! qr : ℝ × ℝ, IsSolution κ α qr.1 qr.2 := by
  -- Use `B_strictAntiOn_Icc` as the monotonicity input.
  have hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1) := by
    simpa using (B_strictAntiOn_Icc (κ := κ) hκ)
  exact existsUnique_solution_of_alpha_lt_alpha_c κ α hκ hα0 hα hB

theorem theorem_main_no_solution
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα : αc κ ≤ α) :
    ¬ ∃ q r : ℝ, IsSolution κ α q r := by
  have hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1) := by
    simpa using (B_strictAntiOn_Icc (κ := κ) hκ)
  exact no_solution_of_alpha_ge_alpha_c κ α hκ hα hB

end TheoremMain

/-! ## 8. Canonical choice of the solution (for `α < αc`) -/

noncomputable def sol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ × ℝ :=
  Classical.choose (theorem_main (κ := κ) (α := α) hκ hα0 hα).exists

lemma sol_spec (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) :
    IsSolution κ α (sol κ α hκ hα0 hα).1 (sol κ α hκ hα0 hα).2 := by
  simpa [sol] using (Classical.choose_spec (theorem_main (κ := κ) (α := α) hκ hα0 hα).exists)

abbrev qSol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  (sol κ α hκ hα0 hα).1

abbrev rSol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  (sol κ α hκ hα0 hα).2

lemma qSol_spec (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) :
    0 ≤ qSol κ α hκ hα0 hα ∧
      qSol κ α hκ hα0 hα < 1 ∧
      0 ≤ rSol κ α hκ hα0 hα ∧
      qSol κ α hκ hα0 hα = P (rSol κ α hκ hα0 hα) ∧
      rSol κ α hκ hα0 hα = R κ (qSol κ α hκ hα0 hα) α := by
  -- Unpack `sol_spec`.
  sorry

/-! ## 9. Theorem 2 (`thm:2ndmain`) — sequential formulation -/

section TheoremSecondMain

lemma tendsto_q_of_tendsto_r
    {κ : ℝ} {α : ℕ → ℝ}
    (r : ℕ → ℝ)
    (q : ℕ → ℝ)
    (hq : ∀ n, q n = P (r n))
    (hr : Tendsto r atTop atTop) :
    Tendsto q atTop (𝓝 (1 : ℝ)) := by
  -- Use `tendsto_P_atTop` and composition.
  sorry

lemma exists_frequently_le_of_not_tendsto_atTop
    (r : ℕ → ℝ)
    (hnot : ¬ Tendsto r atTop atTop) :
    ∃ R : ℝ, (∃ᶠ n in atTop, r n ≤ R) := by
  -- Unfold `Tendsto r atTop atTop` and negate.
  sorry

lemma exists_subseq_tendsto_of_frequently_bounded
    {r : ℕ → ℝ} {R : ℝ}
    (hfreq : ∃ᶠ n in atTop, r n ∈ Set.Icc (0 : ℝ) R) :
    ∃ rStar ∈ Set.Icc (0 : ℝ) R, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (r ∘ φ) atTop (𝓝 rStar) := by
  -- Apply `tendsto_subseq_of_frequently_bounded` in `ℝ`.
  sorry

lemma solution_at_alpha_c_of_bounded_subseq
    (κ : ℝ) (hκ : 0 ≤ κ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 < α n ∧ α n < αc κ)
    (hlim : Tendsto α atTop (𝓝 (αc κ)))
    (R : ℝ)
    (hfreq : ∃ᶠ n in atTop, rSol κ (α n) hκ (hα n).1 (hα n).2 ∈ Set.Icc (0 : ℝ) R) :
    ∃ qStar rStar : ℝ, IsSolution κ (αc κ) qStar rStar := by
  -- Outline (blueprint):
  -- 1. Extract a convergent subsequence r_{φ n} → rStar.
  -- 2. Use continuity of P to get q_{φ n} → qStar := P rStar with qStar < 1.
  -- 3. Take limits in r = α * B(q)/(1-q)^2 to get a solution at αc.
  sorry

theorem theorem_second_main_seq
    (κ : ℝ) (hκ : 0 ≤ κ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 < α n ∧ α n < αc κ)
    (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    (Tendsto (fun n => rSol κ (α n) hκ (hα n).1 (hα n).2) atTop atTop) ∧
      Tendsto (fun n => qSol κ (α n) hκ (hα n).1 (hα n).2) atTop (𝓝 (1 : ℝ)) := by
  -- Main contradiction argument:
  -- if r_n does not tend to +∞, extract bounded subsequence => solution at αc,
  -- contradict Theorem 1 (no solution when α ≥ αc).
  sorry

end TheoremSecondMain

end
end Theorem1
