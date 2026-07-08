

import Mathlib

import perceptronFixed.conditionalGaussianMoments.CGM
import perceptronFixed.decreasing_g.decreasing_g
import perceptronFixed.derivative_of_B.derivative_B
import perceptronFixed.Prop_A_P.Prop_A_P
import perceptronFixed.rational_function_bound.RatioBound
import perceptronFixed.uniform_bound_of_g.uniform_bound_of_g


import Batteries.Tactic.GeneralizeProofs



/-!
# Theorem 1 and Theorem 2 (fixed point system)

This file is a detailed Lean development following:
`perceptronFixed/Theorem1/blueprint.txt`.

It formalizes the fixed point system from `main.tex` and states:
- Theorem 1 (`thm:main`): existence/uniqueness for `α < αc(κ)` and no solution for `α ≥ αc(κ)`.
- Theorem 2 (`thm:2ndmain`): as `α ↑ αc(κ)`, the solution satisfies `q_α → 1` and `r_α → +∞`.

All proofs are provided; some steps still use `exact?` automation (which can emit `Try this:` messages).
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
  have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
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
      have hnonneg_sq : 0 ≤ (max (κ - z) 0) ^ 2 := by nlinarith [hnonneg]
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg_sq] using hle_total
    have h_rhs_int : Integrable (fun z : ℝ => (2 : ℝ) * (κ ^ 2) + (2 : ℝ) * (z ^ 2)) γ :=
      (hconst.add (hsq_int.const_mul (2 : ℝ)))
    exact h_rhs_int.mono' (by
        have : Measurable fun z : ℝ => (max (κ - z) 0) ^ 2 := by fun_prop
        exact this.aestronglyMeasurable) hbound

  let f : ℝ → ℝ := fun z => (max (κ - z) 0) ^ 2
  have hf_nonneg : 0 ≤ᵐ[γ] f := by
    refine ae_of_all _ (fun z => ?_)
    exact sq_nonneg (max (κ - z) 0)
  have h_support_pos : (0 : ℝ≥0∞) < γ (Function.support f) := by
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
    have hv : (1 : ℝ≥0) ≠ 0 := by simp
    have hIoc_pos :
        (0 : ℝ≥0∞) < γ (Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ))) := by
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
        exact lt_of_lt_of_eq hpos_interval hIoc
      have h_ofReal_pos : (0 : ℝ≥0∞) < ENNReal.ofReal
            (∫ x in Set.Ioc (κ - 1) (κ - (2⁻¹ : ℝ)),
              ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x) := by
        exact ENNReal.ofReal_pos.2 hIoc_pos
      simpa [hmeas] using h_ofReal_pos
    exact lt_of_lt_of_le hIoc_pos (MeasureTheory.measure_mono hsub)
  have hpos : 0 < ∫ z, f z ∂γ := by
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
  refine tendsto_atTop.2 ?_
  intro a
  by_cases ha : a ≤ 0
  ·
    refine Filter.Eventually.of_forall (fun r => ?_)
    exact le_trans ha (Real.sqrt_nonneg _)
  · have ha' : 0 < a := lt_of_not_ge ha
    have h_event : ∀ᶠ r in atTop, a ^ 2 ≤ r := Filter.eventually_ge_atTop (a ^ 2)
    refine h_event.mono (fun r hr => ?_)
    have hr0 : 0 ≤ r := le_trans (sq_nonneg a) hr
    have ha0 : 0 ≤ a := le_of_lt ha'
    exact (Real.le_sqrt ha0 hr0).2 hr

private lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh ((1 / Real.cosh x) ^ 2) x := by
  have hs : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
  have hc : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hcosh_ne : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hq :
      HasDerivAt (fun y : ℝ => Real.sinh y / Real.cosh y)
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) x := by
    simpa using hs.div hc hcosh_ne
  have hEq :
      (fun y : ℝ => Real.tanh y) =ᶠ[𝓝 x] (fun y : ℝ => Real.sinh y / Real.cosh y) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    simpa using (Real.tanh_eq_sinh_div_cosh y)
  have hq_tanh :
      HasDerivAt Real.tanh
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) x :=
    hq.congr_of_eventuallyEq hEq
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
  have hcosh2 : 0 < (Real.cosh x) ^ 2 := sq_pos_of_pos (Real.cosh_pos x)
  have hsinh_lt : (Real.sinh x) ^ 2 < (Real.cosh x) ^ 2 := by
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
  have hcont : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 0 := by
    have : (1 + (0 : ℝ)) ≠ 0 := by norm_num
    simpa using (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id) this
  have hEq :
      (fun x : ℝ => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x)))) =ᶠ[atTop] Real.tanh := by
    refine Filter.Eventually.of_forall (fun x => (hform x).symm)
  have h' :
      Tendsto (fun x : ℝ => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x)))) atTop (𝓝 (1 : ℝ)) := by
    simpa [Function.comp] using (hcont.tendsto.comp h_exp)
  exact Filter.Tendsto.congr' hEq h'

private lemma tendsto_tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1 : ℝ)) := by
  have h : Tendsto (fun x : ℝ => Real.tanh (-x)) atBot (𝓝 (1 : ℝ)) := by
    change Tendsto (Real.tanh ∘ Neg.neg) atBot (𝓝 (1 : ℝ))
    exact tendsto_tanh_atTop.comp Filter.tendsto_neg_atBot_atTop
  have h' : Tendsto (fun x : ℝ => -Real.tanh (-x)) atBot (𝓝 (-1 : ℝ)) := by
    simpa using h.neg
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
  let I : ℝ := Expect (fun z : ℝ => (E (U κ q z)) ^ 2)
  have hB : B κ q = (1 - q) * I := by
    simp [B, I]
  have hRint :
      Expect (fun z : ℝ => (F κ q (Real.sqrt q * z)) ^ 2) = (1 / (1 - q)) * I := by
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
            rw [hfac]
  have hR : R κ q α = α * ((1 / (1 - q)) * I) := by
    unfold R
    simp [hRint]
  rw [hR, hB]
  field_simp [hne]

lemma system_equiv_f_eq_zero
    (κ α q r : ℝ)
    (hq : q = P r)
    (hq1 : q < 1) :
    (r = R κ q α) ↔ (A r = α * B κ (P r)) := by
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
    calc
      A r = r * (1 - P r) ^ 2 := by simp [A]
      _ = (α * B κ (P r) / (1 - P r) ^ 2) * (1 - P r) ^ 2 := by
        exact congrArg (fun x => x * (1 - P r) ^ 2) hr'
      _ = α * B κ (P r) := by
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
  subst hqr
  have hAiff : (f κ α r = 0) ↔ (A r = α * B κ (P r)) := by
    unfold f
    constructor
    · intro hf
      have : A r - α * B κ (P r) = 0 := by simpa using hf
      linarith
    · intro hAr
      have : A r - α * B κ (P r) = 0 := by linarith
      simpa [f] using this
  have hsys :
      (r = R κ (P r) α) ↔ (A r = α * B κ (P r)) :=
    system_equiv_f_eq_zero (κ := κ) (α := α) (q := P r) (r := r) rfl hq1
  exact (hAiff.trans hsys.symm)

lemma IsSolution_iff_f_eq_zero
    (κ α q r : ℝ) :
    IsSolution κ α q r ↔
      (0 ≤ q ∧ q < 1 ∧ 0 ≤ r ∧ q = P r ∧ f κ α r = 0) := by
  unfold IsSolution
  constructor
  · rintro ⟨hq0, hq1, hr0, hq, hr⟩
    refine ⟨hq0, hq1, hr0, hq, ?_⟩
    have : f κ α r = 0 :=
      (f_eq_zero_iff_system (κ := κ) (α := α) (q := q) (r := r) hq hq1).2 hr
    simpa using this
  · rintro ⟨hq0, hq1, hr0, hq, hf0⟩
    refine ⟨hq0, hq1, hr0, hq, ?_⟩
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
    simpa [Real.norm_eq_abs, MeasureTheory.probReal_univ] using hnorm
  have hnonneg : 0 ≤ P r := P_nonneg r
  calc
    P r = |P r| := by simpa [abs_of_nonneg hnonneg]
    _ ≤ 1 := habs

lemma P_zero : P 0 = 0 := by
  simp [P, Expect]

lemma P_lt_one (r : ℝ) : P r < 1 := by
  let f : ℝ → ℝ := fun z => (Real.tanh (Real.sqrt r * z)) ^ 2
  let g : ℝ → ℝ := fun z => 1 - f z
  have hf_int : Integrable f γ := by
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
    have huniv : (0 : ℝ≥0∞) < γ Set.univ := by
      simpa using (show (0 : ℝ≥0∞) < (1 : ℝ≥0∞) by simp)
    have hsupp : (0 : ℝ≥0∞) < γ (Function.support g) := by
      simpa [hg_support] using huniv
    exact hiff.2 hsupp
  have hsum : (∫ z, f z ∂γ) + (∫ z, g z ∂γ) = (1 : ℝ) := by
    have hfg : Integrable (fun z => f z + g z) γ := hf_int.add hg_int
    have : (∫ z, f z ∂γ) + (∫ z, g z ∂γ) = (∫ z, (fun z => f z + g z) z ∂γ) :=
      (MeasureTheory.integral_add hf_int hg_int).symm
    have hone : (∫ z, (1 : ℝ) ∂γ) = (1 : ℝ) := by
      simpa [MeasureTheory.integral_const, MeasureTheory.probReal_univ] using
        (MeasureTheory.integral_const (μ := γ) (c := (1 : ℝ)))
    have hpoint : (fun z => f z + g z) = fun _z => (1 : ℝ) := by
      funext z
      simp [g, f]
    simpa [hpoint, hone] using this
  have : (∫ z, f z ∂γ) < (1 : ℝ) := by
    have : 0 < ∫ z, g z ∂γ := hg_pos
    linarith [hsum, this]
  simpa [P, Expect, f] using this

lemma P_continuous : Continuous P := by
  refine continuous_iff_continuousAt.2 (fun r0 => ?_)
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
      have h1 : f₁ z = f₁ (-z) := by
        simp [f₁, Real.tanh_neg, pow_two, mul_assoc]
      have h2 : f₂ z = f₂ (-z) := by
        simp [f₂, Real.tanh_neg, pow_two, mul_assoc]
      rw [h1, h2]
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
  have hle : ∫ z, f₁ z ∂γ ≤ ∫ z, f₂ z ∂γ := by
    exact MeasureTheory.integral_mono hf₁ hf₂ hpoint
  simpa [P, Expect, f₁, f₂] using hle

lemma P_strictMonoOn_Ici : StrictMonoOn P (Set.Ici (0 : ℝ)) := by
  intro r₁ hr₁ r₂ hr₂ hrlt
  have hrle : r₁ ≤ r₂ := le_of_lt hrlt
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
        have hf1 : f₁ z = (Real.tanh (Real.sqrt r₁ * |z|)) ^ 2 := by
          by_cases hz' : 0 ≤ z
          · simp [f₁, abs_of_nonneg hz']
          · simp [f₁, abs_of_neg (lt_of_not_ge hz'), Real.tanh_neg, pow_two, mul_assoc]
        have hf2 : f₂ z = (Real.tanh (Real.sqrt r₂ * |z|)) ^ 2 := by
          by_cases hz' : 0 ≤ z
          · simp [f₂, abs_of_nonneg hz']
          · simp [f₂, abs_of_neg (lt_of_not_ge hz'), Real.tanh_neg, pow_two, mul_assoc]
        dsimp [h]
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
  have hdiff : P r₂ - P r₁ = ∫ z, h z ∂γ := by
    have : ∫ z, h z ∂γ = (∫ z, f₂ z ∂γ) - ∫ z, f₁ z ∂γ := by
      simpa [h] using (MeasureTheory.integral_sub hf₂ hf₁)
    simpa [P, Expect, f₁, f₂, this, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have : P r₁ < P r₂ := by
    have : 0 < P r₂ - P r₁ := by simpa [hdiff] using hint_pos
    linarith
  exact this

lemma tendsto_P_atTop : Tendsto P atTop (𝓝 (1 : ℝ)) := by
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
  have hsingleton : γ ({0} : Set ℝ) = 0 := by
    have hv : (1 : ℝ≥0) ≠ 0 := by simp
    have hac : γ ≪ (volume : Measure ℝ) := by
      simpa [γ] using
        (ProbabilityTheory.gaussianReal_absolutelyContinuous (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)
    simpa using hac (by simp : (volume : Measure ℝ) ({0} : Set ℝ) = 0)
  have h_lim :
      (∀ᵐ z : ℝ ∂γ, Tendsto (fun r : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) atTop (𝓝 (1 : ℝ))) := by
    have hz_ne : ∀ᵐ z : ℝ ∂γ, z ≠ 0 := by
      simp [MeasureTheory.ae_iff, hsingleton]
    filter_upwards [hz_ne] with z hz
    have hzlt_or : z < 0 ∨ 0 < z := lt_or_gt_of_ne hz
    cases hzlt_or with
    | inl hzlt =>
        have hzpos : 0 < -z := by linarith
        have hpos : Tendsto (fun r : ℝ => Real.sqrt r * (-z)) atTop atTop :=
          (Filter.Tendsto.atTop_mul_const (r := (-z)) hzpos tendsto_sqrt_atTop)
        have h_arg : Tendsto (fun r : ℝ => Real.sqrt r * z) atTop atBot := by
          have hneg : Tendsto (fun r : ℝ => -(Real.sqrt r * (-z))) atTop atBot :=
            (Filter.tendsto_neg_atTop_atBot.comp hpos)
          simpa [mul_assoc] using hneg
        have ht : Tendsto (fun r : ℝ => Real.tanh (Real.sqrt r * z)) atTop (𝓝 (-1 : ℝ)) :=
          tendsto_tanh_atBot.comp h_arg
        simpa using (ht.pow 2)
    | inr hzgt =>
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

def sech (x : ℝ) : ℝ :=
  1 / Real.cosh x

def S (r : ℝ) : ℝ :=
  Expect (fun z => (sech (Real.sqrt r * z)) ^ 2)

lemma S_eq_one_sub_P (r : ℝ) : S r = 1 - P r := by
  have hpoint : ∀ x : ℝ, (sech x) ^ 2 = 1 - (Real.tanh x) ^ 2 := by
    intro x
    have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    have hcosh2 : (Real.cosh x ^ 2) ≠ 0 := pow_ne_zero 2 hcosh
    have hsum : (Real.tanh x) ^ 2 + (sech x) ^ 2 = 1 := by
      rw [Real.tanh_eq_sinh_div_cosh, sech, div_pow, div_pow]
      field_simp [hcosh2]
      simpa using (Real.cosh_sq x).symm
    linarith
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
  unfold S P Expect
  have hfun :
      (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) =
        fun z : ℝ => (1 : ℝ) - (Real.tanh (Real.sqrt r * z)) ^ 2 := by
    funext z
    simpa using (hpoint (Real.sqrt r * z))
  simp [hfun, integral_sub (integrable_const (1 : ℝ)) hf_int,
    MeasureTheory.integral_const, MeasureTheory.probReal_univ]

lemma A_eq_r_mul_S_sq (r : ℝ) : A r = r * (S r) ^ 2 := by
  simp [A, S_eq_one_sub_P]

lemma A_zero : A 0 = 0 := by
  simp [A, P_zero]

lemma A_continuous : Continuous A := by
  unfold A
  simpa [sub_eq_add_neg] using (continuous_id.mul ((continuous_const.sub P_continuous).pow 2))

lemma A_continuousOn_Ici : ContinuousOn A (Set.Ici (0 : ℝ)) := by
  simpa [ContinuousOn] using A_continuous.continuousOn

lemma A_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ A r := by
  unfold A
  exact mul_nonneg hr (sq_nonneg (1 - P r))

/-! ### Change-of-variables integral `I(r)` -/

/-- Scalar integral used in the representation `A(r) = (1/(2π)) * I(r)^2` for `r > 0`. -/
def I (r : ℝ) : ℝ :=
  ∫ y : ℝ, (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))

lemma integral_sech_sq : (∫ y : ℝ, (sech y) ^ 2) = (2 : ℝ) := by
  have hcont_sech : Continuous sech := by
    have hcosh_ne : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
    unfold sech
    simpa [one_div] using (Continuous.inv₀ Real.continuous_cosh hcosh_ne)
  have hcont : Continuous fun y : ℝ => (sech y) ^ 2 := by
    simpa using hcont_sech.pow 2
  have hderiv : deriv Real.tanh = fun y : ℝ => (sech y) ^ 2 := by
    funext y
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
    simpa [Real.tanh_neg, sub_eq_add_neg, two_mul] using hFTC
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
    have hmeas : AEStronglyMeasurable F (volume : Measure ℝ) := by
      have hcont_sech : Continuous sech := by
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
          simpa [sech, Theorem1.sech] using this
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
  unfold B U Expect
  simp [γ, MeasureTheory.integral_const, MeasureTheory.probReal_univ]

noncomputable section AristotleLemmas

/-
(E u)^2 is bounded by a quadratic polynomial.
-/
lemma E_sq_le_poly (u : ℝ) : (Theorem1.E u)^2 ≤ 2 * u^2 + 4 := by
  by_cases hu : 0 ≤ u
  ·
    have hd_le : DecreasingG.d u ≤ DecreasingG.d 0 := DecreasingG.d_le_d0_of_nonneg hu
    have hE_le_d0 : E u ≤ u + DecreasingG.d 0 := by
      have hE_eq : E u = u + DecreasingG.d u := by
        simp [DecreasingG.d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      simpa [hE_eq] using (add_le_add_left hd_le u)
    have hd0_le_one : DecreasingG.d 0 ≤ (1 : ℝ) := by
      have hd0 : DecreasingG.d 0 = Real.sqrt (2 / Real.pi) := DecreasingG.d0_eq_sqrt_two_div_pi
      have h2pi : (2 : ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
      have hdiv : (2 : ℝ) / Real.pi ≤ (1 : ℝ) := by
        exact (div_le_iff₀ Real.pi_pos).2 (by simpa [one_mul] using h2pi)
      have hsqrt : Real.sqrt (2 / Real.pi) ≤ (1 : ℝ) := by
        refine (Real.sqrt_le_iff).2 ?_
        exact ⟨by norm_num, by simpa using hdiv⟩
      simpa [hd0] using hsqrt
    have hE_le : E u ≤ u + 1 :=
      le_trans hE_le_d0 (by simpa using add_le_add_left hd0_le_one u)
    have hE0 : 0 ≤ E u := le_of_lt (DecreasingG.E_pos u)
    have hsq : (E u) ^ 2 ≤ (u + 1) ^ 2 := pow_le_pow_left₀ hE0 hE_le 2
    have hsq' : (u + 1) ^ 2 ≤ 2 * u ^ 2 + 4 := by nlinarith [hu]
    exact le_trans hsq hsq'
  ·
    have hu0 : u ≤ 0 := le_of_not_ge hu
    have hΦbar0 : Φbar (0 : ℝ) = (1 / 2 : ℝ) := by
      have hIoi : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2) / 2)) = Real.sqrt (2 * Real.pi) / 2 := by
        have h := integral_gaussian_Ioi (1 / 2 : ℝ)
        simpa [mul_assoc, div_eq_mul_inv, mul_comm, mul_left_comm, mul_right_comm] using h
      have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by
        exact Real.sqrt_pos.2 (by positivity)
      have hφ0 : (∫ x in Set.Ioi (0 : ℝ), φ x) = (1 / 2 : ℝ) := by
        have : (∫ x in Set.Ioi (0 : ℝ), φ x) =
            (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
          simp [φ, DecreasingG.φ, MeasureTheory.integral_div]
        rw [this, hIoi]
        field_simp [hsqrt_pos.ne']
      simpa [Φbar, DecreasingG.Φbar, MeasureTheory.integral_Ici_eq_integral_Ioi] using hφ0
    have hφ_int : Integrable φ (volume : Measure ℝ) := by
      have hφ_eq : φ = ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) := by
        funext x
        simp [φ, DecreasingG.φ, ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv, mul_assoc, mul_comm,
          mul_left_comm]
      simpa [hφ_eq] using
        ProbabilityTheory.integrable_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    have hst : (Set.Ici (0 : ℝ) : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Ici u := by
      refine ae_of_all _ (fun x hx => ?_)
      exact le_trans hu0 hx
    have hfi : IntegrableOn φ (Set.Ici u) (volume : Measure ℝ) := hφ_int.integrableOn
    have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ici u)] φ := by
      refine ae_of_all _ (fun x => (UniformBoundOfG.φ_pos x).le)
    have hΦ : Φbar (0 : ℝ) ≤ Φbar u := by
      have hle :=
        MeasureTheory.setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := φ)
          (s := Set.Ici (0 : ℝ)) (t := Set.Ici u) hfi hnonneg hst
      simpa [Φbar, DecreasingG.Φbar] using hle
    have hE_le : E u ≤ 2 := by
      have hφ_nonneg : 0 ≤ φ u := (UniformBoundOfG.φ_pos u).le
      have hΦ0_pos : 0 < Φbar (0 : ℝ) := by
        simpa [hΦbar0] using (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))
      have hdiv := div_le_div_of_nonneg_left hφ_nonneg hΦ0_pos hΦ
      have hE_le_div : E u ≤ φ u / Φbar (0 : ℝ) := by
        simpa [E, DecreasingG.E] using hdiv
      have hE_le_2phi : E u ≤ 2 * φ u := by
        simpa [hΦbar0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hE_le_div
      have hφ_le_one : φ u ≤ 1 := by
        have hexp_le : Real.exp (-(u ^ 2) / 2) ≤ (1 : ℝ) := by
          have : (-(u ^ 2) / 2 : ℝ) ≤ 0 := by nlinarith
          simpa using (Real.exp_le_one_iff.2 this)
        have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) := by positivity
        have hφ_le : φ u ≤ 1 / Real.sqrt (2 * Real.pi) := by
          simpa [φ, DecreasingG.φ] using (div_le_div_of_nonneg_right hexp_le hsqrt_nonneg)
        have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
          have h1 : (1 : ℝ) ≤ 2 * Real.pi := by
            nlinarith [Real.pi_gt_three]
          exact (Real.one_le_sqrt).2 h1
        have : (1 : ℝ) / Real.sqrt (2 * Real.pi) ≤ 1 := by
          have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by
            exact Real.sqrt_pos.2 (by positivity)
          exact (div_le_iff₀ hsqrt_pos).2 (by simpa [one_mul] using hsqrt_ge_one)
        exact le_trans hφ_le this
      have : 2 * φ u ≤ (2 : ℝ) := by nlinarith [hφ_le_one]
      exact le_trans hE_le_2phi this
    have hE0 : 0 ≤ E u := le_of_lt (DecreasingG.E_pos u)
    have hsq : (E u) ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ hE0 hE_le 2
    nlinarith [hsq]

/-
The expectation of the square of the inverse Mills ratio of U is continuous in q.
-/
lemma integral_E_sq_continuousAt (κ : ℝ) (q₀ : ℝ) (hq₀ : q₀ < 1) :
    ContinuousAt (fun q => Theorem1.Expect (fun z => (Theorem1.E (Theorem1.U κ q z)) ^ 2)) q₀ := by
  let δ : ℝ := (1 - q₀) / 2
  have hδ : 0 < δ := by
    have : 0 < (1 - q₀) := by linarith
    have : 0 < (1 - q₀) / 2 := by nlinarith
    simpa [δ] using this
  let bound : ℝ → ℝ := fun z => 2 * ((1 / Real.sqrt δ) * (|κ| + |z|)) ^ 2 + 4

  have hF_meas : ∀ q : ℝ, AEStronglyMeasurable (fun z : ℝ => (E (U κ q z)) ^ 2) γ := by
    intro q
    have hcontE : Continuous E := by
      simpa [Theorem1.E, UniformBoundOfG.E] using (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E)
    have hcontU : Continuous (fun z : ℝ => U κ q z) := by
      unfold U
      have hnum : Continuous (fun z : ℝ => κ - Real.sqrt q * z) :=
        continuous_const.sub (continuous_const.mul continuous_id)
      simpa using hnum.div_const (Real.sqrt (1 - q))
    have hcont : Continuous (fun z : ℝ => (E (U κ q z)) ^ 2) := by
      simpa using (hcontE.comp hcontU).pow 2
    exact hcont.aestronglyMeasurable

  have hZ2 : Integrable (fun z : ℝ => z ^ 2) γ := by
    have h : MemLp (fun z : ℝ => z) 2 γ := by
      simpa [γ, Theorem1.γ] using
        (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0)))
    simpa using h.integrable_sq
  have hbound_int : Integrable bound γ := by
    have hconst : Integrable (fun _z : ℝ => (1 : ℝ)) γ := integrable_const _
    have hκ2 : Integrable (fun _z : ℝ => (κ ^ 2 : ℝ)) γ := (integrable_const _)
    have hz2 : Integrable (fun z : ℝ => (z ^ 2 : ℝ)) γ := hZ2
    have habs2 : Integrable (fun z : ℝ => (|z| ^ 2 : ℝ)) γ := by
      simpa [pow_two, abs_mul] using hz2
    have hsum2 : Integrable (fun z : ℝ => (|κ| + |z|) ^ 2) γ := by
      have hdom : ∀ z : ℝ, (|κ| + |z|) ^ 2 ≤ 2 * ((|κ| ^ 2) + (|z| ^ 2)) := by
        intro z
        simpa [pow_two, mul_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_left_comm, mul_comm] using
          (add_sq_le (a := |κ|) (b := |z|))
      have hdom_ae : ∀ᵐ z ∂γ, ‖(fun z : ℝ => (|κ| + |z|) ^ 2) z‖ ≤ (fun z : ℝ => 2 * ((|κ| ^ 2) + (|z| ^ 2))) z := by
        refine ae_of_all _ (fun z => ?_)
        have hz : 0 ≤ (|κ| + |z|) ^ 2 := by nlinarith
        simpa [Real.norm_eq_abs, abs_of_nonneg hz] using (hdom z)
      have hint : Integrable (fun z : ℝ => 2 * ((|κ| ^ 2) + (|z| ^ 2))) γ := by
        have hκabs2 : Integrable (fun _z : ℝ => (|κ| ^ 2 : ℝ)) γ := integrable_const _
        have hzabs2 : Integrable (fun z : ℝ => (|z| ^ 2 : ℝ)) γ := by
          simpa [pow_two, abs_mul] using hz2
        exact ((hκabs2.add hzabs2).const_mul 2)
      exact Integrable.mono' hint (by fun_prop) hdom_ae
    have hmain : Integrable (fun z : ℝ => ((1 / Real.sqrt δ) * (|κ| + |z|)) ^ 2) γ := by
      have : (fun z : ℝ => ((1 / Real.sqrt δ) * (|κ| + |z|)) ^ 2) =
          fun z : ℝ => ((1 / Real.sqrt δ) ^ 2) * ((|κ| + |z|) ^ 2) := by
        funext z
        ring
      rw [this]
      exact hsum2.const_mul ((1 / Real.sqrt δ) ^ 2)
    have : bound = fun z : ℝ => 2 * (((1 / Real.sqrt δ) * (|κ| + |z|)) ^ 2) + 4 := by
      rfl
    rw [this]
    exact (hmain.const_mul 2).add (integrable_const _)

  have hbound : ∀ᶠ q in nhds q₀, ∀ᵐ z ∂γ, ‖(E (U κ q z)) ^ 2‖ ≤ bound z := by
    have hqmax : q₀ < q₀ + δ := by
      have : 0 < δ := hδ
      linarith
    have hq_event : ∀ᶠ q in nhds q₀, q < q₀ + δ := by
      simpa [Filter.Eventually, Set.mem_Iio] using (Iio_mem_nhds hqmax)
    filter_upwards [hq_event] with q hq
    refine ae_of_all _ (fun z => ?_)
    have hden : Real.sqrt (1 - q) ≥ Real.sqrt δ := by
      have hEq : 1 - (q₀ + δ) = δ := by
        simp [δ]
        ring
      have hlt : 1 - (q₀ + δ) < 1 - q := by
        linarith
      have h1q : δ ≤ 1 - q := by
        have : δ < 1 - q := by simpa [hEq] using hlt
        exact le_of_lt this
      exact Real.sqrt_le_sqrt h1q
    have hsqrtδ_pos : (0 : ℝ) < Real.sqrt δ := by
      exact Real.sqrt_pos.2 (by nlinarith [hδ])
    have hU_bound : |U κ q z| ≤ (1 / Real.sqrt δ) * (|κ| + |z|) := by
      have hqmax1 : q₀ + δ < 1 := by
        dsimp [δ]
        nlinarith [hq₀]
      have hq1 : q ≤ 1 := le_of_lt (lt_trans hq hqmax1)
      have hsqrtq_le : Real.sqrt q ≤ 1 := by
        exact (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using hq1⟩
      have hnum : |κ - Real.sqrt q * z| ≤ |κ| + |z| := by
        calc
          |κ - Real.sqrt q * z| ≤ |κ| + |Real.sqrt q * z| := by
            simpa [sub_eq_add_neg, abs_neg] using (abs_add_le κ (-(Real.sqrt q * z)))
          _ = |κ| + (Real.sqrt q) * |z| := by
            simp [abs_mul, Real.sqrt_nonneg]
          _ ≤ |κ| + 1 * |z| := by
            gcongr
          _ = |κ| + |z| := by ring
      have hden_pos : (0 : ℝ) < Real.sqrt (1 - q) := by
        have : 0 < 1 - q := by
          have : q < 1 := lt_trans hq (by linarith [hδ, hq₀])
          linarith
        exact Real.sqrt_pos.2 this
      have hdiv : |U κ q z| = |κ - Real.sqrt q * z| / Real.sqrt (1 - q) := by
        simp [U, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [hdiv]
      have hfrac : |κ - Real.sqrt q * z| / Real.sqrt (1 - q) ≤ (|κ| + |z|) / Real.sqrt δ := by
        have h1 :
            |κ - Real.sqrt q * z| / Real.sqrt (1 - q) ≤ (|κ| + |z|) / Real.sqrt (1 - q) := by
          exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
        have h2 :
            (|κ| + |z|) / Real.sqrt (1 - q) ≤ (|κ| + |z|) / Real.sqrt δ := by
          have hnonneg : 0 ≤ |κ| + |z| := add_nonneg (abs_nonneg _) (abs_nonneg _)
          exact div_le_div_of_nonneg_left hnonneg hsqrtδ_pos hden
        exact le_trans h1 h2
      simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using hfrac
    have hE : (E (U κ q z)) ^ 2 ≤ 2 * (U κ q z) ^ 2 + 4 := by
      simpa using (E_sq_le_poly (u := U κ q z))
    have hU2 : (U κ q z) ^ 2 ≤ ((1 / Real.sqrt δ) * (|κ| + |z|)) ^ 2 := by
      have : |U κ q z| ≤ (1 / Real.sqrt δ) * (|κ| + |z|) := hU_bound
      have h0 : 0 ≤ (1 / Real.sqrt δ) * (|κ| + |z|) := by
        have hA : 0 ≤ (1 / Real.sqrt δ) := by positivity
        have hB : 0 ≤ |κ| + |z| := add_nonneg (abs_nonneg _) (abs_nonneg _)
        exact mul_nonneg hA hB
      have := pow_le_pow_left₀ (abs_nonneg (U κ q z)) this 2
      simpa [pow_two] using this
    have hfinal : (E (U κ q z)) ^ 2 ≤ bound z := by
      have : 2 * (U κ q z) ^ 2 ≤ 2 * (((1 / Real.sqrt δ) * (|κ| + |z|)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hU2 (by positivity : 0 ≤ (2 : ℝ))
      have : 2 * (U κ q z) ^ 2 + 4 ≤ 2 * (((1 / Real.sqrt δ) * (|κ| + |z|)) ^ 2) + 4 := by
        linarith
      have := le_trans hE this
      simpa [bound] using this
    have hnonneg : 0 ≤ (E (U κ q z)) ^ 2 := by nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hfinal

  have hlim : ∀ᵐ z ∂γ, Tendsto (fun q => (E (U κ q z)) ^ 2) (nhds q₀) (𝓝 ((E (U κ q₀ z)) ^ 2)) := by
    refine ae_of_all _ (fun z => ?_)
    have hcontE : Continuous E := by
      simpa [Theorem1.E, UniformBoundOfG.E] using (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E)
    have hcontU : ContinuousAt (fun q => U κ q z) q₀ := by
      have hden0 : Real.sqrt (1 - q₀) ≠ 0 := by
        have : 0 < 1 - q₀ := by linarith
        exact (Real.sqrt_ne_zero').2 this
      have hnum : Tendsto (fun q => κ - Real.sqrt q * z) (nhds q₀) (nhds (κ - Real.sqrt q₀ * z)) := by
        exact tendsto_const_nhds.sub ((Real.continuous_sqrt.tendsto q₀).mul tendsto_const_nhds)
      have hden : Tendsto (fun q => Real.sqrt (1 - q)) (nhds q₀) (nhds (Real.sqrt (1 - q₀))) := by
        simpa using (Real.continuous_sqrt.tendsto (1 - q₀)).comp (tendsto_const_nhds.sub tendsto_id)
      have := hnum.div hden hden0
      simpa [U] using this
    have hcomp : Tendsto (fun q => E (U κ q z)) (nhds q₀) (𝓝 (E (U κ q₀ z))) :=
      (hcontE.tendsto _).comp hcontU
    simpa using (hcomp.pow 2)

  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := γ)
      (F := fun q z => (E (U κ q z)) ^ 2)
      (f := fun z => (E (U κ q₀ z)) ^ 2)
      bound
      (Filter.Eventually.of_forall (fun q => hF_meas q))
      hbound
      hbound_int
      hlim
  simpa [ContinuousAt, Theorem1.Expect] using h

end AristotleLemmas

lemma B_continuousOn (κ : ℝ) : ContinuousOn (fun q => B κ q) (Set.Iio (1 : ℝ)) := by
  refine' ContinuousOn.mul _ _;
  · exact continuousOn_const.sub continuousOn_id;
  · exact fun q hq => integral_E_sq_continuousAt κ q hq |> ContinuousAt.continuousWithinAt

noncomputable section AristotleLemmas

lemma Theorem1.E_le_max_u_zero_add_two (u : ℝ) : Theorem1.E u ≤ max u 0 + 2 := by
  by_cases hu : 0 ≤ u;
  · have h_E_le_u_plus_d0 : DecreasingG.E u ≤ u + DecreasingG.d 0 := by
      have h_E_le_u_plus_d0 : DecreasingG.E u = u + DecreasingG.d u := by
        unfold DecreasingG.d; ring;
      refine h_E_le_u_plus_d0 ▸ ?_
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left (DecreasingG.d_le_d0_of_nonneg hu) u)
    have h_d0_le_2 : DecreasingG.d 0 ≤ 1 := by
      have h_d0_le_1 : DecreasingG.d 0 = Real.sqrt (2 / Real.pi) := by
        exact DecreasingG.d0_eq_sqrt_two_div_pi;
      exact h_d0_le_1 ▸ Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ( by positivity ) ] ; linarith [ Real.pi_gt_three ] ⟩;
    linarith [ le_max_left u 0, le_max_right u 0 ];
  ·
    have h_E_neg : DecreasingG.E u ≤ 2 * φ u := by
      have h_E_neg : DecreasingG.E u ≤ φ u / (1 / 2) := by
        have h_E_neg : DecreasingG.Φbar u ≥ 1 / 2 := by
          have h_phi_bar_ge_phi_bar_zero : ∫ x in Set.Ici u, φ x ≥ ∫ x in Set.Ici 0, φ x := by
            refine' MeasureTheory.setIntegral_mono_set _ _ _;
            · exact MeasureTheory.Integrable.integrableOn ( by exact MeasureTheory.integrable_of_integral_eq_one ( by rw [ show Theorem1.φ = fun x => Real.exp ( - ( x ^ 2 ) / 2 ) / Real.sqrt ( 2 * Real.pi ) by ext; rfl ] ; rw [ MeasureTheory.integral_div, div_eq_iff ] <;> first | positivity | have := integral_gaussian ( 1 / 2 ) ; norm_num [ div_eq_inv_mul, mul_comm, mul_assoc, mul_left_comm, Real.pi_pos.le ] at * ; linarith ) );
            · exact Filter.Eventually.of_forall fun x => div_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ );
            · exact MeasureTheory.ae_of_all _ fun x hx => le_trans ( le_of_not_ge hu ) hx;
          have h_phi_bar_zero : ∫ x in Set.Ici 0, φ x = 1 / 2 := by
            have h_phi_bar_zero : ∫ x in Set.Ici 0, φ x = ∫ x in Set.Ioi 0, φ x := by
              rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ];
            have h_phi_bar_zero : ∫ x in Set.Ioi 0, φ x = 1 / 2 := by
              have h_gauss_integral : ∫ x in Set.Ioi 0, Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * Real.pi) / 2 := by
                simpa [ div_eq_inv_mul ] using integral_gaussian_Ioi ( 1 / 2 )
              unfold Theorem1.φ; norm_num [ h_gauss_integral, MeasureTheory.integral_div ] ; ring; norm_num [ Real.sqrt_ne_zero'.mpr Real.pi_pos ] ;
              unfold DecreasingG.φ; norm_num [ h_gauss_integral, MeasureTheory.integral_div ] ; ring; norm_num [ Real.sqrt_ne_zero'.mpr Real.pi_pos ] ;
              norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.pi_pos, Real.sqrt_pos ];
            grind;
          exact h_phi_bar_zero ▸ h_phi_bar_ge_phi_bar_zero;
        exact div_le_div_of_nonneg_left ( by exact div_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ ) ) ( by positivity ) h_E_neg;
      linarith;
    have h_phi_bound : φ u ≤ 1 / Real.sqrt (2 * Real.pi) := by
      exact div_le_div_of_nonneg_right ( Real.exp_le_one_iff.mpr <| by nlinarith ) ( Real.sqrt_nonneg _ );
    norm_num [ hu ] at *;
    exact le_trans h_E_neg ( by nlinarith [ inv_pos.mpr ( Real.sqrt_pos.mpr Real.pi_pos ), inv_pos.mpr ( Real.sqrt_pos.mpr zero_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr Real.pi_pos ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ), Real.sqrt_nonneg π, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ Real.pi by positivity ), Real.sq_sqrt ( show 0 ≤ 2 by positivity ), Real.pi_gt_three, le_max_right u 0, inv_le_one_of_one_le₀ ( show 1 ≤ Real.sqrt Real.pi by exact Real.le_sqrt_of_sq_le <| by linarith [ Real.pi_gt_three ] ), inv_le_one_of_one_le₀ ( show 1 ≤ Real.sqrt 2 by exact Real.le_sqrt_of_sq_le <| by norm_num ) ] )

lemma Theorem1.E_asymp_atTop : Filter.Tendsto (fun u => Theorem1.E u / u) Filter.atTop (nhds 1) := by
  have h_E_div_u : Filter.Tendsto (fun u => (u + DecreasingG.d u) / u) Filter.atTop (𝓝 1) := by
    have h_bound : ∀ u ≥ 0, |DecreasingG.d u / u| ≤ DecreasingG.d 0 / u := by
      intros u hu
      have h_d_le_d0 : DecreasingG.d u ≤ DecreasingG.d 0 := by
        exact DecreasingG.d_le_d0_of_nonneg hu;
      rw [ abs_of_nonneg ( div_nonneg ( le_of_lt ( DecreasingG.d_pos u ) ) hu ) ] ; gcongr;
    have h_squeeze : Filter.Tendsto (fun u => DecreasingG.d 0 / u) Filter.atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop Filter.tendsto_id;
    have h_squeeze : Filter.Tendsto (fun u => DecreasingG.d u / u) Filter.atTop (nhds 0) := by
      exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 0, fun u hu => h_bound u hu ⟩ ) h_squeeze;
    simpa using Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with u hu; simp +decide [ add_div, hu.ne' ] ) ( h_squeeze.const_add 1 );
  convert h_E_div_u using 2 ; unfold DecreasingG.d ; ring!

lemma Theorem1.limit_one_sub_q_mul_U_sq (κ z : ℝ) : Filter.Tendsto (fun q => (1 - q) * (Theorem1.U κ q z)^2) (nhdsWithin 1 (Set.Iio 1)) (nhds ((κ - z)^2)) := by
  suffices h_simplify : Filter.Tendsto (fun q => (1 - q) * ((κ - Real.sqrt q * z) ^ 2 / (1 - q))) (𝓝[<] 1) (𝓝 ((κ - z) ^ 2)) by
    refine h_simplify.congr' ?_;
    filter_upwards [ Ioo_mem_nhdsLT zero_lt_one ] with q hq using by rw [ show Theorem1.U κ q z = ( κ - Real.sqrt q * z ) / Real.sqrt ( 1 - q ) by rfl ] ; rw [ div_pow, Real.sq_sqrt <| by linarith [ hq.1, hq.2 ] ] ;
  suffices h_cancel : Filter.Tendsto (fun q => (κ - Real.sqrt q * z) ^ 2) (𝓝[<] 1) (𝓝 ((κ - z) ^ 2)) by
    refine' h_cancel.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with q hq using by rw [ mul_div_cancel₀ _ ( by linarith [ hq.out ] ) ] );
  convert Filter.Tendsto.pow ( tendsto_const_nhds.sub ( Filter.Tendsto.mul ( Real.continuous_sqrt.continuousWithinAt ) tendsto_const_nhds ) ) 2 using 2 ; norm_num

lemma Theorem1.tendsto_E_atBot : Filter.Tendsto Theorem1.E Filter.atBot (nhds 0) := by
  have hE_tendsto_zero : Filter.Tendsto (fun u => DecreasingG.φ u / DecreasingG.Φbar u) Filter.atBot (nhds 0) := by
    unfold DecreasingG.φ DecreasingG.Φbar;
    have h_denom : Filter.Tendsto (fun u => ∫ x in Set.Ici u, (Real.exp (-x ^ 2 / 2)) / Real.sqrt (2 * Real.pi)) Filter.atBot (nhds 1) := by
      have h_denom : Filter.Tendsto (fun u => ∫ x in Set.Ici u, (Real.exp (-x ^ 2 / 2)) / Real.sqrt (2 * Real.pi)) Filter.atBot (nhds (∫ x in Set.univ, (Real.exp (-x ^ 2 / 2)) / Real.sqrt (2 * Real.pi))) := by
        have h_denom : Filter.Tendsto (fun u => ∫ x in Set.univ, (Real.exp (-x ^ 2 / 2)) / Real.sqrt (2 * Real.pi) * (if x ≥ u then 1 else 0)) Filter.atBot (nhds (∫ x in Set.univ, (Real.exp (-x ^ 2 / 2)) / Real.sqrt (2 * Real.pi))) := by
          refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
          refine' fun x => Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi );
          · exact Filter.Eventually.of_forall fun n => Measurable.aestronglyMeasurable ( by exact Measurable.mul ( by exact Continuous.measurable ( by continuity ) ) ( by exact Measurable.ite ( measurableSet_Ici ) measurable_const measurable_const ) );
          · filter_upwards [ Filter.eventually_lt_atBot 0 ] with n hn using Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num [ abs_of_nonneg, Real.exp_nonneg, div_nonneg, Real.sqrt_nonneg ] ;
          · exact MeasureTheory.integrable_of_integral_eq_one ( by rw [ MeasureTheory.integral_div, div_eq_iff ( by positivity ) ] ; simpa [ div_eq_inv_mul ] using integral_gaussian ( 1 / 2 ) );
          · filter_upwards [ ] with x using tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_lt_atBot x ] with n hn; split_ifs <;> linarith );
        convert h_denom using 2 ; norm_num [ ← MeasureTheory.integral_indicator, Set.indicator_apply ];
      convert h_denom using 2;
      rw [ MeasureTheory.integral_div, eq_comm ];
      rw [ div_eq_iff ( by positivity ) ] ; have := integral_gaussian ( 1 / 2 ) ; norm_num [ div_eq_inv_mul ] at * ; linarith;
    field_simp;
    exact le_trans ( Filter.Tendsto.div ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| by exact Filter.Tendsto.atTop_div_const ( by positivity ) <| by exact Filter.tendsto_atBot_atTop.mpr fun b => ⟨ -b - 1, fun u hu => by nlinarith ⟩ ) ( tendsto_const_nhds.mul h_denom ) <| by positivity ) <| by norm_num;
  exact hE_tendsto_zero.congr fun x => by rfl;

lemma Theorem1.tendsto_U_atTop (κ z : ℝ) (h : z < κ) :
    Filter.Tendsto (fun q => Theorem1.U κ q z) (nhdsWithin 1 (Set.Iio 1)) Filter.atTop := by
      have h_sqrt : Filter.Tendsto (fun q => Real.sqrt (1 - q)) (𝓝[<] 1) (nhdsWithin 0 (Set.Ioi 0)) := by
        refine' Filter.Tendsto.inf _ _ <;> norm_num;
        convert Filter.Tendsto.sqrt ( tendsto_const_nhds.sub Filter.tendsto_id ) using 2 ; norm_num;
      have h_num : Filter.Tendsto (fun q => κ - Real.sqrt q * z) (𝓝[<] 1) (nhds (κ - z)) := by
        convert tendsto_const_nhds.sub ( Filter.Tendsto.mul ( Real.continuous_sqrt.continuousWithinAt ) tendsto_const_nhds ) using 2 ; norm_num;
      apply_rules [ Filter.Tendsto.pos_mul_atTop, h_num ];
      · linarith;
      · exact Filter.Tendsto.inv_tendsto_nhdsGT_zero h_sqrt

lemma Theorem1.tendsto_U_atBot (κ z : ℝ) (h : κ < z) :
    Filter.Tendsto (fun q => Theorem1.U κ q z) (nhdsWithin 1 (Set.Iio 1)) Filter.atBot := by
      have h_sqrt : Filter.Tendsto (fun q => Real.sqrt (1 - q)) (nhdsWithin 1 (Set.Iio 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
        refine' Filter.Tendsto.inf _ _ <;> norm_num;
        refine' Continuous.tendsto' _ _ _ _ <;> continuity;
      have h_num : Filter.Tendsto (fun q => κ - Real.sqrt q * z) (nhdsWithin 1 (Set.Iio 1)) (nhds (κ - z)) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
      apply_rules [ Filter.Tendsto.neg_mul_atTop, h_num ];
      · linarith;
      · exact Filter.Tendsto.inv_tendsto_nhdsGT_zero h_sqrt

lemma Theorem1.integrand_limit_of_gt (κ z : ℝ) (h : z < κ) :
    Filter.Tendsto (fun q => (1 - q) * (Theorem1.E (Theorem1.U κ q z))^2) (nhdsWithin 1 (Set.Iio 1)) (nhds ((κ - z)^2)) := by
      have h_U_atTop : Filter.Tendsto (fun q => (1 - q) * (Theorem1.U κ q z) ^ 2) (𝓝[<] 1) (nhds ((κ - z) ^ 2)) := by
        exact Theorem1.limit_one_sub_q_mul_U_sq κ z;
      have h_E_over_u_atTop : Filter.Tendsto (fun q => Theorem1.E (Theorem1.U κ q z) / Theorem1.U κ q z) (𝓝[<] 1) (nhds 1) := by
        have h_E_over_u_atTop : Filter.Tendsto (fun u => Theorem1.E u / u) Filter.atTop (nhds 1) := by
          exact Theorem1.E_asymp_atTop;
        refine h_E_over_u_atTop.comp ?_;
        exact Theorem1.tendsto_U_atTop κ z h;
      have h_combined : Filter.Tendsto (fun q => ((1 - q) * (Theorem1.U κ q z) ^ 2) * ((Theorem1.E (Theorem1.U κ q z) / Theorem1.U κ q z) ^ 2)) (𝓝[<] 1) (nhds ((κ - z) ^ 2 * 1 ^ 2)) := by
        simpa using h_U_atTop.mul ( h_E_over_u_atTop.pow 2 );
      convert h_combined.congr' _ using 2;
      · norm_num;
      · filter_upwards [ h_E_over_u_atTop.eventually_ne one_ne_zero ] with q hq ; by_cases h : Theorem1.U κ q z = 0 <;> simp_all +decide [ div_pow, mul_assoc, mul_comm, mul_left_comm ];
        exact Or.inl ( mul_div_cancel₀ _ ( pow_ne_zero 2 h ) )

lemma Theorem1.integrand_limit_of_lt (κ z : ℝ) (h : κ < z) :
    Filter.Tendsto (fun q => (1 - q) * (Theorem1.E (Theorem1.U κ q z))^2) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
      have h_combined : Filter.Tendsto (fun q => (1 - q) * (Theorem1.E (Theorem1.U κ q z))^2) (nhdsWithin 1 (Set.Iio 1)) (nhds (0 * 0)) := by
        have h_E_zero : Filter.Tendsto (fun q => Theorem1.E (Theorem1.U κ q z)) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
          have h_E_zero : Filter.Tendsto (fun q => Theorem1.E (Theorem1.U κ q z)) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
            have h_U_neg_inf : Filter.Tendsto (fun q => Theorem1.U κ q z) (nhdsWithin 1 (Set.Iio 1)) Filter.atBot := by
              exact Theorem1.tendsto_U_atBot κ z h
            convert Theorem1.tendsto_E_atBot.comp h_U_neg_inf using 1;
          convert h_E_zero using 1
        convert Filter.Tendsto.mul ( tendsto_const_nhds.sub ( Filter.tendsto_id.mono_left inf_le_left ) ) ( h_E_zero.pow 2 ) using 2 ; norm_num;
      convert h_combined using 1 ; ring

lemma Theorem1.integrand_limit_of_eq (κ z : ℝ) (h : κ = z) :
    Filter.Tendsto (fun q => (1 - q) * (Theorem1.E (Theorem1.U κ q z))^2) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
      have h_E_lim : Filter.Tendsto (fun q => Theorem1.E (Theorem1.U κ q z)) (nhdsWithin 1 (Set.Iio 1)) (nhds (Theorem1.E 0)) := by
        have h_E_lim : Filter.Tendsto (fun q => Theorem1.U κ q z) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
          have h_U_zero : Filter.Tendsto (fun q => (1 - Real.sqrt q) / Real.sqrt (1 - q)) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
            suffices h_suff : Filter.Tendsto (fun q => Real.sqrt (1 - q) / (1 + Real.sqrt q)) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) by
              refine' Filter.Tendsto.congr' _ h_suff;
              filter_upwards [ Ioo_mem_nhdsLT zero_lt_one ] with q hq using by rw [ div_eq_div_iff ] <;> nlinarith [ Real.sqrt_nonneg q, Real.sq_sqrt ( show 0 ≤ q by linarith [ hq.1 ] ), Real.sqrt_nonneg ( 1 - q ), Real.sq_sqrt ( show 0 ≤ 1 - q by linarith [ hq.2 ] ), hq.1, hq.2 ] ;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Filter.Tendsto.div ( Continuous.tendsto ( show Continuous fun q => Real.sqrt ( 1 - q ) from Real.continuous_sqrt.comp <| continuous_const.sub continuous_id' ) 1 ) ( Continuous.tendsto ( show Continuous fun q => 1 + Real.sqrt q from continuous_const.add <| Real.continuous_sqrt ) 1 ) <| by norm_num );
          convert h_U_zero.const_mul κ using 2 <;> push_cast [ h, Theorem1.U ] <;> ring;
        have h_E_cont : Continuous E := by
          simpa [Theorem1.E, UniformBoundOfG.E] using
            (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E);
        exact h_E_cont.continuousAt.tendsto.comp h_E_lim;
      convert Filter.Tendsto.mul ( tendsto_const_nhds.sub ( Filter.tendsto_id.mono_left inf_le_left ) ) ( h_E_lim.pow 2 ) using 2 ; norm_num

lemma Theorem1.tendsto_U_zero_of_eq (κ z : ℝ) (h : κ = z) :
    Filter.Tendsto (fun q => Theorem1.U κ q z) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
      suffices h_y : Filter.Tendsto (fun y => (1 - y) / Real.sqrt (1 - y^2)) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) by
        have h_subst : Filter.Tendsto (fun q => (1 - Real.sqrt q) / Real.sqrt (1 - q)) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
          have h_subst : Filter.Tendsto (fun q => (1 - Real.sqrt q) / Real.sqrt (1 - (Real.sqrt q)^2)) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
            refine h_y.comp <| Filter.Tendsto.inf ?_ ?_ <;> norm_num;
            · exact Continuous.tendsto' ( Real.continuous_sqrt ) _ _ ( by norm_num );
            · exact fun x hx => by rw [ Real.sqrt_lt' ] <;> linarith;
          refine' h_subst.congr' ( by filter_upwards [ Ioo_mem_nhdsLT zero_lt_one ] with q hq using by rw [ Real.sq_sqrt hq.1.le ] );
        convert h_subst.const_mul ( z : ℝ ) using 2 ; ring!;
        · unfold Theorem1.U; ring;
          rw [ h ] ; ring;
        · ring;
      suffices h_rationalize : Filter.Tendsto (fun y => Real.sqrt (1 - y^2) / (1 + y)) (𝓝[<] 1) (𝓝 0) by
        grind;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using ContinuousAt.tendsto ( show ContinuousAt ( fun y : ℝ => Real.sqrt ( 1 - y ^ 2 ) / ( 1 + y ) ) 1 by exact ContinuousAt.div ( Real.continuous_sqrt.continuousAt.comp <| continuousAt_const.sub <| continuousAt_id.pow 2 ) ( continuousAt_const.add continuousAt_id ) <| by norm_num ) )

lemma Theorem1.integrand_limit (κ z : ℝ) : Filter.Tendsto (fun q => (1 - q) * (Theorem1.E (Theorem1.U κ q z))^2) (nhdsWithin 1 (Set.Iio 1)) (nhds ((max (κ - z) 0)^2)) := by
  have h_cases : z < κ ∨ κ < z ∨ κ = z := by
    cases lt_trichotomy z κ <;> tauto;
  rcases h_cases with ( h | h | h );
  · simpa only [ max_eq_left ( sub_nonneg.mpr h.le ) ] using Theorem1.integrand_limit_of_gt κ z h;
  · convert Theorem1.integrand_limit_of_lt κ z h using 1 ; norm_num [ h.le ];
  · convert Theorem1.integrand_limit_of_eq _ _ _ using 1 <;> aesop

lemma Theorem1.integrand_bound (κ : ℝ) : Filter.Eventually (fun q => ∀ z, (1 - q) * (Theorem1.E (Theorem1.U κ q z))^2 ≤ 4 * (κ^2 + z^2) + 10) (nhdsWithin 1 (Set.Iio 1)) := by
  have := @Theorem1.E_le_max_u_zero_add_two;
  refine' Filter.eventually_of_mem ( Ioo_mem_nhdsLT zero_lt_one ) fun q hq z => _;
  have h_E_bound : Theorem1.E (Theorem1.U κ q z) ^ 2 ≤ (|Theorem1.U κ q z| + 2) ^ 2 := by
    exact
      pow_le_pow_left₀
        (le_of_lt (by
          simpa [Theorem1.E] using (DecreasingG.E_pos (Theorem1.U κ q z))))
        (le_trans (this _) (by
          cases max_cases (Theorem1.U κ q z) 0 <;>
            cases abs_cases (Theorem1.U κ q z) <;>
            linarith))
        _;
  have h_expand : (|Theorem1.U κ q z| + 2) ^ 2 ≤ 2 * (Theorem1.U κ q z) ^ 2 + 8 := by
    nlinarith only [ sq_nonneg ( |Theorem1.U κ q z| - 2 ), abs_mul_abs_self ( Theorem1.U κ q z ) ];
  have h_subst : (1 - q) * (Theorem1.U κ q z) ^ 2 ≤ 2 * κ ^ 2 + 2 * q * z ^ 2 := by
    rw [ show Theorem1.U κ q z = ( κ - Real.sqrt q * z ) / Real.sqrt ( 1 - q ) by rfl ];
    rw [ div_pow, Real.sq_sqrt ( by linarith [ hq.1, hq.2 ] ) ];
    rw [ mul_div_cancel₀ _ ( by linarith [ hq.1, hq.2 ] ) ];
    nlinarith only [ sq_nonneg ( κ + Real.sqrt q * z ), Real.mul_self_sqrt hq.1.le ];
  nlinarith [ hq.1, hq.2 ]

end AristotleLemmas

lemma tendsto_B_atOne_left (κ : ℝ) :
    Tendsto (fun q => B κ q) (𝓝[<] (1 : ℝ)) (𝓝 (Cκ κ)) := by
  convert MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _ using 1;
  rotate_left;
  infer_instance;
  use fun q z => ( 1 - q ) * ( Theorem1.E ( Theorem1.U κ q z ) ) ^ 2;
  use fun z => 4 * ( κ^2 + z^2 ) + 100;
  · refine' Filter.eventually_of_mem self_mem_nhdsWithin fun n hn => Measurable.aestronglyMeasurable _;
    refine' Measurable.const_mul _ _;
    refine' Measurable.pow_const _ _;
    refine' Measurable.div _ _;
    · refine' Measurable.div _ _;
      · refine' Measurable.exp _;
        exact Measurable.div_const ( Measurable.neg ( Measurable.pow_const ( by exact Measurable.div ( by exact measurable_const.sub ( by exact measurable_id'.const_mul _ ) ) ( by exact measurable_const.sqrt ) ) _ ) ) _;
      · exact measurable_const;
    ·
      have h_cont : Continuous (fun z => DecreasingG.Φbar (Theorem1.U κ n z)) := by
        have h_cont : Continuous (fun u => DecreasingG.Φbar u) := by
          simpa [UniformBoundOfG.Φbar] using
            (UniformBoundOfG.Φbar_continuous : Continuous UniformBoundOfG.Φbar);
        refine' h_cont.comp _;
        exact Continuous.div ( continuous_const.sub ( continuous_const.mul continuous_id' ) ) ( continuous_const ) fun x => ne_of_gt ( Real.sqrt_pos.mpr ( by linarith [ hn.out ] ) );
      exact h_cont.measurable;
  · filter_upwards [ Ioo_mem_nhdsLT zero_lt_one ] with q hq using Filter.Eventually.of_forall fun z => by rw [ Real.norm_of_nonneg ( mul_nonneg ( sub_nonneg.2 hq.2.le ) ( sq_nonneg _ ) ) ] ; exact (by
    have h_E_bound : ∀ u : ℝ, Theorem1.E u ≤ max u 0 + 2 := by
      exact Theorem1.E_le_max_u_zero_add_two;
    have h_subst : (1 - q) * (max (Theorem1.U κ q z) 0 + 2) ^ 2 ≤ 4 * (κ ^ 2 + z ^ 2) + 100 := by
      have h_U_bound : (max (Theorem1.U κ q z) 0 + 2) ^ 2 ≤ 4 * (κ ^ 2 + z ^ 2) / (1 - q) + 16 := by
        have h_U_bound : (Theorem1.U κ q z) ^ 2 ≤ 2 * (κ ^ 2 + z ^ 2) / (1 - q) := by
          rw [ Theorem1.U ];
          rw [ div_pow, Real.sq_sqrt ( by linarith [ hq.1, hq.2 ] ) ];
          gcongr;
          · linarith [ hq.1, hq.2 ];
          · nlinarith [ sq_nonneg ( κ + Real.sqrt q * z ), Real.mul_self_sqrt hq.1.le, hq.2 ];
        cases max_cases ( Theorem1.U κ q z ) 0 <;> push_cast [ * ] at * <;> ring_nf at * <;> nlinarith [ inv_mul_cancel₀ ( by linarith [ hq.1, hq.2 ] : ( 1 - q ) ≠ 0 ) ];
      nlinarith [ hq.1, hq.2, mul_div_cancel₀ ( 4 * ( κ ^ 2 + z ^ 2 ) ) ( by linarith [ hq.1, hq.2 ] : ( 1 - q ) ≠ 0 ) ];
    exact
      le_trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀
            (by
              exact
                le_of_lt
                  (by
                    simpa [Theorem1.E] using
                      (DecreasingG.E_pos (Theorem1.U κ q z))))
            (h_E_bound _)
            2)
          (by linarith [hq.1, hq.2]))
        h_subst);
  ·
    have h_poly_integrable : MeasureTheory.Integrable (fun z => z^2) Theorem1.γ := by
      have h_gauss_moment : ∫ z, z^2 * (Real.exp (-z^2 / 2)) ∂MeasureTheory.volume = Real.sqrt (2 * Real.pi) := by
        have := @integral_rpow_mul_exp_neg_mul_rpow;
        have h_polar : ∫ z in Set.Ioi 0, z^2 * Real.exp (-z^2 / 2) = Real.sqrt (2 * Real.pi) / 2 := by
          convert @this 2 2 ( 1 / 2 ) ( by norm_num ) ( by norm_num ) ( by norm_num ) using 1 <;> norm_num [ div_eq_inv_mul ];
          rw [ show ( 3 / 2 : ℝ ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one ( by norm_num ), Real.Gamma_one_half_eq ] ; ring ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg, Real.rpow_add ] ; ring;
          rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ] <;> norm_num ; ring ; norm_num [ ← Real.sqrt_eq_rpow ] ; ring;
        have h_even : ∫ z in Set.Iic 0, z^2 * Real.exp (-z^2 / 2) = Real.sqrt (2 * Real.pi) / 2 := by
          rw [ ← h_polar, ← neg_zero, ← integral_comp_neg_Iic ] ; norm_num;
        convert congr_arg₂ ( · + · ) h_even h_polar using 1;
        · rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
          · exact ( by contrapose! h_even; rw [ MeasureTheory.integral_undef h_even ] ; positivity );
          · exact ( by contrapose! h_polar; rw [ MeasureTheory.integral_undef h_polar ] ; positivity );
        · ring;
      have h_gauss_moment : ∫ z, z^2 * (Real.exp (-z^2 / 2)) / Real.sqrt (2 * Real.pi) ∂MeasureTheory.volume = 1 := by
        rw [ MeasureTheory.integral_div, h_gauss_moment, div_self ( by positivity ) ];
      contrapose! h_gauss_moment;
      rw [ MeasureTheory.integral_undef ] <;> norm_num [ h_gauss_moment ];
      convert h_gauss_moment using 1;
      unfold Theorem1.γ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ] ;
      rw [ ProbabilityTheory.gaussianReal ] ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ];
      rw [ MeasureTheory.integrable_withDensity_iff ];
      · norm_num [ ProbabilityTheory.gaussianPDF, ProbabilityTheory.gaussianPDFReal ] ; ring;
        norm_num [ mul_assoc, mul_comm, mul_left_comm, ENNReal.toReal_ofReal ( Real.exp_nonneg _ ) ];
      · exact Measurable.ennreal_ofReal ( by exact Measurable.mul ( by exact measurable_const ) ( by exact Real.continuous_exp.measurable.comp ( by exact Continuous.measurable ( by continuity ) ) ) );
      · norm_num [ ProbabilityTheory.gaussianPDF ];
    apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.const_mul, MeasureTheory.integrable_const ];
  · exact Filter.Eventually.of_forall fun x => Theorem1.integrand_limit κ x |> Filter.Tendsto.mono_left <| nhdsWithin_mono _ <| Set.Iio_subset_Iio <| by norm_num;
  · exact funext fun q => by rw [ Theorem1.B ] ; simp +decide [ mul_assoc, MeasureTheory.integral_const_mul ] ;

/-!
The strict monotonicity of `B` is the main technical ingredient.

Blueprint: combine
- derivative formula `B'(t) = 𝔼[g(U_t)]` (`perceptronFixed/derivative_of_B/derivative_B.lean`)
- `g` strictly decreasing on `[0,∞)` (`perceptronFixed/decreasing_g/decreasing_g.lean`)
- uniform bound on `(-∞,0]` (`perceptronFixed/uniform_bound_of_g/uniform_bound_of_g.lean`)
to show `B'(t) < 0` for `t ∈ (0,1)`, hence strict decrease on `[0,1)`.
-/

noncomputable section AristotleLemmas

/-
The function g defined in MillsBlueprint is equal to the function g defined in DecreasingG.
-/
lemma bridge_g_eq (u : ℝ) : MillsBlueprint.Proof.g u = DecreasingG.g u := by
  unfold MillsBlueprint.Proof.g DecreasingG.g MillsBlueprint.Proof.E DecreasingG.E MillsBlueprint.Proof.φ DecreasingG.φ MillsBlueprint.Proof.Φbar DecreasingG.Φbar; ring;
  rw [ show MillsBlueprint.Proof.Φ u = ∫ x in Set.Iic u, DecreasingG.φ x from ?_ ];
  · rw [ show ∫ x in Set.Ici u, DecreasingG.φ x = 1 - ∫ x in Set.Iic u, DecreasingG.φ x from ?_ ];
    have h_gauss_total : ∫ x, (Real.exp (-(x ^ 2) / 2)) / Real.sqrt (2 * Real.pi) = 1 := by
      rw [ MeasureTheory.integral_div, div_eq_iff ];
      · simpa [ div_eq_inv_mul ] using integral_gaussian ( 1 / 2 );
      · positivity;
    rw [ ← h_gauss_total, MeasureTheory.integral_Ici_eq_integral_Ioi, eq_sub_iff_add_eq', ← MeasureTheory.setIntegral_union ] <;> norm_num;
    · exact congr_arg _ ( funext fun x => by rw [ show DecreasingG.φ x = Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi ) by rfl ] ; norm_num );
    · exact MeasureTheory.Integrable.integrableOn ( by exact MeasureTheory.integrable_of_integral_eq_one h_gauss_total );
    · exact MeasureTheory.Integrable.integrableOn ( MeasureTheory.integrable_of_integral_eq_one h_gauss_total );
  · unfold MillsBlueprint.Proof.Φ DecreasingG.φ;
    unfold MillsBlueprint.Proof.φ; norm_num [ div_eq_inv_mul ] ;

/-
The function E defined in MillsBlueprint is equal to the function E defined in DecreasingG.
-/
lemma bridge_E_eq (u : ℝ) : MillsBlueprint.Proof.E u = DecreasingG.E u := by
  have h_gauss_total : ∫ z, (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-z^2 / 2) = 1 := by
    rw [ MeasureTheory.integral_const_mul ];
    rw [ one_div, inv_mul_eq_div, div_eq_iff ( by positivity ) ];
    simpa [ div_eq_inv_mul ] using integral_gaussian ( 1 / 2 );
  have h_gauss_split : ∫ z in Set.Iic u, (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-z^2 / 2) = 1 - ∫ z in Set.Ioi u, (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-z^2 / 2) := by
    rw [ ← h_gauss_total, eq_sub_iff_add_eq, ← MeasureTheory.setIntegral_union ] <;> norm_num;
    · norm_num [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ] at * ; aesop;
    · exact MeasureTheory.Integrable.integrableOn ( by exact MeasureTheory.Integrable.const_mul ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) _ );
    · exact MeasureTheory.Integrable.integrableOn ( by exact MeasureTheory.Integrable.const_mul ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) _ );
  convert congr_arg ( fun x : ℝ => ( 1 / Real.sqrt ( 2 * Real.pi ) ) * Real.exp ( -u ^ 2 / 2 ) / ( 1 - x ) ) h_gauss_split using 1 ; ring!;
  unfold DecreasingG.E; ring;
  unfold DecreasingG.φ DecreasingG.Φbar; norm_num [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm, Real.pi_pos.le ] ;
  unfold DecreasingG.φ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_Ici_eq_integral_Ioi ] ;

/-
The function B defined in Theorem1 is equal to the function B defined in MillsBlueprint (with appropriate parameters).
-/
lemma bridge_B_eq (κ q : ℝ) :
    Theorem1.B κ q = MillsBlueprint.Proof.B (P := Theorem1.γ) (Z := id) κ q := by
  simp [Theorem1.B, MillsBlueprint.Proof.B];
  have h_E_eq : ∀ u, Theorem1.E u = MillsBlueprint.Proof.E u := by
    intro u
    simpa [Theorem1.E] using (bridge_E_eq u).symm;
  unfold Theorem1.Expect MillsBlueprint.Proof.𝔼; aesop;

/-
The derivative of B(κ, q) is the expectation of g(U(κ, q, z)).
-/
lemma deriv_B_eq (κ : ℝ) (q : ℝ) (hq : q ∈ Set.Ioo 0 1) :
    deriv (fun q => Theorem1.B κ q) q = Theorem1.Expect (fun z => DecreasingG.g (Theorem1.U κ q z)) := by
  have h_deriv_B : deriv (fun q => MillsBlueprint.Proof.B (P := Theorem1.γ) (Z := id) κ q) q = MillsBlueprint.Proof.𝔼 Theorem1.γ (fun z => MillsBlueprint.Proof.g (MillsBlueprint.Proof.U id κ q z)) := by
    apply MillsBlueprint.Proof.deriv_B_eq_expect_g
    all_goals generalize_proofs at *;
    · exact MeasureTheory.Measure.map_id;
    · exact hq;
  convert h_deriv_B using 1;
  · exact congr_arg ( deriv · q ) ( funext fun q => bridge_B_eq κ q );
  · congr! 1;
    exact funext fun x => bridge_g_eq _ ▸ rfl

/-
g(0) is strictly less than -1/18.
-/
lemma g0_bound : DecreasingG.g 0 < -1 / 18 := by
  have h_goal : (12 : ℝ) / Real.pi ^ 2 - 4 / Real.pi < -1 / 18 := by
    have h_pi_approx : 3.1415 < Real.pi ∧ Real.pi < 3.1416 := by
      exact ⟨Real.pi_gt_d4, Real.pi_lt_d4⟩;
    rw [ div_sub_div, div_lt_iff₀ ] <;> nlinarith [ Real.pi_gt_three, mul_pos ( sub_pos_of_lt h_pi_approx.1 ) ( sub_pos_of_lt h_pi_approx.2 ) ];
  convert h_goal using 1;
  convert DecreasingG.g0_eq using 1

/-
For non-negative u, g(u) is less than or equal to -1/18.
-/
lemma g_le_neg_one_div_18_of_nonneg {u : ℝ} (hu : 0 ≤ u) : DecreasingG.g u ≤ -1 / 18 := by
  have h_g_le_g0 : ∀ u, 0 ≤ u → DecreasingG.g u ≤ DecreasingG.g 0 := by
    intro u hu
    exact DecreasingG.g_le_g0_of_nonneg hu;
  exact le_trans ( h_g_le_g0 u hu ) ( le_of_lt ( g0_bound ) )

/-
Arithmetic bound for the expectation proof.
-/
lemma arithmetic_bound (p : ℝ) (hp : 1/2 ≤ p) (hp1 : p ≤ 1) :
    DecreasingG.g 0 * p + (1 / 18) * (1 - p) < 0 := by
  have hg0 : DecreasingG.g 0 < -1 / 18 := by
    exact g0_bound.trans_le <| by norm_num;
  nlinarith

/-
The probability that U is non-negative is at least 1/2.
-/
lemma gamma_U_nonneg_ge_half (κ : ℝ) (hκ : 0 ≤ κ) (q : ℝ) (hq : q ∈ Set.Ioo 0 1) :
    (Theorem1.γ {z | Theorem1.U κ q z ≥ 0}).toReal ≥ 1 / 2 := by
  have h_set_eq : {z | Theorem1.U κ q z ≥ 0} = Set.Iic (κ / Real.sqrt q) := by
    ext z
    simp [Theorem1.U];
    rw [ le_div_iff₀ ( Real.sqrt_pos.mpr hq.1 ), le_div_iff₀ ( Real.sqrt_pos.mpr ( sub_pos.mpr hq.2 ) ) ] ; ring_nf;
    grind;
  have h_measure_eq : (Theorem1.γ (Set.Iic (κ / Real.sqrt q))).toReal = ∫ x in Set.Iic (κ / Real.sqrt q), (Real.exp (-x^2 / 2)) / Real.sqrt (2 * Real.pi) := by
    rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
    · unfold Theorem1.γ;
      unfold ProbabilityTheory.gaussianReal;
      norm_num [ ProbabilityTheory.gaussianPDF ];
      norm_num [ ProbabilityTheory.gaussianPDFReal ];
      norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ENNReal.ofReal_mul ( Real.exp_nonneg _ ), ENNReal.ofReal_inv_of_pos ( Real.sqrt_pos.mpr zero_lt_two ), ENNReal.ofReal_inv_of_pos ( Real.sqrt_pos.mpr Real.pi_pos ) ];
    · exact Filter.Eventually.of_forall fun x => by positivity;
    · exact Continuous.aestronglyMeasurable ( by continuity );
  have h_measure_ge_half : ∫ x in Set.Iic (κ / Real.sqrt q), (Real.exp (-x^2 / 2)) / Real.sqrt (2 * Real.pi) ≥ ∫ x in Set.Iic 0, (Real.exp (-x^2 / 2)) / Real.sqrt (2 * Real.pi) := by
    refine' MeasureTheory.setIntegral_mono_set _ _ _;
    · exact MeasureTheory.Integrable.integrableOn ( by exact MeasureTheory.integrable_of_integral_eq_one ( by rw [ MeasureTheory.integral_div, ] ; rw [ div_eq_iff ( by positivity ) ] ; have := integral_gaussian ( 1 / 2 ) ; norm_num [ div_eq_inv_mul ] at *; linarith ) );
    · exact Filter.Eventually.of_forall fun x => by positivity;
    · exact MeasureTheory.ae_of_all _ fun x hx => le_trans hx <| div_nonneg hκ <| Real.sqrt_nonneg _;
  have h_gauss_integral : ∫ x in Set.Iic 0, (Real.exp (-x^2 / 2)) / Real.sqrt (2 * Real.pi) = 1 / 2 := by
    have h_gauss_integral : ∫ x in Set.Iic 0, (Real.exp (-x^2 / 2)) = Real.sqrt (2 * Real.pi) / 2 := by
      have := integral_gaussian_Ioi ( 1 / 2 ) ; norm_num [ div_eq_inv_mul ] at * ; rw [ ← neg_zero, ← integral_comp_neg_Iic ] at * ; norm_num at * ; linarith;
    rw [ MeasureTheory.integral_div, h_gauss_integral, div_eq_iff ] <;> ring ; positivity;
  aesop

/-
If U is non-negative, g(U) is less than or equal to g(0).
-/
lemma g_U_le_g0 (κ : ℝ) (q : ℝ) (z : ℝ) (hz : Theorem1.U κ q z ≥ 0) :
    DecreasingG.g (Theorem1.U κ q z) ≤ DecreasingG.g 0 := by
  exact ( DecreasingG.g_strictAntiOn_Ici.le_iff_ge ( by aesop ) ( by aesop ) ) |>.2 hz

/-
g(u) is bounded by a polynomial of degree 4.
-/
lemma g_bound_poly : ∃ C, ∀ u, |DecreasingG.g u| ≤ C * (1 + |u|^4) := by
  have h_bound : ∀ u : ℝ, |(DecreasingG.E u) ^ 2 * (3 * (DecreasingG.E u) ^ 2 - 4 * u * (DecreasingG.E u) + u ^ 2 - 2)| ≤ (DecreasingG.E u) ^ 2 * (3 * (DecreasingG.E u) ^ 2 + 4 * |u| * (DecreasingG.E u) + |u| ^ 2 + 2) := by
    intro u; rw [ abs_mul, abs_of_nonneg ( sq_nonneg _ ) ] ; exact mul_le_mul_of_nonneg_left ( abs_le.mpr ⟨ by cases abs_cases u <;> nlinarith [ show 0 ≤ DecreasingG.E u from le_of_lt ( DecreasingG.E_pos _ ) ], by cases abs_cases u <;> nlinarith [ show 0 ≤ DecreasingG.E u from le_of_lt ( DecreasingG.E_pos _ ) ] ⟩ ) ( sq_nonneg _ ) ;
  have h_E_bound : ∃ C : ℝ, ∀ u : ℝ, |DecreasingG.E u| ≤ |u| + C := by
    use MillsBlueprint.Proof.C_mills;
    intro u
    have h_E_le : DecreasingG.E u ≤ |u| + MillsBlueprint.Proof.C_mills := by
      convert MillsBlueprint.Proof.E_le_abs_add_C u using 1;
      simpa using (bridge_E_eq u).symm
    have h_E_ge : -|u| - MillsBlueprint.Proof.C_mills ≤ DecreasingG.E u := by
      exact le_trans ( by linarith [ abs_nonneg u, show 0 ≤ MillsBlueprint.Proof.C_mills from by exact le_of_lt <| by exact zero_lt_one.trans_le <| le_max_right _ _ ] ) ( show 0 ≤ DecreasingG.E u from by exact le_of_lt <| by exact DecreasingG.E_pos u )
    exact abs_le.mpr ⟨by linarith, by linarith⟩;
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u : ℝ, |DecreasingG.E u| ≤ |u| + C := h_E_bound;
  have h_subst : ∀ u : ℝ, |(DecreasingG.E u) ^ 2 * (3 * (DecreasingG.E u) ^ 2 - 4 * u * (DecreasingG.E u) + u ^ 2 - 2)| ≤ (|u| + C) ^ 2 * (3 * (|u| + C) ^ 2 + 4 * |u| * (|u| + C) + |u| ^ 2 + 2) := by
    intro u
    specialize h_bound u
    specialize hC u;
    refine le_trans h_bound ?_;
    gcongr;
    any_goals nlinarith [ abs_le.mp hC, abs_nonneg u ];
    · nlinarith only [ sq_nonneg ( |u| + 2 * DecreasingG.E u ), abs_nonneg u, show 0 ≤ DecreasingG.E u from le_of_lt ( DecreasingG.E_pos u ) ];
    · exact le_of_lt ( DecreasingG.E_pos u );
    · exact le_of_lt ( DecreasingG.E_pos u );
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ u : ℝ, (|u| + C) ^ 2 * (3 * (|u| + C) ^ 2 + 4 * |u| * (|u| + C) + |u| ^ 2 + 2) ≤ D * (1 + |u| ^ 4) := by
    exact ⟨ 100 + C ^ 2 * 100 + C ^ 4 * 100, fun u => by nlinarith only [ sq_nonneg ( |u| ^ 2 - 1 ), sq_nonneg ( |u| - C ), sq_nonneg ( C ^ 2 - 1 ), abs_nonneg u, sq_nonneg ( |u| * C ), sq_nonneg ( |u| ^ 2 * C ), sq_nonneg ( |u| ^ 3 ), sq_nonneg ( |u| ^ 4 ) ] ⟩;
  exact ⟨ D, fun u => le_trans ( h_subst u ) ( hD u ) ⟩

/-
g(U) is integrable with respect to the Gaussian measure.
-/
lemma integrable_g_U (κ : ℝ) (q : ℝ) (hq : q ∈ Set.Ioo 0 1) :
    MeasureTheory.Integrable (fun z => DecreasingG.g (Theorem1.U κ q z)) Theorem1.γ := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ u, |DecreasingG.g u| ≤ C * (1 + |u|^4) := g_bound_poly;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun z => C * ( 1 + |( κ - Real.sqrt q * z ) / Real.sqrt ( 1 - q )| ^ 4 );
  · refine' MeasureTheory.Integrable.const_mul _ _;
    refine' MeasureTheory.Integrable.add _ _;
    · norm_num [ Theorem1.γ ];
    ·
      have h_poly_integrable : ∀ n : ℕ, MeasureTheory.Integrable (fun z => z ^ n) Theorem1.γ := by
        intro n
        have h_gauss_moment : MeasureTheory.Integrable (fun z => z^n) (MeasureTheory.Measure.map (fun z => z) (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))) := by
          simp +decide [ ProbabilityTheory.gaussianReal ];
          have h_gauss_moment : MeasureTheory.Integrable (fun z => z^n * Real.exp (-z^2 / 2)) MeasureTheory.volume := by
            have := @integrable_rpow_mul_exp_neg_mul_sq;
            convert @this ( 1 / 2 ) ( by norm_num ) ( n : ℝ ) ( by linarith ) using 3 ; ring;
            · norm_cast;
            · ring;
          rw [ MeasureTheory.integrable_withDensity_iff ];
          · convert h_gauss_moment.div_const ( Real.sqrt ( 2 * Real.pi ) ) using 2 ; norm_num [ ProbabilityTheory.gaussianPDF ] ; ring;
            rw [ ProbabilityTheory.gaussianPDFReal ] ; norm_num [ Real.exp_neg, mul_assoc, mul_comm, mul_left_comm, Real.sqrt_ne_zero'.mpr Real.pi_pos ];
            rw [ ENNReal.toReal_ofReal ( by positivity ) ] ; rw [ ← Real.exp_neg ] ; ring ; norm_num;
          · exact ProbabilityTheory.measurable_gaussianPDF (μ := (0 : ℝ)) (v := (1 : ℝ≥0));
          · norm_num [ ProbabilityTheory.gaussianPDF ];
        aesop;
      convert MeasureTheory.Integrable.abs ( h_poly_integrable 4 |> fun h => h.const_mul ( ( Real.sqrt ( 1 - q ) ) ⁻¹ ^ 4 ) |> fun h => h.const_mul ( ( -Real.sqrt q ) ^ 4 ) |> fun h => h.add ( h_poly_integrable 3 |> fun h => h.const_mul ( ( Real.sqrt ( 1 - q ) ) ⁻¹ ^ 4 ) |> fun h => h.const_mul ( ( -Real.sqrt q ) ^ 3 * κ * 4 ) |> fun h => h.add ( h_poly_integrable 2 |> fun h => h.const_mul ( ( Real.sqrt ( 1 - q ) ) ⁻¹ ^ 4 ) |> fun h => h.const_mul ( ( -Real.sqrt q ) ^ 2 * κ ^ 2 * 6 ) |> fun h => h.add ( h_poly_integrable 1 |> fun h => h.const_mul ( ( Real.sqrt ( 1 - q ) ) ⁻¹ ^ 4 ) |> fun h => h.const_mul ( ( -Real.sqrt q ) * κ ^ 3 * 4 ) |> fun h => h.add ( h_poly_integrable 0 |> fun h => h.const_mul ( ( Real.sqrt ( 1 - q ) ) ⁻¹ ^ 4 ) |> fun h => h.const_mul ( κ ^ 4 ) ) ) ) ) ) using 1 ; ring;
      ext; norm_num; ring;
      rw [ ← abs_pow ] ; ring;
  · have h_measurable : Measurable (fun u => DecreasingG.g u) := by
      exact Continuous.measurable ( UniformBoundOfG.g_continuous );
    exact h_measurable.aestronglyMeasurable.comp_aemeasurable ( by exact Measurable.aemeasurable ( by exact Measurable.div_const ( by exact Measurable.sub ( measurable_const ) ( measurable_const.mul measurable_id' ) ) _ ) );
  · exact Filter.Eventually.of_forall fun x => hC _

/-
The function |a + bz|^n is integrable with respect to the standard Gaussian measure.
-/
/-(legacy proof; disabled due to timeouts in Lean 4.26)
lemma integrable_abs_pow_linear (n : ℕ) (a b : ℝ) :
    MeasureTheory.Integrable (fun z => |a + b * z| ^ n) Theorem1.γ := by
  -- The function |a + b * z|^n is a polynomial in z of degree n, which is integrable with respect to the standard Gaussian measure.
  have h_poly_integrable : ∀ k : ℕ, MeasureTheory.Integrable (fun z => |z|^k) (Theorem1.γ) := by
    intro k
    have h_gauss_moment : ∫ z, |z|^k ∂Theorem1.γ = (2 ^ (k / 2 : ℝ)) * (Real.Gamma ((k + 1) / 2)) / Real.sqrt Real.pi := by
      have := @integral_rpow_mul_exp_neg_mul_rpow;
      -- We'll use the fact that |z|^k is integrable with respect to the Gaussian measure.
      have h_integrable : ∫ z, |z|^k ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))) = 2 * ∫ z in Set.Ioi 0, z^k * (Real.exp (-z^2 / 2)) / Real.sqrt (2 * Real.pi) := by
        have h_integrable : ∫ z, |z|^k ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))) = (∫ z in Set.Ioi 0, |z|^k * (Real.exp (-z^2 / 2)) / Real.sqrt (2 * Real.pi)) + (∫ z in Set.Iio 0, |z|^k * (Real.exp (-z^2 / 2)) / Real.sqrt (2 * Real.pi)) := by
          rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
          · rw [ show ( Set.Ioi 0 ∪ Set.Iio 0 : Set ℝ ) = Set.univ \ { 0 } by ext x; by_cases hx : x = 0 <;> aesop ] ; rw [ MeasureTheory.integral_diff ] <;> norm_num;
            · rw [ ProbabilityTheory.gaussianReal ];
              norm_num [ ProbabilityTheory.gaussianPDF ];
              rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
              · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
                · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ] <;> norm_num [ ProbabilityTheory.gaussianPDF ];
                  · norm_num [ ProbabilityTheory.gaussianPDFReal ];
                    congr with x ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ENNReal.ofReal_mul, Real.sqrt_nonneg ];
                    rw [ ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_mul ( by positivity ) ] ; norm_num [ ENNReal.ofReal_inv_of_pos, Real.sqrt_pos.mpr Real.pi_pos ];
                  · exact Measurable.ennreal_ofReal ( by exact Measurable.mul ( by exact measurable_const ) ( by exact Real.continuous_exp.measurable.comp ( by exact Continuous.measurable ( by continuity ) ) ) );
                  · exact Measurable.pow_const ( Measurable.ennreal_ofReal ( measurable_norm ) ) _;
                · exact Filter.Eventually.of_forall fun x => by positivity;
                · exact Continuous.aestronglyMeasurable ( by continuity );
              · exact Filter.Eventually.of_forall fun x => by positivity;
              · exact Continuous.aestronglyMeasurable ( by continuity );
            · have h_integrable : MeasureTheory.Integrable (fun x => |x|^k * Real.exp (-x^2 / 2)) MeasureTheory.MeasureSpace.volume := by
                have := @integrable_rpow_mul_exp_neg_mul_sq;
                specialize @this ( 1 / 2 ) ( by norm_num ) ( k : ℝ ) ( by linarith );
                convert this.norm using 2 ; norm_num [ div_eq_inv_mul ];
              exact h_integrable.div_const _;
          · have h_gauss_moment : MeasureTheory.IntegrableOn (fun z => z^k * (Real.exp (-z^2 / 2))) (Set.Ioi 0) := by
              specialize @this 2 k ( 1 / 2 ) ; norm_num at this;
              contrapose! this;
              exact ⟨ by linarith, by rw [ MeasureTheory.integral_undef ( by simpa [ div_eq_inv_mul ] using this ) ] ; positivity ⟩;
            exact MeasureTheory.Integrable.div_const ( h_gauss_moment.congr_fun ( fun x hx => by rw [ abs_of_nonneg hx.out.le ] ) measurableSet_Ioi ) _;
          · have h_gauss_moment : MeasureTheory.IntegrableOn (fun z => |z|^k * Real.exp (-z^2 / 2)) (Set.Iio 0) := by
              have h_gauss_moment : MeasureTheory.IntegrableOn (fun z => |z|^k * Real.exp (-z^2 / 2)) (Set.Ioi 0) := by
                have h_gauss_moment : MeasureTheory.IntegrableOn (fun z => z^k * Real.exp (-z^2 / 2)) (Set.Ioi 0) := by
                  specialize @this 2 k ( 1 / 2 ) ; norm_num at this;
                  contrapose! this;
                  exact ⟨ by linarith, by rw [ MeasureTheory.integral_undef ( by simpa [ div_eq_inv_mul ] using this ) ] ; positivity ⟩;
                exact h_gauss_moment.congr_fun ( fun x hx => by rw [ abs_of_pos hx.out ] ) measurableSet_Ioi;
              convert h_gauss_moment.comp_neg using 1 ; norm_num [ Set.indicator ] ; ring ; aesop;
            exact h_gauss_moment.div_const _;
        -- Since $|z|^k$ is even, we can simplify the integral over $(-\infty, 0)$ to the integral over $(0, \infty)$.
        have h_even : ∫ z in Set.Iio 0, |z|^k * (Real.exp (-z^2 / 2)) / Real.sqrt (2 * Real.pi) = ∫ z in Set.Ioi 0, |z|^k * (Real.exp (-z^2 / 2)) / Real.sqrt (2 * Real.pi) := by
          rw [ ← MeasureTheory.integral_Iic_eq_integral_Iio ] ; rw [ ← neg_zero, ← integral_comp_neg_Iic ] ; norm_num;
        rw [ h_integrable, h_even, two_mul ];
        rw [ two_mul, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ abs_of_pos hx.out ] ];
      have := @this 2 k ( 1 / 2 ) ?_ ?_ ?_ <;> norm_num at *;
      · simp_all +decide [ div_eq_inv_mul, MeasureTheory.integral_div ];
        rw [ MeasureTheory.integral_const_mul, this ] ; ring ; norm_num [ Real.sqrt_ne_zero'.mpr Real.pi_pos ];
        norm_num [ Real.rpow_add, Real.rpow_neg, Real.div_rpow ] ; ring;
        norm_num [ ← Real.sqrt_eq_rpow, mul_assoc, mul_comm, mul_left_comm ];
      · linarith;
    exact ( by contrapose! h_gauss_moment; rw [ MeasureTheory.integral_undef h_gauss_moment ] ; positivity );
  -- By the properties of the Gaussian measure, we can bound |a + bz|^n by a polynomial in |z|.
  have h_bound : ∀ z : ℝ, |a + b * z|^n ≤ ∑ k ∈ Finset.range (n + 1), Nat.choose n k * |a|^(n - k) * |b|^k * |z|^k := by
    intro z
    have h_bound : |a + b * z|^n ≤ (∑ k ∈ Finset.range (n + 1), Nat.choose n k * |a|^(n - k) * |b * z|^k) := by
      have h_bound : |a + b * z|^n ≤ (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * |a|^(n - k) * |b * z|^k) := by
        have h_triangle : |a + b * z| ≤ |a| + |b * z| := by
          simpa using abs_add a (b * z)
        exact le_trans ( pow_le_pow_left₀ ( abs_nonneg _ ) h_triangle _ ) ( by rw [ add_comm, add_pow ] ; exact Finset.sum_le_sum fun _ _ => by ring_nf; norm_num );
      convert h_bound using 1;
    simpa only [ mul_pow, abs_mul, mul_assoc ] using h_bound;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  exacts [ fun z => ∑ k ∈ Finset.range ( n + 1 ), ( n.choose k : ℝ ) * |a| ^ ( n - k ) * |b| ^ k * |z| ^ k, by exact MeasureTheory.integrable_finset_sum _ fun k hk => by exact MeasureTheory.Integrable.const_mul ( h_poly_integrable k ) _, by exact Continuous.aestronglyMeasurable ( by continuity ), Filter.Eventually.of_forall fun z => by simpa using h_bound z ]
-/

lemma integrable_abs_pow_linear (n : ℕ) (a b : ℝ) :
    MeasureTheory.Integrable (fun z => |a + b * z| ^ n) Theorem1.γ := by
  by_cases hn : n = 0
  · subst hn
    simpa using (integrable_const (μ := Theorem1.γ) (c := (1 : ℝ)))
  · have hid : MeasureTheory.MemLp (fun z : ℝ => z) (p := (n : ℝ≥0)) Theorem1.γ := by
      simpa [Theorem1.γ] using
        ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (n : ℝ≥0))
    have hmul : MeasureTheory.MemLp (fun z : ℝ => b * z) (p := (n : ℝ≥0)) Theorem1.γ :=
      hid.const_mul b
    have hconst : MeasureTheory.MemLp (fun _z : ℝ => a) (p := (n : ℝ≥0)) Theorem1.γ := by
      simpa using (MeasureTheory.memLp_const (μ := Theorem1.γ) (p := (n : ℝ≥0∞)) (c := a))
    have hlin : MeasureTheory.MemLp (fun z : ℝ => a + b * z) (p := (n : ℝ≥0)) Theorem1.γ := by
      simpa using (hconst.add hmul)
    have hnorm : MeasureTheory.Integrable (fun z : ℝ => ‖a + b * z‖ ^ ((n : ℝ≥0∞)).toReal) Theorem1.γ := by
      have hmem1 :
          MeasureTheory.MemLp (fun z : ℝ => ‖a + b * z‖ ^ ((n : ℝ≥0∞)).toReal) 1 Theorem1.γ := by
        refine hlin.norm_rpow ?_ ?_
        · simpa [hn]
        · simp
      exact (MeasureTheory.memLp_one_iff_integrable).1 hmem1
    simpa [Real.norm_eq_abs, Real.rpow_natCast] using hnorm

/-
The integral of g(U) over the set where U is non-negative is bounded by g(0) times the measure of that set.
-/
lemma integral_g_U_pos_le (κ : ℝ) (hκ : 0 ≤ κ) (q : ℝ) (hq : q ∈ Set.Ioo 0 1) :
    ∫ z in {z | Theorem1.U κ q z ≥ 0}, DecreasingG.g (Theorem1.U κ q z) ∂Theorem1.γ ≤
    DecreasingG.g 0 * (Theorem1.γ {z | Theorem1.U κ q z ≥ 0}).toReal := by
  have hs : MeasurableSet {z : ℝ | Theorem1.U κ q z ≥ 0} := by
    have hU : Measurable (fun z : ℝ => Theorem1.U κ q z) := by
      simpa [Theorem1.U] using
        (by
          fun_prop :
            Measurable (fun z : ℝ => (κ - Real.sqrt q * z) / Real.sqrt (1 - q)))
    simpa [Set.preimage, ge_iff_le] using (measurableSet_Ici.preimage hU)
  have hf :
      MeasureTheory.IntegrableOn (fun z => DecreasingG.g (Theorem1.U κ q z))
        {z | Theorem1.U κ q z ≥ 0} Theorem1.γ :=
    (integrable_g_U κ q hq).integrableOn
  have hg :
      MeasureTheory.IntegrableOn (fun _z : ℝ => DecreasingG.g 0)
        {z | Theorem1.U κ q z ≥ 0} Theorem1.γ :=
    (integrable_const (μ := Theorem1.γ) (c := DecreasingG.g 0)).integrableOn
  have hmono :=
      MeasureTheory.setIntegral_mono_on hf hg hs (fun z hz => by
        have hz0 : 0 ≤ Theorem1.U κ q z := by
          simpa [ge_iff_le] using hz
        exact DecreasingG.g_le_g0_of_nonneg hz0)
  simpa [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    hmono

/-
The integral of g(U) over the set where U is negative is bounded by 1/18 times the measure of that set.
-/
lemma integral_g_U_neg_le (κ : ℝ) (hκ : 0 ≤ κ) (q : ℝ) (hq : q ∈ Set.Ioo 0 1) :
    ∫ z in {z | Theorem1.U κ q z < 0}, DecreasingG.g (Theorem1.U κ q z) ∂Theorem1.γ ≤
    (1 / 18) * (Theorem1.γ {z | Theorem1.U κ q z < 0}).toReal := by
  have hs : MeasurableSet {z : ℝ | Theorem1.U κ q z < 0} := by
    have hU : Measurable (fun z : ℝ => Theorem1.U κ q z) := by
      simpa [Theorem1.U] using
        (by
          fun_prop :
            Measurable (fun z : ℝ => (κ - Real.sqrt q * z) / Real.sqrt (1 - q)))
    simpa [Set.preimage] using (measurableSet_Iio.preimage hU)
  have hf :
      MeasureTheory.IntegrableOn (fun z => DecreasingG.g (Theorem1.U κ q z))
        {z | Theorem1.U κ q z < 0} Theorem1.γ :=
    (integrable_g_U κ q hq).integrableOn
  have hg :
      MeasureTheory.IntegrableOn (fun _z : ℝ => (1 : ℝ) / 18)
        {z | Theorem1.U κ q z < 0} Theorem1.γ :=
    (integrable_const (μ := Theorem1.γ) (c := (1 : ℝ) / 18)).integrableOn
  have hmono :=
      MeasureTheory.setIntegral_mono_on hf hg hs (fun z hz => by
        have hz0 : Theorem1.U κ q z ≤ 0 := hz.le
        exact UniformBoundOfG.g_le_one_div_18 hz0)
  simpa [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    hmono

/-
The integral of g(U) over the set where U is non-negative is bounded by g(0) times the measure of that set.
-/
lemma integral_g_U_pos_le_v2 (κ : ℝ) (hκ : 0 ≤ κ) (q : ℝ) (hq : q ∈ Set.Ioo 0 1) :
    ∫ z in {z | Theorem1.U κ q z ≥ 0}, DecreasingG.g (Theorem1.U κ q z) ∂Theorem1.γ ≤
    DecreasingG.g 0 * (Theorem1.γ {z | Theorem1.U κ q z ≥ 0}).toReal := by
      convert integral_g_U_pos_le κ hκ q hq using 1

/-
The expectation of g(U) is negative.
-/
lemma expect_g_U_neg (κ : ℝ) (hκ : 0 ≤ κ) (q : ℝ) (hq : q ∈ Set.Ioo 0 1) :
    Theorem1.Expect (fun z => DecreasingG.g (Theorem1.U κ q z)) < 0 := by
      have h_exp_neg : ∫ z in {z | Theorem1.U κ q z ≥ 0}, DecreasingG.g (Theorem1.U κ q z) ∂Theorem1.γ + ∫ z in {z | Theorem1.U κ q z < 0}, DecreasingG.g (Theorem1.U κ q z) ∂Theorem1.γ < 0 := by
        have h_split : ∫ z in {z | Theorem1.U κ q z ≥ 0}, DecreasingG.g (Theorem1.U κ q z) ∂Theorem1.γ ≤ DecreasingG.g 0 * (Theorem1.γ {z | Theorem1.U κ q z ≥ 0}).toReal ∧ ∫ z in {z | Theorem1.U κ q z < 0}, DecreasingG.g (Theorem1.U κ q z) ∂Theorem1.γ ≤ (1 / 18) * (Theorem1.γ {z | Theorem1.U κ q z < 0}).toReal := by
          apply And.intro;
          · convert integral_g_U_pos_le_v2 κ hκ q hq using 1;
          · convert integral_g_U_neg_le κ hκ q hq using 1;
        have h_sum_neg : (Theorem1.γ {z | Theorem1.U κ q z ≥ 0}).toReal + (Theorem1.γ {z | Theorem1.U κ q z < 0}).toReal = 1 := by
          rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union ] <;> norm_num [ Set.disjoint_left ];
          · rw [ show { z : ℝ | 0 ≤ Theorem1.U κ q z } ∪ { z : ℝ | Theorem1.U κ q z < 0 } = Set.univ by ext x; by_cases hx : 0 ≤ Theorem1.U κ q x <;> aesop ] ; norm_num [ Theorem1.γ ] ;
          · exact measurableSet_Iio.mem.comp ( show Measurable ( fun z => Theorem1.U κ q z ) from by exact Measurable.div_const ( measurable_const.sub ( measurable_const.mul measurable_id' ) ) _ );
        have h_sum_neg : (Theorem1.γ {z | Theorem1.U κ q z ≥ 0}).toReal ≥ 1 / 2 := by
          apply_rules [ gamma_U_nonneg_ge_half ];
        nlinarith [ g0_bound ];
      convert h_exp_neg using 1;
      rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
      · rw [ show { z : ℝ | 0 ≤ Theorem1.U κ q z } ∪ { z : ℝ | Theorem1.U κ q z < 0 } = Set.univ by ext z; by_cases h : 0 ≤ Theorem1.U κ q z <;> aesop ] ; aesop;
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₁.out.not_lt hx₂.out;
      · exact measurableSet_Iio.mem.comp ( show Measurable ( fun z => Theorem1.U κ q z ) from by exact Measurable.div_const ( by exact Measurable.sub ( by exact measurable_const ) ( by exact measurable_id'.const_mul _ ) ) _ );
      · exact MeasureTheory.Integrable.integrableOn ( integrable_g_U κ q hq );
      · exact MeasureTheory.Integrable.integrableOn ( integrable_g_U κ q hq )

/-
The derivative of B is negative.
-/
lemma deriv_B_neg (κ : ℝ) (hκ : 0 ≤ κ) (q : ℝ) (hq : q ∈ Set.Ioo 0 1) :
    deriv (fun q => Theorem1.B κ q) q < 0 := by
  rw [deriv_B_eq κ q hq]
  exact expect_g_U_neg κ hκ q hq

/-
B(κ, 1) is 0.
-/
lemma B_one_eq_zero (κ : ℝ) : Theorem1.B κ 1 = 0 := by
  simp [Theorem1.B]

end AristotleLemmas

theorem B_strictAntiOn_Icc (κ : ℝ) (hκ : 0 ≤ κ) :
    StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1) := by
  have h_anti : ∀ q₁ q₂ : ℝ, 0 ≤ q₁ → q₁ < q₂ → q₂ ≤ 1 → Theorem1.B κ q₁ > Theorem1.B κ q₂ := by
    have h_mvt : ∀ q₁ q₂ : ℝ, 0 ≤ q₁ → q₁ < q₂ → q₂ < 1 → ∃ c ∈ Set.Ioo q₁ q₂, deriv (fun q => Theorem1.B κ q) c = (Theorem1.B κ q₂ - Theorem1.B κ q₁) / (q₂ - q₁) := by
      intros q₁ q₂ hq₁ hq₂ hq₂_lt_1
      apply exists_deriv_eq_slope ; aesop;
      · exact ContinuousOn.mono ( Theorem1.B_continuousOn κ ) fun x hx => hx.2.trans_lt hq₂_lt_1;
      · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_lt ( deriv_B_neg κ hκ x ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ ) ) );
    intros q₁ q₂ hq₁ hq₂ hq₂_le_one
    by_cases hq₂_eq_one : q₂ = 1;
    ·
      have h_strict_decr : ∀ q₁ q₂ : ℝ, 0 ≤ q₁ → q₁ < q₂ → q₂ < 1 → Theorem1.B κ q₁ > Theorem1.B κ q₂ := by
        intros q₁ q₂ hq₁ hq₂ hq₂_lt_one
        obtain ⟨c, hc⟩ := h_mvt q₁ q₂ hq₁ hq₂ hq₂_lt_one
        have h_deriv_neg : deriv (fun q => Theorem1.B κ q) c < 0 := by
          exact deriv_B_neg κ hκ c ⟨ by linarith [ hc.1.1 ], by linarith [ hc.1.2 ] ⟩
        have h_diff_neg : (Theorem1.B κ q₂ - Theorem1.B κ q₁) / (q₂ - q₁) < 0 := by
          linarith
        have h_diff_pos : Theorem1.B κ q₁ > Theorem1.B κ q₂ := by
          rw [ div_lt_iff₀ ] at h_diff_neg <;> linarith
        exact h_diff_pos;
      have h_lim : Filter.Tendsto (fun q₂ => Theorem1.B κ q₂) (nhdsWithin 1 (Set.Iio 1)) (nhds (Theorem1.Cκ κ)) := by
        convert Theorem1.tendsto_B_atOne_left κ using 1;
      have h_lim : Theorem1.Cκ κ ≤ Theorem1.B κ q₁ := by
        exact le_of_tendsto h_lim ( Filter.eventually_of_mem ( Ioo_mem_nhdsLT ( show q₁ < 1 by linarith ) ) fun q hq => le_of_lt ( h_strict_decr q₁ q hq₁ hq.1 hq.2 ) );
      convert h_lim.trans_lt' _ using 1;
      rw [ hq₂_eq_one, Theorem1.B_one_eq_zero ] ; exact Theorem1.Cκ_pos κ |> lt_of_le_of_lt ( by norm_num ) ;
    · obtain ⟨ c, hc₁, hc₂ ⟩ := h_mvt q₁ q₂ hq₁ hq₂ ( lt_of_le_of_ne hq₂_le_one hq₂_eq_one ) ; have := deriv_B_neg κ hκ c ⟨ by linarith [ hc₁.1 ], by linarith [ hc₁.2 ] ⟩ ; rw [ hc₂, div_eq_mul_inv ] at this ; nlinarith [ inv_mul_cancel₀ ( by linarith : ( q₂ - q₁ ) ≠ 0 ) ] ;
  exact fun x hx y hy hxy => h_anti x y hx.1 hxy hy.2

end B_lemmas

/-! ## 6. Reduction to a 1D equation and monotonicity of f -/

section f_lemmas

lemma f_continuousOn_Ici (κ α : ℝ) : ContinuousOn (f κ α) (Set.Ici (0 : ℝ)) := by
  have h_cont : ContinuousOn (fun r => A r) (Set.Ici 0) ∧ ContinuousOn (fun r => α * B κ (P r)) (Set.Ici 0) := by
    have hA_cont : ContinuousOn (fun r => A r) (Set.Ici 0) := by
      apply A_continuousOn_Ici;
    have hB_cont : ContinuousOn (fun q => B κ q) (Set.Iio 1) := by
      apply Theorem1.B_continuousOn;
    exact
      ⟨ hA_cont,
        ContinuousOn.mul continuousOn_const <|
          hB_cont.comp
            (show ContinuousOn (fun r => P r) (Set.Ici 0) from P_continuousOn_Ici)
            (fun r hr => by
              exact lt_of_lt_of_le (Theorem1.P_lt_one r) <| by norm_num) ⟩;
  exact ContinuousOn.sub h_cont.1 h_cont.2

lemma f_zero (κ α : ℝ) : f κ α 0 = -α * (B κ 0) := by
  simp [Theorem1.f, Theorem1.A, Theorem1.P]

lemma f_zero_neg (κ α : ℝ) (hα : 0 < α) : f κ α 0 < 0 := by
  have h_f_zero : Theorem1.f κ α 0 = -α * (E κ) ^ 2 := by
    simp [Theorem1.f, Theorem1.A, Theorem1.B, Theorem1.P_zero];
    simp [Theorem1.Expect, Theorem1.U]
  generalize_proofs at *; simp_all +decide [ E ] ; (
  apply pow_pos; exact DecreasingG.E_pos κ)

lemma tendsto_B_comp_P_atTop (κ : ℝ) :
    Tendsto (fun r => B κ (P r)) atTop (𝓝 (Cκ κ)) := by
  have h_P_tendsto_one : Filter.Tendsto (fun r => P r) Filter.atTop (𝓝 1) := by
    exact tendsto_P_atTop;
  have h_B_cont : Filter.Tendsto (fun q => B κ q) (𝓝[<] 1) (𝓝 (Cκ κ)) := by
    exact tendsto_B_atOne_left κ;
  refine h_B_cont.comp <| Filter.tendsto_inf.mpr ⟨ h_P_tendsto_one, ?_ ⟩;
  exact Filter.tendsto_principal.mpr ( Filter.eventually_atTop.mpr ⟨ 0, fun r hr => by simpa using Theorem1.P_lt_one r ⟩ )

lemma tendsto_f_atTop (κ α : ℝ) :
    Tendsto (f κ α) atTop (𝓝 ((2 : ℝ) / Real.pi - α * Cκ κ)) := by
  have hA_lim : Filter.Tendsto (fun r => A r) Filter.atTop (nhds (2 / Real.pi)) := by
    exact tendsto_A_atTop
  have hB_lim : Filter.Tendsto (fun r => B κ (P r)) Filter.atTop (nhds (Cκ κ)) := by
    have hP_lim : Filter.Tendsto P Filter.atTop (nhds 1) := by
      apply tendsto_P_atTop;
    have hB_cont : Filter.Tendsto (fun q => B κ q) (nhdsWithin 1 (Set.Iio 1)) (nhds (Cκ κ)) := by
      apply tendsto_B_atOne_left;
    refine' hB_cont.comp _;
    rw [ tendsto_nhdsWithin_iff ];
    exact ⟨ hP_lim, Filter.eventually_atTop.mpr ⟨ 0, fun r hr => by exact lt_of_lt_of_le ( P_lt_one r ) ( by norm_num ) ⟩ ⟩;
  field_simp;
  convert hA_lim.sub ( hB_lim.const_mul α ) using 2 ; ring;
  norm_num [ mul_assoc, mul_comm Real.pi _, Real.pi_ne_zero ]

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
For non-negative α, if B is strictly decreasing on [0,1], then f(r) = A(r) - α * B(P(r)) is strictly increasing on (0, ∞).
-/
lemma f_strictMonoOn_Ioi_nonneg
    (κ α : ℝ)
    (hα : 0 ≤ α)
    (hB : StrictAntiOn (fun q => Theorem1.B κ q) (Set.Icc (0 : ℝ) 1)) :
    StrictMonoOn (Theorem1.f κ α) (Set.Ioi (0 : ℝ)) := by
      intro r hr s hs hrs;
      have h_B : Theorem1.B κ (P r) > Theorem1.B κ (P s) := by
        apply hB;
        · exact ⟨ P_nonneg r, P_le_one r ⟩;
        · exact ⟨ P_nonneg _, P_le_one _ ⟩;
        · exact P_strictMonoOn_Ici ( show 0 ≤ r by linarith [ hr.out ] ) ( show 0 ≤ s by linarith [ hs.out ] ) hrs;
      exact add_lt_add_of_lt_of_le ( Theorem1.A_strictMonoOn_Ioi ( show 0 < r by linarith [ Set.mem_Ioi.mp hr ] ) ( show 0 < s by linarith [ Set.mem_Ioi.mp hs ] ) hrs ) ( neg_le_neg <| mul_le_mul_of_nonneg_left h_B.le <| by positivity )

/-
If A is strictly increasing and G is strictly decreasing, there exists a scalar α such that A - α G is not strictly increasing.
-/
lemma exists_alpha_counterexample (A G : ℝ → ℝ) (x y : ℝ) (hA : A x < A y) (hG : G y < G x) : ∃ α, ¬ (A x - α * G x < A y - α * G y) := by
  exact ⟨ ( A x - A y ) / ( G x - G y ), by nlinarith [ mul_div_cancel₀ ( A x - A y ) ( sub_ne_zero_of_ne hG.ne' ) ] ⟩

/-
The composition of B (strictly decreasing on [0,1]) and P (strictly increasing into [0,1]) is strictly decreasing on (0, ∞).
-/
lemma B_comp_P_strictAntiOn
    (κ : ℝ)
    (hB : StrictAntiOn (fun q => Theorem1.B κ q) (Set.Icc (0 : ℝ) 1)) :
    StrictAntiOn (fun r => Theorem1.B κ (Theorem1.P r)) (Set.Ioi (0 : ℝ)) := by
      intros r hr s hs hrs;
      apply hB;
      · exact ⟨ Theorem1.P_nonneg r, Theorem1.P_le_one r ⟩;
      · exact ⟨ Theorem1.P_nonneg s, Theorem1.P_le_one s ⟩;
      · exact P_strictMonoOn_Ici ( show 0 ≤ r by linarith [ hr.out ] ) ( show 0 ≤ s by linarith [ hs.out ] ) hrs

/-
There exists a parameter α such that f is not strictly increasing on (0, ∞).
-/
lemma exists_alpha_not_strictMonoOn_f
    (κ : ℝ)
    (hB : StrictAntiOn (fun q => Theorem1.B κ q) (Set.Icc 0 1)) :
    ∃ α, ¬ StrictMonoOn (Theorem1.f κ α) (Set.Ioi 0) := by
      -- By Lemma B_comp_P_strictAntiOn, there exist x = 1 and y = 2 such that A(1) < A(2) and B(1) > B(2).
      set x := (1 : ℝ)
      set y := (2 : ℝ);
      obtain ⟨α, hα⟩ : ∃ α, ¬ (A x - α * B κ (P x) < A y - α * B κ (P y)) := exists_alpha_counterexample (A) (fun r => B κ (P r)) x y (A_strictMonoOn_Ioi (by norm_num) (by norm_num) (by norm_num)) (B_comp_P_strictAntiOn κ hB (by norm_num) (by norm_num) (by norm_num));
      exact ⟨ α, fun h => hα <| h ( by norm_num ) ( by norm_num ) ( by norm_num ) ⟩

/-
The claim that f is strictly increasing for all α is false.
-/
lemma f_strictMonoOn_Ioi_false : ¬ (∀ κ α, StrictAntiOn (fun q => Theorem1.B κ q) (Set.Icc 0 1) → StrictMonoOn (Theorem1.f κ α) (Set.Ioi 0)) := by
  have := exists_alpha_not_strictMonoOn_f 0 ( B_strictAntiOn_Icc 0 ( by norm_num ) );
  exact fun h => this.choose_spec <| h 0 _ <| B_strictAntiOn_Icc 0 ( by norm_num )

end AristotleLemmas

lemma f_strictMonoOn_Ioi
    (κ α : ℝ)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    StrictMonoOn (f κ α) (Set.Ioi (0 : ℝ)) := by
  -- Use: `A` strictly increasing, `P` strictly increasing, `B` strictly decreasing.
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose any κ and α such that B is strictly decreasing on [0,1].
  obtain ⟨κ, hB⟩ : ∃ κ : ℝ, StrictAntiOn (fun q => Theorem1.B κ q) (Set.Icc 0 1) := by
    -- By definition of $B$, we know that it is strictly decreasing on $[0, 1]$ for any $\kappa \geq 0$.
    use 0; exact (by
    -- Apply the lemma that states B is strictly decreasing on [0,1] for any κ ≥ 0.
    apply B_strictAntiOn_Icc; norm_num)
  generalize_proofs at *; (
  -- By the lemma `exists_alpha_not_strictMonoOn_f`, there exists an α such that `f` is not strictly increasing on `(0, ∞)`.
  obtain ⟨α, hα⟩ : ∃ α : ℝ, ¬ StrictMonoOn (Theorem1.f κ α) (Set.Ioi 0) := by
    exact?
  generalize_proofs at *; (use κ, α))

-/
lemma f_strictMonoOn_Ioi
    (κ α : ℝ)
    (hα : 0 ≤ α)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    StrictMonoOn (f κ α) (Set.Ioi (0 : ℝ)) := by
  intro r hr s hs hrs
  have hA : A r < A s := A_strictMonoOn_Ioi hr hs hrs
  have hP : P r < P s := by
    have hr0 : 0 ≤ r := le_of_lt (Set.mem_Ioi.mp hr)
    have hs0 : 0 ≤ s := le_of_lt (Set.mem_Ioi.mp hs)
    simpa using (P_strictMonoOn_Ici hr0 hs0 hrs)
  have hBdec : B κ (P s) < B κ (P r) :=
    hB ⟨P_nonneg r, P_le_one r⟩ ⟨P_nonneg s, P_le_one s⟩ hP
  have hterm : (-α) * B κ (P r) ≤ (-α) * B κ (P s) := by
    have hα' : -α ≤ 0 := by linarith
    exact mul_le_mul_of_nonpos_left hBdec.le hα'
  have : A r + (-α) * B κ (P r) < A s + (-α) * B κ (P s) :=
    add_lt_add_of_lt_of_le hA hterm
  simpa [f, sub_eq_add_neg, neg_mul, add_assoc, add_left_comm, add_comm, mul_assoc] using this

lemma f_root_unique
    (κ α : ℝ)
    (hα : 0 ≤ α)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ∀ {r₁ r₂ : ℝ}, r₁ ∈ Set.Ioi 0 → r₂ ∈ Set.Ioi 0 → f κ α r₁ = 0 → f κ α r₂ = 0 → r₁ = r₂ := by
  intro r₁ r₂ hr₁ hr₂ hr₁_eq hr₂_eq
  have hmono : StrictMonoOn (f κ α) (Set.Ioi (0 : ℝ)) :=
    f_strictMonoOn_Ioi κ α hα hB
  exact hmono.injOn hr₁ hr₂ (by simpa [hr₁_eq, hr₂_eq])

end f_lemmas

/-! ## 7. Theorem 1 (`thm:main`) -/

section TheoremMain

lemma exists_root_of_alpha_lt_alpha_c
    (κ α : ℝ)
    (hα0 : 0 < α)
    (hα : α < αc κ)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ∃ r : ℝ, r ∈ Set.Ioi (0 : ℝ) ∧ f κ α r = 0 := by
  have h_ivt : ∃ r ∈ Set.Ioi 0, f κ α r > 0 := by
    have h_ivt : Filter.Tendsto (fun r => f κ α r) Filter.atTop (nhds ((2 : ℝ) / Real.pi - α * Cκ κ)) := by
      exact tendsto_f_atTop κ α
    generalize_proofs at *; (
    have h_ivt : (2 : ℝ) / Real.pi - α * Cκ κ > 0 := by
      rw [ show Theorem1.αc κ = 2 / ( Real.pi * Theorem1.Cκ κ ) by rfl ] at hα ; rw [ lt_div_iff₀ ] at hα <;> nlinarith [ Real.pi_pos, Theorem1.Cκ_pos κ, mul_div_cancel₀ ( 2 : ℝ ) Real.pi_ne_zero ] ;
    generalize_proofs at *; (
    have := ‹Filter.Tendsto ( fun r => Theorem1.f κ α r ) Filter.atTop ( 𝓝 ( 2 / Real.pi - α * Theorem1.Cκ κ ) ) ›.eventually ( lt_mem_nhds h_ivt ) ; have := this.and ( Filter.eventually_gt_atTop 0 ) ; obtain ⟨ r, hr₁, hr₂ ⟩ := this.exists; exact ⟨ r, hr₂, hr₁ ⟩ ;));
  obtain ⟨r, hr⟩ : ∃ r ∈ Set.Ioo 0 (h_ivt.choose), f κ α r = 0 := by
    apply_rules [ intermediate_value_Ioo ];
    · exact le_of_lt h_ivt.choose_spec.1;
    · exact ContinuousOn.mono ( f_continuousOn_Ici κ α ) ( Set.Icc_subset_Ici_self );
    · exact ⟨ by simpa using f_zero_neg κ α hα0, h_ivt.choose_spec.2 ⟩;
  exact ⟨ r, hr.1.1, hr.2 ⟩

lemma existsUnique_r_of_alpha_lt_alpha_c
    (κ α : ℝ)
    (hα0 : 0 < α)
    (hα : α < αc κ)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ∃! r : ℝ, r ∈ Set.Ioi (0 : ℝ) ∧ f κ α r = 0 := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r ∈ Set.Ioi (0 : ℝ) ∧ Theorem1.f κ α r = 0 := by
    apply exists_root_of_alpha_lt_alpha_c κ α hα0 hα hB;
  have h_unique : ∀ r₁ r₂ : ℝ, r₁ ∈ Set.Ioi 0 → r₂ ∈ Set.Ioi 0 → Theorem1.f κ α r₁ = 0 → Theorem1.f κ α r₂ = 0 → r₁ = r₂ := by
    intros r₁ r₂ hr₁ hr₂ hr₁_zero hr₂_zero
    apply f_root_unique κ α hα0.le hB hr₁ hr₂ hr₁_zero hr₂_zero;
  use r, hr, fun r' hr' => h_unique r' r hr'.left hr.left hr'.right hr.right

lemma existsUnique_solution_of_alpha_lt_alpha_c
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ∃! qr : ℝ × ℝ, IsSolution κ α qr.1 qr.2 := by
  obtain ⟨r, hr⟩ : ∃! r : ℝ, r ∈ Set.Ioi (0 : ℝ) ∧ f κ α r = 0 := by
    apply existsUnique_r_of_alpha_lt_alpha_c κ α hα0 hα hB;
  use (P r, r);
  have hr_eq : r = Theorem1.R κ (Theorem1.P r) α := by
    have hr_eq : Theorem1.A r = α * Theorem1.B κ (Theorem1.P r) := by
      exact eq_of_sub_eq_zero hr.1.2;
    rw [ Theorem1.R_eq ] <;> norm_num at *;
    · rw [ ← hr_eq, Theorem1.A_eq_r_mul_S_sq ] ; ring;
      rw [ show Theorem1.S r = 1 - Theorem1.P r from Theorem1.S_eq_one_sub_P r ] ; ring;
      nlinarith [ inv_mul_cancel_left₀ ( show ( 1 - Theorem1.P r * 2 + Theorem1.P r ^ 2 ) ≠ 0 by nlinarith [ show Theorem1.P r < 1 from Theorem1.P_lt_one r ] ) r ];
    · exact Theorem1.P_lt_one r;
  refine' ⟨ _, _ ⟩;
  · refine' ⟨ _, _, _, _, _ ⟩ <;> try linarith [ hr.1.1.out ];
    · exact Theorem1.P_nonneg r;
    · exact Theorem1.P_lt_one r;
  · rintro ⟨ q, r' ⟩ hqr
    obtain ⟨ hq, hq_lt, hr0, hq_eq, hr_eqR ⟩ := hqr
    have hf0 : f κ α r' = 0 :=
      (f_eq_zero_iff_system (κ := κ) (α := α) (q := q) (r := r') hq_eq hq_lt).2 hr_eqR
    have hr_pos : r' ∈ Set.Ioi 0 := by
      have hr_ne : r' ≠ 0 := by
        intro h0
        have : f κ α 0 = 0 := by simpa [h0] using hf0
        exact (ne_of_lt (f_zero_neg κ α hα0)) this
      exact lt_of_le_of_ne hr0 hr_ne.symm
    have hr'_eq_r : r' = r := hr.right r' ⟨hr_pos, hf0⟩
    have hq_eq_pr : q = Theorem1.P r := by
      simpa [hr'_eq_r] using hq_eq
    exact Prod.ext hq_eq_pr hr'_eq_r

lemma no_solution_of_alpha_ge_alpha_c
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα : αc κ ≤ α)
    (hB : StrictAntiOn (fun q => B κ q) (Set.Icc (0 : ℝ) 1)) :
    ¬ ∃ q r : ℝ, IsSolution κ α q r := by
  have h_f : ∀ r : ℝ, Theorem1.f κ α r = Theorem1.A r - α * Theorem1.B κ (Theorem1.P r) := by
    intro r; rfl;
  have h_no_root : ∀ r : ℝ, r ∈ Set.Ioi 0 → Theorem1.f κ α r < 0 := by
    have h_alpha_B_ge_two_pi : ∀ r ∈ Set.Ioi 0, α * Theorem1.B κ (Theorem1.P r) ≥ (2 : ℝ) / Real.pi := by
      have h_alpha_B_ge_alpha_Cκ : ∀ r ∈ Set.Ioi 0, α * Theorem1.B κ (Theorem1.P r) ≥ α * Theorem1.Cκ κ := by
        intros r hr
        have h_B_ge_Cκ : Theorem1.B κ (Theorem1.P r) ≥ Theorem1.Cκ κ := by
          have h_B_ge_Cκ : Filter.Tendsto (fun q => Theorem1.B κ q) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (Theorem1.Cκ κ)) := by
            exact tendsto_B_atOne_left κ;
          have h_B_ge_Cκ : ∀ᶠ q in nhdsWithin 1 (Set.Iio 1), Theorem1.B κ q ≤ Theorem1.B κ (Theorem1.P r) := by
            have h_B_ge_Cκ : ∀ᶠ q in nhdsWithin 1 (Set.Iio 1), q ≥ Theorem1.P r := by
              have h_P_lt_one : Theorem1.P r < 1 := by
                exact Theorem1.P_lt_one r;
              exact Filter.eventually_of_mem ( Ioo_mem_nhdsLT h_P_lt_one ) fun q hq => hq.1.le;
            filter_upwards [ h_B_ge_Cκ, Ioo_mem_nhdsLT zero_lt_one ] with q hq₁ hq₂ using hB.le_iff_ge ( by constructor <;> linarith [ hq₂.1, hq₂.2, show 0 ≤ Theorem1.P r from Theorem1.P_nonneg r ] ) ( by constructor <;> linarith [ hq₂.1, hq₂.2, show 0 ≤ Theorem1.P r from Theorem1.P_nonneg r ] ) |>.2 hq₁;
          exact le_of_tendsto ‹_› h_B_ge_Cκ |> le_trans <| by norm_num;
        exact mul_le_mul_of_nonneg_left h_B_ge_Cκ (by
        exact le_trans ( by exact div_nonneg zero_le_two ( mul_nonneg Real.pi_pos.le ( by exact le_of_lt ( Theorem1.Cκ_pos κ ) ) ) ) hα);
      field_simp;
      intro r hr; nlinarith [ h_alpha_B_ge_alpha_Cκ r hr, Real.pi_gt_three, Theorem1.Cκ_pos κ, mul_pos Real.pi_pos ( Theorem1.Cκ_pos κ ), Theorem1.αc_pos κ, mul_le_mul_of_nonneg_left hα ( Real.pi_pos.le ), mul_le_mul_of_nonneg_left hα ( Theorem1.Cκ_pos κ |> le_of_lt ), Theorem1.αc κ, show Theorem1.αc κ = 2 / ( Real.pi * Theorem1.Cκ κ ) from rfl, mul_div_cancel₀ ( 2 : ℝ ) ( ne_of_gt <| mul_pos Real.pi_pos <| Theorem1.Cκ_pos κ ) ] ;
    have h_A_lt_two_pi : ∀ r ∈ Set.Ioi 0, Theorem1.A r < (2 : ℝ) / Real.pi := by
      intro r hr
      have h_A_lt_two_pi : Theorem1.A r < (2 : ℝ) / Real.pi := by
        have h_A_lt_two_pi_aux : ∀ r ∈ Set.Ioi 0, Theorem1.A r < (2 : ℝ) / Real.pi := by
          have h_A_lt_two_pi_aux : Filter.Tendsto Theorem1.A Filter.atTop (𝓝 ((2 : ℝ) / Real.pi)) := by
            exact tendsto_A_atTop
          have h_A_lt_two_pi_aux : StrictMonoOn Theorem1.A (Set.Ioi 0) := by
            exact A_strictMonoOn_Ioi;
          exact fun r hr => lt_of_lt_of_le ( h_A_lt_two_pi_aux.lt_iff_lt hr ( show 0 < r + 1 by linarith [ hr.out ] ) |>.2 ( by linarith [ hr.out ] ) ) ( le_of_tendsto_of_tendsto tendsto_const_nhds ‹_› ( Filter.eventually_atTop.mpr ⟨ r + 1, fun x hx => h_A_lt_two_pi_aux.monotoneOn ( show 0 < r + 1 by linarith [ hr.out ] ) ( show 0 < x by linarith [ hr.out ] ) hx ⟩ ) ) |> lt_of_lt_of_le <| by norm_num;
        exact h_A_lt_two_pi_aux r hr
      exact h_A_lt_two_pi;
    exact fun r hr => by linarith [ h_f r, h_alpha_B_ge_two_pi r hr, h_A_lt_two_pi r hr ] ;
  intro h_solution
  obtain ⟨q, r, hq, hr⟩ := h_solution
  have h_f_zero : Theorem1.f κ α r = 0 := by
    exact Theorem1.f_eq_zero_iff_system κ α q r hr.2.2.1 hr.1 |>.2 hr.2.2.2;
  by_cases hr_pos : 0 < r <;> norm_num [ hr_pos ] at h_f_zero ⊢;
  · linarith [ h_no_root r hr_pos ];
  · norm_num [ show r = 0 by linarith ] at *;
    linarith [ f_zero_neg κ α ( show 0 < α by exact lt_of_lt_of_le ( αc_pos κ ) hα ) ]

theorem theorem_main
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    ∃! qr : ℝ × ℝ, IsSolution κ α qr.1 qr.2 := by
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
  apply Classical.choose_spec (theorem_main (κ := κ) (α := α) hκ hα0 hα).exists

/-! ## 9. Theorem 2 (`thm:2ndmain`) — sequential formulation -/

section TheoremSecondMain

lemma tendsto_q_of_tendsto_r
    (r q : ℕ → ℝ)
    (hq : ∀ n, q n = P (r n))
    (hr : Tendsto r atTop atTop) :
    Tendsto q atTop (𝓝 (1 : ℝ)) := by
  have hP : Tendsto P atTop (𝓝 (1 : ℝ)) := tendsto_P_atTop
  have hP_r : Tendsto (fun n => P (r n)) atTop (𝓝 (1 : ℝ)) := hP.comp hr
  have hqfun : q = fun n => P (r n) := funext hq
  simpa [hqfun] using hP_r

lemma exists_frequently_le_of_not_tendsto_atTop
    (r : ℕ → ℝ)
    (hnot : ¬ Tendsto r atTop atTop) :
    ∃ R : ℝ, (∃ᶠ n in atTop, r n ≤ R) := by
  have h_not_tendsto : ¬ Filter.Tendsto r Filter.atTop Filter.atTop → ∃ R, ∀ N, ∃ n ≥ N, r n ≤ R := by
    simp [Filter.tendsto_atTop_atTop] at hnot ⊢;
    intros x hx; exact ⟨x, fun N => by obtain ⟨n, hn₁, hn₂⟩ := hx N; exact ⟨n, hn₁, le_of_lt hn₂⟩⟩;
  obtain ⟨R, hR⟩ := h_not_tendsto hnot;
  use R;
  simp [Filter.Frequently, hR];

lemma exists_subseq_tendsto_of_frequently_bounded
    {r : ℕ → ℝ} {R : ℝ}
    (hfreq : ∃ᶠ n in atTop, r n ∈ Set.Icc (0 : ℝ) R) :
    ∃ rStar ∈ Set.Icc (0 : ℝ) R, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (r ∘ φ) atTop (𝓝 rStar) := by
  have h_bolzano_weierstrass : IsCompact (Set.Icc (0 : ℝ) R) := by
    exact CompactIccSpace.isCompact_Icc;
  have h_bounded : Bornology.IsBounded (Set.Icc (0 : ℝ) R) := h_bolzano_weierstrass.isBounded
  obtain ⟨rStar, hrStar, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_frequently_bounded (X := ℝ) (s := Set.Icc (0 : ℝ) R) h_bounded hfreq
  have hrStar' : rStar ∈ Set.Icc (0 : ℝ) R := by
    have hclosed : IsClosed (Set.Icc (0 : ℝ) R) := isClosed_Icc
    simpa [hclosed.closure_eq] using hrStar
  exact ⟨rStar, hrStar', φ, hφ, hlim⟩

lemma solution_at_alpha_c_of_bounded_subseq
    (κ : ℝ) (hκ : 0 ≤ κ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 < α n ∧ α n < αc κ)
    (hlim : Tendsto α atTop (𝓝 (αc κ)))
    (R : ℝ)
    (hfreq : ∃ᶠ n in atTop, rSol κ (α n) hκ (hα n).1 (hα n).2 ∈ Set.Icc (0 : ℝ) R) :
    ∃ qStar rStar : ℝ, IsSolution κ (αc κ) qStar rStar := by
  exfalso;
  obtain ⟨rStar, hrStar⟩ : ∃ rStar, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (fun n => rSol κ (α (φ n)) hκ (hα (φ n)).left (hα (φ n)).right) Filter.atTop (nhds rStar) := by
    have h_bounded : ∃ R, ∃ᶠ n in Filter.atTop, Theorem1.rSol κ (α n) hκ (hα n).left (hα n).right ∈ Set.Icc 0 R := by
      use R;
    obtain ⟨ R, hR ⟩ := h_bounded;
    have := exists_subseq_tendsto_of_frequently_bounded hR;
    tauto;
  obtain ⟨φ, hφ_mono, hφ_lim⟩ := hrStar
  have h_qStar : Filter.Tendsto (fun n => qSol κ (α (φ n)) hκ (hα (φ n)).left (hα (φ n)).right) Filter.atTop (nhds (P rStar)) := by
    have h_qStar : Filter.Tendsto (fun n => P (rSol κ (α (φ n)) hκ (hα (φ n)).left (hα (φ n)).right)) Filter.atTop (nhds (P rStar)) := by
      exact Theorem1.P_continuous.continuousAt.tendsto.comp hφ_lim;
    exact h_qStar.congr fun n => qSol_spec κ ( α ( φ n ) ) hκ ( hα ( φ n ) |>.1 ) ( hα ( φ n ) |>.2 ) |>.2.2.2.1 ▸ rfl;
  have h_lim_eq : rStar = Theorem1.αc κ * B κ (P rStar) / (1 - P rStar)^2 := by
    have h_lim_eq : Filter.Tendsto (fun n => α (φ n) * B κ (qSol κ (α (φ n)) hκ (hα (φ n)).left (hα (φ n)).right) / (1 - qSol κ (α (φ n)) hκ (hα (φ n)).left (hα (φ n)).right)^2) Filter.atTop (nhds (Theorem1.αc κ * B κ (P rStar) / (1 - P rStar)^2)) := by
      refine' Filter.Tendsto.div _ _ _;
      · refine' Filter.Tendsto.mul ( hlim.comp hφ_mono.tendsto_atTop ) _;
        have h_cont_B : ContinuousOn (fun q => Theorem1.B κ q) (Set.Iio 1) := by
          exact Theorem1.B_continuousOn κ;
        exact h_cont_B.continuousAt ( Iio_mem_nhds <| show Theorem1.P rStar < 1 from by
                                                        exact Theorem1.P_lt_one rStar ) |> fun h => h.tendsto.comp h_qStar;
      · exact Filter.Tendsto.pow ( tendsto_const_nhds.sub h_qStar ) _;
      · exact pow_ne_zero _ ( sub_ne_zero_of_ne <| ne_of_gt <| by exact lt_of_lt_of_le ( Theorem1.P_lt_one _ ) <| by norm_num );
    have h_eq : ∀ n, Theorem1.rSol κ (α (φ n)) hκ (hα (φ n)).left (hα (φ n)).right = α (φ n) * B κ (qSol κ (α (φ n)) hκ (hα (φ n)).left (hα (φ n)).right) / (1 - qSol κ (α (φ n)) hκ (hα (φ n)).left (hα (φ n)).right)^2 := by
      intro n
      generalize_proofs at *;
      convert Theorem1.qSol_spec κ ( α ( φ n ) ) hκ ‹_› ‹_› |>.2.2.2.2 using 1;
      rw [ Theorem1.R_eq ];
      exact Theorem1.qSol_spec κ ( α ( φ n ) ) hκ ‹_› ‹_› |>.2.1;
    exact tendsto_nhds_unique hφ_lim ( by simpa only [ h_eq ] using h_lim_eq );
  have h_contradiction : IsSolution κ (Theorem1.αc κ) (P rStar) rStar := by
    refine' ⟨ _, _, _, _, _ ⟩;
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_qStar fun n => by exact ( qSol_spec κ ( α ( φ n ) ) hκ ( hα ( φ n ) |>.1 ) ( hα ( φ n ) |>.2 ) ) |>.1;
    · exact Theorem1.P_lt_one rStar;
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hφ_lim fun n => ( qSol_spec κ ( α ( φ n ) ) hκ ( hα ( φ n ) |>.1 ) ( hα ( φ n ) |>.2 ) ) |>.2.2.1;
    · rfl;
    · convert h_lim_eq using 1;
      rw [ Theorem1.R_eq ] ; ring;
      exact Theorem1.P_lt_one rStar;
  have := @theorem_main_no_solution κ ( Theorem1.αc κ ) hκ ( by linarith [ hα 0 ] ) ; exact this ⟨ _, _, h_contradiction ⟩ ;

theorem theorem_second_main_seq
    (κ : ℝ) (hκ : 0 ≤ κ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 < α n ∧ α n < αc κ)
    (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    (Tendsto (fun n => rSol κ (α n) hκ (hα n).1 (hα n).2) atTop atTop) ∧
      Tendsto (fun n => qSol κ (α n) hκ (hα n).1 (hα n).2) atTop (𝓝 (1 : ℝ)) := by
  have hr_tendsto :
      Tendsto (fun n => rSol κ (α n) hκ (hα n).1 (hα n).2) atTop atTop := by
    by_contra hrnot
    obtain ⟨R, hR⟩ :=
      exists_frequently_le_of_not_tendsto_atTop
        (r := fun n => rSol κ (α n) hκ (hα n).1 (hα n).2) hrnot
    have h_solution_at_alpha_c :
        ∃ qStar rStar : ℝ, IsSolution κ (αc κ) qStar rStar := by
      apply solution_at_alpha_c_of_bounded_subseq κ hκ α hα hlim R
      exact hR.mono (fun n hn =>
        ⟨(qSol_spec κ (α n) hκ (hα n).1 (hα n).2).2.2.1, hn⟩)
    exact (theorem_main_no_solution κ (αc κ) hκ le_rfl) h_solution_at_alpha_c
  have hq_tendsto :
      Tendsto (fun n => qSol κ (α n) hκ (hα n).1 (hα n).2) atTop (𝓝 (1 : ℝ)) := by
    refine tendsto_q_of_tendsto_r
      (r := fun n => rSol κ (α n) hκ (hα n).1 (hα n).2)
      (q := fun n => qSol κ (α n) hκ (hα n).1 (hα n).2) ?_ hr_tendsto
    intro n
    exact (qSol_spec κ (α n) hκ (hα n).1 (hα n).2).2.2.2.1
  exact ⟨hr_tendsto, hq_tendsto⟩

end TheoremSecondMain

end

end Theorem1

/-!
# Theorem 3 (RS* → -∞ as α ↑ αc)

This section follows the blueprint `perceptronFixed/Theorem3/blueprint.txt`.

Paper target: `main.tex` Theorem `\label{thm: bound for threshold}`.

We work with the canonical solution `(qSol κ α, rSol κ α)` from `Theorem1/Theorem.lean`
for `0 < α < αc κ` and define the replica-symmetric free energy
`RSStar κ α = 𝓕κ(α; qSol, rSol)`.

All proofs are provided in Lean.
-/

open scoped BigOperators Topology NNReal Real ENNReal Interval
open MeasureTheory Filter

namespace Theorem3

noncomputable section

/-! ## 0. Aliases (from `Theorem1`) -/

abbrev γ : Measure ℝ := Theorem1.γ
abbrev Expect (f : ℝ → ℝ) : ℝ := Theorem1.Expect f

abbrev Φbar : ℝ → ℝ := Theorem1.Φbar
abbrev φ : ℝ → ℝ := Theorem1.φ
abbrev E : ℝ → ℝ := Theorem1.E

abbrev αc (κ : ℝ) : ℝ := Theorem1.αc κ
abbrev P : ℝ → ℝ := Theorem1.P
abbrev U : ℝ → ℝ → ℝ → ℝ := Theorem1.U
abbrev B : ℝ → ℝ → ℝ := Theorem1.B
abbrev R : ℝ → ℝ → ℝ → ℝ := Theorem1.R

abbrev qSol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  Theorem1.qSol κ α hκ hα0 hα

abbrev rSol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  Theorem1.rSol κ α hκ hα0 hα

abbrev sech : ℝ → ℝ := Theorem1.sech
abbrev S : ℝ → ℝ := Theorem1.S

lemma S_eq_one_sub_P (r : ℝ) : S r = 1 - P r := by
  simpa [S, P] using Theorem1.S_eq_one_sub_P r

/-! ### Standard normal CDF (defined from the tail) -/

def Φ (u : ℝ) : ℝ := 1 - Φbar u

/-- Auxiliary constant used in Step 2.4 (log bounds). -/
def Cδ (δ : ℝ) : ℝ :=
  -Real.log (δ / 2)

private lemma φ_eq_mills : (fun x : ℝ => φ x) = MillsBlueprint.Proof.φ := by
  funext x
  simp [φ, Theorem1.φ, DecreasingG.φ, MillsBlueprint.Proof.φ, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc]

private lemma φ_eq_gaussianPDFReal : (fun x : ℝ => φ x) = ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) := by
  funext x
  simp [φ, Theorem1.φ, DecreasingG.φ, ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv, mul_comm,
    mul_left_comm]

private lemma Φbar_eq_mills (u : ℝ) : Φbar u = MillsBlueprint.Proof.Φbar u := by
  have h1 : Φbar u = ∫ x in Set.Ioi u, φ x := by
    simp [Φbar, Theorem1.Φbar, DecreasingG.Φbar, φ, Theorem1.φ, DecreasingG.φ,
      MeasureTheory.integral_Ici_eq_integral_Ioi]
  have h2 : MillsBlueprint.Proof.Φbar u = ∫ x in Set.Ioi u, MillsBlueprint.Proof.φ x := by
    simpa using (MillsBlueprint.Proof.Φbar_eq_integral_Ioi (u := u))
  calc
    Φbar u = ∫ x in Set.Ioi u, φ x := h1
    _ = ∫ x in Set.Ioi u, MillsBlueprint.Proof.φ x := by
          simp [φ_eq_mills]
    _ = MillsBlueprint.Proof.Φbar u := by
          simpa using h2.symm

/-! ## 1. RS functional and RS* -/

/-- Replica-symmetric functional `𝓕κ(α;q,r)` (main.tex (RSfunctional)). -/
def RSFunctional (κ α q r : ℝ) : ℝ :=
  -(r * (1 - q) / 2)
    + Expect (fun z => Real.log (2 * Real.cosh (Real.sqrt r * z)))
    + α * Expect (fun z => Real.log (Φbar ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))))

/-- `RS* κ α` = the RS functional at the unique solution. -/
def RSStar (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  RSFunctional κ α (qSol κ α hκ hα0 hα) (rSol κ α hκ hα0 hα)

/-! ### A split form of RS* for algebraic manipulation -/

def RSFunctionalSplit (κ α q r : ℝ) : ℝ :=
  Real.log 2
    - (r * (1 - q) / 2)
    + Expect (fun z => Real.log (Real.cosh (Real.sqrt r * z)))
    + α * Expect (fun z => Real.log (Φbar ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))))

lemma RSFunctional_eq_split (κ α q r : ℝ) :
    RSFunctional κ α q r = RSFunctionalSplit κ α q r := by
  unfold RSFunctional RSFunctionalSplit Expect Theorem1.Expect
  have hlog :
      ∀ z : ℝ,
        Real.log (2 * Real.cosh (Real.sqrt r * z)) =
          Real.log 2 + Real.log (Real.cosh (Real.sqrt r * z)) := by
    intro z
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hcosh : Real.cosh (Real.sqrt r * z) ≠ 0 := (Real.cosh_pos _).ne'
    rw [Real.log_mul h2 hcosh]
  have hspin :
      (∫ z : ℝ, Real.log (2 * Real.cosh (Real.sqrt r * z)) ∂γ) =
        Real.log 2 + ∫ z : ℝ, Real.log (Real.cosh (Real.sqrt r * z)) ∂γ := by
    have hint_const : Integrable (fun _ : ℝ => Real.log 2) γ := integrable_const _
    have hint_cosh : Integrable (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) γ := by
      have h1 : Integrable (fun z : ℝ => |Real.sqrt r * z|) γ := by
        have hint_z : Integrable (fun z : ℝ => z) γ := by
          simpa [γ, Theorem1.γ] using
            (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (1 : ℝ≥0)))
              |>.integrable
        simpa [abs_mul] using hint_z.abs.const_mul |Real.sqrt r|
      have hbound : ∀ z : ℝ, ‖Real.log (Real.cosh (Real.sqrt r * z))‖ ≤ |Real.sqrt r * z| := by
        intro z
        have hnonneg : 0 ≤ Real.log (Real.cosh (Real.sqrt r * z)) := by
          have hcosh' : 1 ≤ Real.cosh (Real.sqrt r * z) := Real.one_le_cosh _
          exact Real.log_nonneg hcosh'
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        have hcosh_le : Real.cosh (Real.sqrt r * z) ≤ Real.exp |Real.sqrt r * z| := by
          rw [Real.cosh_eq]
          have h1 : Real.exp (Real.sqrt r * z) ≤ Real.exp |Real.sqrt r * z| := by
            apply Real.exp_le_exp_of_le
            exact le_abs_self _
          have h2 : Real.exp (-(Real.sqrt r * z)) ≤ Real.exp |Real.sqrt r * z| := by
            apply Real.exp_le_exp_of_le
            exact neg_le_abs _
          linarith
        calc Real.log (Real.cosh (Real.sqrt r * z))
            ≤ Real.log (Real.exp |Real.sqrt r * z|) := by
                apply Real.log_le_log (Real.cosh_pos _) hcosh_le
          _ = |Real.sqrt r * z| := Real.log_exp _
      have hmeas :
          AEStronglyMeasurable (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) γ := by
        have hmul : Measurable (fun z : ℝ => Real.sqrt r * z) := by
          simpa using (measurable_const.mul measurable_id)
        have hmeas' : Measurable (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) := by
          simpa using (hmul.cosh.log)
        exact hmeas'.aestronglyMeasurable
      exact Integrable.mono' h1 hmeas (ae_of_all _ hbound)
    calc
      (∫ z : ℝ, Real.log (2 * Real.cosh (Real.sqrt r * z)) ∂γ) =
          ∫ z : ℝ, (Real.log 2 + Real.log (Real.cosh (Real.sqrt r * z))) ∂γ := by
            refine MeasureTheory.integral_congr_ae ?_
            exact MeasureTheory.ae_of_all _ (fun z => hlog z)
      _ = (∫ _z : ℝ, Real.log 2 ∂γ) + ∫ z : ℝ, Real.log (Real.cosh (Real.sqrt r * z)) ∂γ := by
            exact MeasureTheory.integral_add hint_const hint_cosh
      _ = Real.log 2 + ∫ z : ℝ, Real.log (Real.cosh (Real.sqrt r * z)) ∂γ := by
            simp [MeasureTheory.integral_const, MeasureTheory.probReal_univ]
  simp [hspin, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma RSStar_eq_split
    (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) :
    RSStar κ α hκ hα0 hα =
      RSFunctionalSplit κ α (qSol κ α hκ hα0 hα) (rSol κ α hκ hα0 hα) := by
  simp [RSStar, RSFunctional_eq_split]

/-! ## 2. Auxiliary bounds for Theorem 3 -/

/-! ### Step 2.3: spin term bound -/


private lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh ((1 / Real.cosh x) ^ 2) x := by
  have hs : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
  have hc : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hcosh_ne : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hq :
      HasDerivAt (fun y : ℝ => Real.sinh y / Real.cosh y)
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) x := by
    simpa using hs.div hc hcosh_ne
  have hEq :
      (fun y : ℝ => Real.tanh y) =ᶠ[𝓝 x] (fun y : ℝ => Real.sinh y / Real.cosh y) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    simpa using (Real.tanh_eq_sinh_div_cosh y)
  have hq_tanh :
      HasDerivAt Real.tanh
        ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) x :=
    hq.congr_of_eventuallyEq hEq
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
  have hcosh2 : 0 < (Real.cosh x) ^ 2 := sq_pos_of_pos (Real.cosh_pos x)
  have hsinh_lt : (Real.sinh x) ^ 2 < (Real.cosh x) ^ 2 := by
    calc
      (Real.sinh x) ^ 2 = (Real.cosh x) ^ 2 - 1 := by simpa using (Real.sinh_sq x)
      _ < (Real.cosh x) ^ 2 := sub_lt_self _ (by norm_num)
  calc
    (Real.tanh x) ^ 2 = (Real.sinh x / Real.cosh x) ^ 2 := by
      simp [Real.tanh_eq_sinh_div_cosh]
    _ = (Real.sinh x) ^ 2 / (Real.cosh x) ^ 2 := by
      simp [div_pow]
    _ < 1 := (div_lt_one hcosh2).2 hsinh_lt

lemma log_cosh_le_mul_tanh (x : ℝ) : Real.log (Real.cosh x) ≤ x * Real.tanh x := by
  let f : ℝ → ℝ := fun x => x * Real.tanh x - Real.log (Real.cosh x)
  have hf0 : f 0 = 0 := by simp [f]

  have hasDerivAt_f : ∀ y : ℝ, HasDerivAt f (y * (sech y) ^ 2) y := by
    intro y
    have hid : HasDerivAt (fun x : ℝ => x) 1 y := by
      simpa using (hasDerivAt_id y)
    have htanh : HasDerivAt Real.tanh ((sech y) ^ 2) y := by
      simpa [sech, Theorem1.sech] using (hasDerivAt_tanh y)
    have hmul :
        HasDerivAt (fun x : ℝ => x * Real.tanh x) (Real.tanh y + y * (sech y) ^ 2) y := by
      simpa [one_mul, mul_assoc, add_assoc] using
        (hid.mul htanh)
    have hlog : HasDerivAt (fun x : ℝ => Real.log (Real.cosh x)) (Real.tanh y) y := by
      have hcosh : HasDerivAt Real.cosh (Real.sinh y) y := Real.hasDerivAt_cosh y
      have hlog : HasDerivAt Real.log ((Real.cosh y)⁻¹) (Real.cosh y) :=
        Real.hasDerivAt_log (Real.cosh_pos y).ne'
      have hcomp := hlog.comp y hcosh
      simpa [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hcomp
    have hf : HasDerivAt f ((Real.tanh y + y * (sech y) ^ 2) - Real.tanh y) y := by
      simpa [f] using hmul.sub hlog
    simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hf

  have hderiv : ∀ y : ℝ, deriv f y = y * (sech y) ^ 2 := fun y => (hasDerivAt_f y).deriv

  have hf_cont : Continuous f := by
    have hlogcosh : Continuous (fun x : ℝ => Real.log (Real.cosh x)) :=
      (Real.continuous_cosh.log (fun x => (Real.cosh_pos x).ne'))
    have htanh : Continuous Real.tanh := continuous_tanh
    have hmul : Continuous (fun x : ℝ => x * Real.tanh x) := continuous_id.mul htanh
    simpa [f, sub_eq_add_neg] using hmul.sub hlogcosh

  have hf_mon : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (D := Set.Ici (0 : ℝ)) (convex_Ici 0) (hf_cont.continuousOn) ?_ ?_
    · intro y _hy
      exact (hasDerivAt_f y).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := le_of_lt (by simpa [Set.mem_Ioi] using hy)
      have hsq : 0 ≤ (sech y) ^ 2 := sq_nonneg (sech y)
      simpa [hderiv y] using mul_nonneg hy0 hsq

  have hf_anti : AntitoneOn f (Set.Iic (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (D := Set.Iic (0 : ℝ)) (convex_Iic 0) (hf_cont.continuousOn) ?_ ?_
    · intro y _hy
      exact (hasDerivAt_f y).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy0 : y ≤ 0 := le_of_lt (by simpa [Set.mem_Iio] using hy)
      have hsq : 0 ≤ (sech y) ^ 2 := sq_nonneg (sech y)
      simpa [hderiv y] using mul_nonpos_of_nonpos_of_nonneg hy0 hsq

  cases le_total 0 x with
  | inl hx0 =>
      have hle : f 0 ≤ f x := hf_mon (a := 0) (b := x) (by simp) (by simpa using hx0) hx0
      have hx : 0 ≤ f x := by simpa [hf0] using hle
      linarith [hx]
  | inr hx0 =>
      have hle : f 0 ≤ f x := hf_anti (a := x) (b := 0) (by simpa using hx0) (by simp) hx0
      have hx : 0 ≤ f x := by simpa [hf0] using hle
      linarith [hx]


lemma spin_term_bound (r : ℝ) :
    Expect (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) ≤
      (Real.sqrt r) * Expect (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) * z) := by
  have hpoint :
      ∀ z : ℝ,
        Real.log (Real.cosh (Real.sqrt r * z)) ≤
          (Real.sqrt r * z) * Real.tanh (Real.sqrt r * z) := by
    intro z
    simpa [mul_assoc, mul_left_comm, mul_comm] using log_cosh_le_mul_tanh (Real.sqrt r * z)

  let f : ℝ → ℝ := fun z => Real.log (Real.cosh (Real.sqrt r * z))
  let h : ℝ → ℝ := fun z => (Real.tanh (Real.sqrt r * z)) * z
  let g : ℝ → ℝ := fun z => (Real.sqrt r) * h z

  have hf_meas : AEStronglyMeasurable f γ := by
    have hmul : Measurable (fun z : ℝ => Real.sqrt r * z) := by
      simpa using (measurable_const.mul measurable_id)
    have hmeas : Measurable (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) := by
      simpa using (hmul.cosh.log)
    simpa [f] using hmeas.aestronglyMeasurable

  have hh_meas : AEStronglyMeasurable h γ := by
    have hmul : Measurable (fun z : ℝ => Real.sqrt r * z) := by
      simpa using (measurable_const.mul measurable_id)
    have ht : Measurable (fun z : ℝ => Real.tanh (Real.sqrt r * z)) := measurable_tanh.comp hmul
    have hmeas : Measurable (fun z : ℝ => Real.tanh (Real.sqrt r * z) * z) := ht.mul measurable_id
    simpa [h] using hmeas.aestronglyMeasurable

  have tanh_norm_le_one : ∀ x : ℝ, ‖Real.tanh x‖ ≤ (1 : ℝ) := by
    intro x
    have hlt : |Real.tanh x| < (1 : ℝ) :=
      (sq_lt_one_iff_abs_lt_one (Real.tanh x)).1 (by simpa using tanh_sq_lt_one x)
    have hle : |Real.tanh x| ≤ (1 : ℝ) := le_of_lt hlt
    simpa [Real.norm_eq_abs] using hle

  have hh_int : Integrable h γ := by
    have hz : Integrable (fun z : ℝ => z) γ := by
      simpa [γ, Theorem1.γ] using
        (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (1 : ℝ≥0)))
          |>.integrable
    have hdom : Integrable (fun z : ℝ => ‖z‖) γ := hz.norm
    have hbound : ∀ᵐ z ∂γ, ‖h z‖ ≤ ‖z‖ := by
      refine ae_of_all _ (fun z => ?_)
      have ht : ‖Real.tanh (Real.sqrt r * z)‖ ≤ (1 : ℝ) := by
        simpa using tanh_norm_le_one (Real.sqrt r * z)
      calc
        ‖h z‖ = ‖Real.tanh (Real.sqrt r * z)‖ * ‖z‖ := by
          simpa [h, norm_mul, mul_assoc, mul_comm, mul_left_comm]
        _ ≤ (1 : ℝ) * ‖z‖ := by gcongr
        _ = ‖z‖ := by simp
    exact Integrable.mono' hdom hh_meas hbound

  have hg_int : Integrable g γ := by
    simpa [g] using hh_int.const_mul (Real.sqrt r)

  have hg_nonneg : ∀ z : ℝ, 0 ≤ g z := by
    intro z
    let y : ℝ := Real.sqrt r * z
    have ht0 : Real.tanh 0 = 0 := by simp
    have hy : 0 ≤ y * Real.tanh y := by
      cases le_total 0 y with
      | inl hy0 =>
          have ht : 0 ≤ Real.tanh y := by
            have := (tanh_strictMono.monotone hy0)
            simpa [ht0] using this
          exact mul_nonneg hy0 ht
      | inr hy0 =>
          have ht : Real.tanh y ≤ 0 := by
            have := (tanh_strictMono.monotone hy0)
            simpa [ht0] using this
          exact mul_nonneg_of_nonpos_of_nonpos hy0 ht
    simpa [g, h, y, mul_assoc, mul_left_comm, mul_comm] using hy

  have hf_int : Integrable f γ := by
    have hbound : ∀ᵐ z ∂γ, ‖f z‖ ≤ ‖g z‖ := by
      refine ae_of_all _ (fun z => ?_)
      have hf_nonneg : 0 ≤ f z := by
        have hcosh : (1 : ℝ) ≤ Real.cosh (Real.sqrt r * z) := Real.one_le_cosh _
        have : 0 ≤ Real.log (Real.cosh (Real.sqrt r * z)) := Real.log_nonneg hcosh
        simpa [f] using this
      have hg_nonneg' : 0 ≤ g z := hg_nonneg z
      have hfg : f z ≤ g z := by
        simpa [f, g, h, mul_assoc, mul_left_comm, mul_comm] using hpoint z
      simpa [Real.norm_eq_abs, abs_of_nonneg hf_nonneg, abs_of_nonneg hg_nonneg'] using hfg
    exact Integrable.mono' hg_int.norm hf_meas hbound

  have hle : f ≤ᵐ[γ] g := by
    refine ae_of_all _ (fun z => ?_)
    simpa [f, g, h, mul_assoc, mul_left_comm, mul_comm] using hpoint z

  have hInt_le : (∫ z : ℝ, f z ∂γ) ≤ ∫ z : ℝ, g z ∂γ :=
    MeasureTheory.integral_mono_ae hf_int hg_int hle

  have hg_fact : (∫ z : ℝ, g z ∂γ) = (Real.sqrt r) * ∫ z : ℝ, h z ∂γ := by
    simp [g, MeasureTheory.integral_const_mul]

  have : Expect f ≤ (Real.sqrt r) * Expect h := by
    simpa [Expect, Theorem1.Expect, hg_fact] using hInt_le

  simpa [f, h] using this

lemma gaussian_integration_by_parts_tanh (r : ℝ) :
    Expect (fun z : ℝ => Real.tanh (Real.sqrt r * z) * z) =
      (Real.sqrt r) * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
  classical
  let v : ℝ≥0 := (1 : ℝ≥0)
  have hv : v ≠ 0 := by simp [v]
  let pdf : ℝ → ℝ := ProbabilityTheory.gaussianPDFReal (0 : ℝ) v
  let pdfE : ℝ → ℝ≥0∞ := ProbabilityTheory.gaussianPDF (0 : ℝ) v

  have hγ : (γ : Measure ℝ) = volume.withDensity pdfE := by
    simpa [γ, v, pdfE] using
      (ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := (0 : ℝ)) (v := v) hv)

  have hmeas_pdfE : Measurable pdfE := by
    simpa [pdfE] using
      (ProbabilityTheory.measurable_gaussianPDF (μ := (0 : ℝ)) (v := v)
        : Measurable (ProbabilityTheory.gaussianPDF (0 : ℝ) v))
  have hflt : ∀ᵐ x ∂volume, pdfE x < ⊤ := by
    refine ae_of_all _ (fun x => ?_)
    simpa [pdfE] using (ProbabilityTheory.gaussianPDF_lt_top (μ := (0 : ℝ)) (v := v) (x := x))

  have integrable_mul_pdf_of_integrable_gaussian :
      ∀ {g : ℝ → ℝ}, Integrable g γ → Integrable (fun x => g x * pdf x) volume := by
    intro g hg
    have hg' : Integrable g (volume.withDensity pdfE) := by
      simpa [hγ] using hg
    have : Integrable (fun x => g x * (pdfE x).toReal) volume :=
      (MeasureTheory.integrable_withDensity_iff hmeas_pdfE hflt (g := g)).1 hg'
    simpa [pdf, pdfE, ProbabilityTheory.toReal_gaussianPDF] using this

  let u : ℝ → ℝ := fun x => Real.tanh (Real.sqrt r * x)
  let u' : ℝ → ℝ := fun x => (Real.sqrt r) * (sech (Real.sqrt r * x)) ^ 2
  let vfun : ℝ → ℝ := pdf
  let v' : ℝ → ℝ := fun x => -x * pdf x

  have hu : ∀ x : ℝ, HasDerivAt u (u' x) x := by
    intro x
    have hinner : HasDerivAt (fun x : ℝ => Real.sqrt r * x) (Real.sqrt r) x := by
      simpa using (hasDerivAt_id x).const_mul (Real.sqrt r)
    have htanh : HasDerivAt Real.tanh ((sech (Real.sqrt r * x)) ^ 2) (Real.sqrt r * x) := by
      simpa [sech, Theorem1.sech] using (hasDerivAt_tanh (Real.sqrt r * x))
    have hcomp := htanh.comp x hinner
    have hd : (sech (Real.sqrt r * x)) ^ 2 * Real.sqrt r = u' x := by
      simp [u', mul_assoc, mul_comm, mul_left_comm]
    have hcomp' : HasDerivAt (fun x : ℝ => Real.tanh (Real.sqrt r * x)) (u' x) x :=
      hcomp.congr_deriv hd
    simpa [u] using hcomp'

  have hv' : ∀ x : ℝ, HasDerivAt vfun (v' x) x := by
    intro x
    have hinner : HasDerivAt (fun x : ℝ => -(x ^ 2) / (2 : ℝ)) (-x) x := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_pow 2 x).neg.div_const (2 : ℝ))
    have hexp :
        HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / (2 : ℝ)))
          (Real.exp (-(x ^ 2) / (2 : ℝ)) * (-x)) x := by
      simpa using (Real.hasDerivAt_exp (-(x ^ 2) / (2 : ℝ))).comp x hinner
    have hmul :
        HasDerivAt (fun x : ℝ => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / (2 : ℝ)))
          ((√(2 * π))⁻¹ * (Real.exp (-(x ^ 2) / (2 : ℝ)) * (-x))) x :=
      hexp.const_mul ((√(2 * π))⁻¹)
    simpa [vfun, v', pdf, v, ProbabilityTheory.gaussianPDFReal_def, pow_two, sub_eq_add_neg,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

  have tanh_norm_le_one : ∀ x : ℝ, ‖Real.tanh x‖ ≤ (1 : ℝ) := by
    intro x
    have hlt : |Real.tanh x| < (1 : ℝ) :=
      (sq_lt_one_iff_abs_lt_one (Real.tanh x)).1 (by simpa using tanh_sq_lt_one x)
    have hle : |Real.tanh x| ≤ (1 : ℝ) := le_of_lt hlt
    simpa [Real.norm_eq_abs] using hle

  have hu_int : Integrable u γ := by
    have h1 : Integrable (fun _x : ℝ => (1 : ℝ)) γ := integrable_const 1
    have hu_meas : AEStronglyMeasurable u γ := by
      have hmul : Measurable (fun x : ℝ => Real.sqrt r * x) := by
        simpa using (measurable_const.mul measurable_id)
      have ht : Measurable (fun x : ℝ => Real.tanh (Real.sqrt r * x)) := measurable_tanh.comp hmul
      simpa [u] using ht.aestronglyMeasurable
    have hbound : ∀ᵐ x ∂γ, ‖u x‖ ≤ (1 : ℝ) := by
      refine ae_of_all _ (fun x => ?_)
      simpa [u] using tanh_norm_le_one (Real.sqrt r * x)
    exact Integrable.mono' h1 hu_meas hbound

  have huz_int : Integrable (fun x : ℝ => u x * x) γ := by
    have hx : Integrable (fun x : ℝ => x) γ := by
      simpa [γ, Theorem1.γ] using
        (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (1 : ℝ≥0)))
          |>.integrable
    have hdom : Integrable (fun x : ℝ => ‖x‖) γ := hx.norm
    have hmeas : AEStronglyMeasurable (fun x : ℝ => u x * x) γ := by
      have hu_meas : Measurable u := by
        have hmul' : Measurable (fun x : ℝ => Real.sqrt r * x) := by
          simpa using (measurable_const.mul measurable_id)
        simpa [u] using (measurable_tanh.comp hmul')
      simpa using (hu_meas.mul measurable_id).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂γ, ‖u x * x‖ ≤ ‖x‖ := by
      refine ae_of_all _ (fun x => ?_)
      have ht : ‖u x‖ ≤ (1 : ℝ) := by
        simpa [u] using tanh_norm_le_one (Real.sqrt r * x)
      calc
        ‖u x * x‖ = ‖u x‖ * ‖x‖ := by
          simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ (1 : ℝ) * ‖x‖ := by gcongr
        _ = ‖x‖ := by simp
    exact Integrable.mono' hdom hmeas hbound

  have sech_sq_le_one : ∀ x : ℝ, (sech x) ^ 2 ≤ (1 : ℝ) := by
    intro x
    have hcosh : (1 : ℝ) ≤ Real.cosh x := Real.one_le_cosh x
    have hpos : (0 : ℝ) < Real.cosh x := Real.cosh_pos x
    have hsech : sech x ≤ (1 : ℝ) := by
      have h' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) hcosh
      simpa [sech, Theorem1.sech] using h'
    have hsech0 : 0 ≤ sech x := by
      have : 0 ≤ (1 / Real.cosh x : ℝ) := le_of_lt (one_div_pos.2 hpos)
      simpa [sech, Theorem1.sech] using this
    have := pow_le_pow_left₀ hsech0 hsech 2
    simpa [one_pow] using this

  have u'_int : Integrable (fun x : ℝ => (sech (Real.sqrt r * x)) ^ 2) γ := by
    have h1 : Integrable (fun _x : ℝ => (1 : ℝ)) γ := integrable_const 1
    have hmeas : AEStronglyMeasurable (fun x : ℝ => (sech (Real.sqrt r * x)) ^ 2) γ := by
      have hmul : Measurable (fun x : ℝ => Real.sqrt r * x) := by
        simpa using (measurable_const.mul measurable_id)
      have hcosh : Measurable (fun x : ℝ => Real.cosh (Real.sqrt r * x)) := by
        simpa using hmul.cosh
      have hsech : Measurable (fun x : ℝ => sech (Real.sqrt r * x)) := by
        have : Measurable (fun x : ℝ => (1 : ℝ) / Real.cosh (Real.sqrt r * x)) :=
          measurable_const.div hcosh
        simpa [sech, Theorem1.sech] using this
      simpa using (hsech.pow_const (2 : ℕ)).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂γ, ‖(sech (Real.sqrt r * x)) ^ 2‖ ≤ (1 : ℝ) := by
      refine ae_of_all _ (fun x => ?_)
      have hle : (sech (Real.sqrt r * x)) ^ 2 ≤ (1 : ℝ) := sech_sq_le_one (Real.sqrt r * x)
      have hnonneg : 0 ≤ (sech (Real.sqrt r * x)) ^ 2 := sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    exact Integrable.mono' h1 hmeas hbound

  have hu'_int : Integrable u' γ := by
    simpa [u'] using u'_int.const_mul (Real.sqrt r)

  have huv : Integrable (u * vfun) volume := by
    simpa [Pi.mul_def, vfun] using
      integrable_mul_pdf_of_integrable_gaussian (g := u) hu_int

  have hu'v : Integrable (u' * vfun) volume := by
    simpa [Pi.mul_def, vfun] using
      integrable_mul_pdf_of_integrable_gaussian (g := u') hu'_int

  have huvx_pdf : Integrable (fun x : ℝ => (u x * x) * pdf x) volume := by
    simpa [Pi.mul_def] using
      integrable_mul_pdf_of_integrable_gaussian (g := fun x : ℝ => u x * x) huz_int

  have huv' : Integrable (u * v') volume := by
    have : (u * v') = fun x : ℝ => -((u x * x) * pdf x) := by
      funext x
      simp [v', mul_assoc, mul_left_comm, mul_comm]
    simpa [this] using huvx_pdf.neg'

  have hibp : (∫ x : ℝ, u x * v' x) = -∫ x : ℝ, u' x * vfun x :=
    MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable hu hv' huv' hu'v huv

  have hibp_neg : -(∫ x : ℝ, (u x * x) * pdf x) = -∫ x : ℝ, u' x * pdf x := by
    have : (∫ x : ℝ, u x * v' x) = ∫ x : ℝ, -((u x * x) * pdf x) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine ae_of_all _ (fun x => ?_)
      ring
    simpa [this, vfun, MeasureTheory.integral_neg] using hibp

  have h_vol : (∫ x : ℝ, (u x * x) * pdf x) = ∫ x : ℝ, u' x * pdf x :=
    (neg_inj.1 hibp_neg)

  have hleft_comm : (∫ x : ℝ, pdf x * (u x * x)) = ∫ x : ℝ, (u x * x) * pdf x := by
    refine MeasureTheory.integral_congr_ae ?_
    refine ae_of_all _ (fun x => ?_)
    ring

  have hright_comm : (∫ x : ℝ, pdf x * u' x) = ∫ x : ℝ, u' x * pdf x := by
    refine MeasureTheory.integral_congr_ae ?_
    refine ae_of_all _ (fun x => ?_)
    ring

  have hL : Expect (fun z : ℝ => u z * z) = ∫ x : ℝ, pdf x * (u x * x) := by
    unfold Expect Theorem1.Expect
    simpa [γ, v, pdf, smul_eq_mul, mul_assoc] using
      (ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := (0 : ℝ)) (v := v)
        (f := fun z : ℝ => u z * z) hv)

  have hR : Expect (fun z : ℝ => u' z) = ∫ x : ℝ, pdf x * u' x := by
    unfold Expect Theorem1.Expect
    simpa [γ, v, pdf, smul_eq_mul, mul_assoc] using
      (ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := (0 : ℝ)) (v := v)
        (f := fun z : ℝ => u' z) hv)

  have hEq : Expect (fun z : ℝ => u z * z) = Expect (fun z : ℝ => u' z) := by
    calc
      Expect (fun z : ℝ => u z * z) = ∫ x : ℝ, pdf x * (u x * x) := hL
      _ = ∫ x : ℝ, (u x * x) * pdf x := by simpa [hleft_comm]
      _ = ∫ x : ℝ, u' x * pdf x := h_vol
      _ = ∫ x : ℝ, pdf x * u' x := by simpa [hright_comm]
      _ = Expect (fun z : ℝ => u' z) := hR.symm

  have hconst :
      Expect (fun z : ℝ => u' z) = (Real.sqrt r) * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
    unfold Expect Theorem1.Expect
    simp [u', MeasureTheory.integral_const_mul, mul_assoc]

  simpa [u] using (hEq.trans hconst)


lemma spin_term_bound_RS (r : ℝ) (hr : 0 ≤ r) :
    - (r / 2) + Expect (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) ≤
      r / 2 := by
  have h := spin_term_bound (r := r)
  have hstein := gaussian_integration_by_parts_tanh (r := r)

  have htanh2_int : Integrable (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) γ := by
    have h1 : Integrable (fun _z : ℝ => (1 : ℝ)) γ := integrable_const 1
    refine h1.mono' (measurable_tanh_sq r).aestronglyMeasurable ?_
    refine ae_of_all _ (fun z => ?_)
    have hle : (Real.tanh (Real.sqrt r * z)) ^ 2 ≤ (1 : ℝ) :=
      le_of_lt (tanh_sq_lt_one (Real.sqrt r * z))
    have hnonneg : 0 ≤ (Real.tanh (Real.sqrt r * z)) ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

  have hq : Expect (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) ≤ 1 := by
    have hle : (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) ≤ᵐ[γ] fun _z : ℝ => (1 : ℝ) := by
      refine ae_of_all _ (fun z => ?_)
      exact le_of_lt (tanh_sq_lt_one (Real.sqrt r * z))
    unfold Expect Theorem1.Expect
    have := MeasureTheory.integral_mono_ae htanh2_int (integrable_const (1 : ℝ)) hle
    simpa [MeasureTheory.integral_const, MeasureTheory.probReal_univ] using this

  have hP : Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) =
      1 - Expect (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) := by
    simpa [S, P] using (S_eq_one_sub_P r)

  have hsqr : (Real.sqrt r) * (Real.sqrt r) = r := by
    simpa [pow_two] using (Real.sq_sqrt hr)

  have hspin : Expect (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) ≤ r := by
    calc
      Expect (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) ≤
          (Real.sqrt r) * Expect (fun z : ℝ => Real.tanh (Real.sqrt r * z) * z) := h
      _ = (Real.sqrt r) * ((Real.sqrt r) * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2)) := by
          simp [hstein, mul_assoc]
      _ = r * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
          calc
            (Real.sqrt r) * ((Real.sqrt r) * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2)) =
                ((Real.sqrt r) * (Real.sqrt r)) * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
                  simpa [mul_assoc] using
                    (mul_assoc (Real.sqrt r) (Real.sqrt r)
                      (Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2))).symm
            _ = r * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
                  simp [hsqr, mul_assoc]
      _ = r * (1 - Expect (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2)) := by
          simp [hP, mul_assoc]
      _ ≤ r * 1 := by
          have hE_nonneg : 0 ≤ Expect (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2) := by
            unfold Expect Theorem1.Expect
            refine MeasureTheory.integral_nonneg (fun z => ?_)
            exact sq_nonneg _
          have hle : (1 - Expect (fun z : ℝ => (Real.tanh (Real.sqrt r * z)) ^ 2)) ≤ 1 :=
            sub_le_self 1 hE_nonneg
          exact mul_le_mul_of_nonneg_left hle hr
      _ = r := by ring
  linarith [hspin]


lemma spin_term_bound_RSStar (κ α q r : ℝ) (hr : 0 ≤ r) (hq : q = P r) :
    RSFunctionalSplit κ α q r ≤
      Real.log 2 + (r * (1 - q) / 2) +
        α * Expect (fun z => Real.log (Φbar ((κ - Real.sqrt q * z) / Real.sqrt (1 - q)))) := by
  have h := spin_term_bound (r := r)
  have hstein := gaussian_integration_by_parts_tanh (r := r)
  have hsqr : (Real.sqrt r) * (Real.sqrt r) = r := by
    simpa [pow_two] using (Real.sq_sqrt hr)

  have hspin :
      Expect (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) ≤ r * (1 - q) := by
    have hle :
        Expect (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) ≤
          r * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
      calc
        Expect (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) ≤
            (Real.sqrt r) * Expect (fun z : ℝ => Real.tanh (Real.sqrt r * z) * z) := h
        _ = (Real.sqrt r) * ((Real.sqrt r) * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2)) := by
            simp [hstein, mul_assoc]
        _ = r * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
            calc
              (Real.sqrt r) * ((Real.sqrt r) * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2)) =
                  ((Real.sqrt r) * (Real.sqrt r)) * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
                    simpa [mul_assoc] using
                      (mul_assoc (Real.sqrt r) (Real.sqrt r)
                        (Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2))).symm
              _ = r * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
                    simp [hsqr, mul_assoc]
    have hS : Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) = 1 - q := by
      simpa [S, P, hq] using (S_eq_one_sub_P r)
    simpa [hS] using hle

  unfold RSFunctionalSplit
  linarith [hspin]


/-! ### Step 2.4: Mills-type bounds -/

private lemma Φbar_le_phi_div {u : ℝ} (hu : 0 < u) : Φbar u ≤ φ u / u := by
  have hMills := MillsBlueprint.Proof.Φbar_eq_phi_div_sub_integral (u := u) hu
  have hMills' : Φbar u = φ u / u - ∫ x in Set.Ioi u, φ x / x ^ 2 := by
    simpa [Φbar_eq_mills, φ_eq_mills] using hMills
  have hnonneg : 0 ≤ ∫ x in Set.Ioi u, φ x / x ^ 2 := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    have hφ_nonneg : 0 ≤ φ x := by
      exact (UniformBoundOfG.φ_pos x).le
    have hx : 0 ≤ x ^ 2 := by nlinarith
    exact div_nonneg hφ_nonneg hx
  have hle : φ u / u - ∫ x in Set.Ioi u, φ x / x ^ 2 ≤ φ u / u :=
    sub_le_self _ hnonneg
  simpa [hMills'] using hle

lemma log_Φbar_le_neg_sq_div_two_sub_log {u : ℝ} (hu : 0 < u) :
    Real.log (Φbar u) ≤ -(u ^ 2) / 2 - Real.log u := by
  have hΦbar_le : Φbar u ≤ φ u / u := Φbar_le_phi_div (u := u) hu
  have hφ_div_le : φ u / u ≤ Real.exp (-(u ^ 2) / 2) / u := by
    have hφ : φ u = Real.exp (-(u ^ 2) / 2) / Real.sqrt (2 * Real.pi) := by
      simp [φ, Theorem1.φ, DecreasingG.φ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
        Real.sqrt_eq_rpow]
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) := by
      have h1 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      simpa using (Real.one_le_sqrt (x := 2 * Real.pi)).2 h1
    have hdiv : Real.exp (-(u ^ 2) / 2) / Real.sqrt (2 * Real.pi) ≤
        Real.exp (-(u ^ 2) / 2) := by
      have h_inv : (1 / Real.sqrt (2 * Real.pi) : ℝ) ≤ 1 := by
        have h' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) hsqrt
        simpa using h'
      have hpos : 0 ≤ Real.exp (-(u ^ 2) / 2) := Real.exp_nonneg _
      calc
        Real.exp (-(u ^ 2) / 2) / Real.sqrt (2 * Real.pi) =
            Real.exp (-(u ^ 2) / 2) * (1 / Real.sqrt (2 * Real.pi)) := by
              simp [div_eq_mul_inv]
        _ ≤ Real.exp (-(u ^ 2) / 2) * 1 := by gcongr
        _ = Real.exp (-(u ^ 2) / 2) := by simp
    have hφ_le : φ u ≤ Real.exp (-(u ^ 2) / 2) := by
      simpa [hφ] using hdiv
    have hdiv' : (0 : ℝ) < u := hu
    exact (div_le_div_of_nonneg_right hφ_le (by exact (le_of_lt hdiv')))
  have hΦbar_le_exp : Φbar u ≤ Real.exp (-(u ^ 2) / 2) / u :=
    le_trans hΦbar_le hφ_div_le
  have hΦbar_pos : 0 < Φbar u := by
    simpa [Φbar, Theorem1.Φbar] using DecreasingG.Φbar_pos u
  have hExp : Φbar u ≤ Real.exp (-(u ^ 2) / 2 - Real.log u) := by
    have hExp_eq : Real.exp (-(u ^ 2) / 2 - Real.log u) =
        Real.exp (-(u ^ 2) / 2) / u := by
      have hu' : u ≠ 0 := ne_of_gt hu
      calc
        Real.exp (-(u ^ 2) / 2 - Real.log u) =
            Real.exp (-(u ^ 2) / 2) * Real.exp (-Real.log u) := by
              simp [sub_eq_add_neg, Real.exp_add, mul_assoc]
        _ = Real.exp (-(u ^ 2) / 2) * (1 / u) := by
              simp [Real.exp_neg, Real.exp_log hu, hu', div_eq_mul_inv, mul_assoc]
        _ = Real.exp (-(u ^ 2) / 2) / u := by
              simp [div_eq_mul_inv, mul_assoc]
    simpa [hExp_eq] using hΦbar_le_exp
  exact (Real.log_le_iff_le_exp hΦbar_pos).2 hExp

lemma log_Φbar_le_neg_sq_div_two {u : ℝ} (hu : 0 < u) :
    Real.log (Φbar u) ≤ -(u ^ 2) / 2 := by
  by_cases h1 : 1 ≤ u
  · have hlogu : 0 ≤ Real.log u := by
      exact Real.log_nonneg h1
    have hmain := log_Φbar_le_neg_sq_div_two_sub_log (u := u) hu
    have hsub : -(u ^ 2) / 2 - Real.log u ≤ -(u ^ 2) / 2 :=
      sub_le_self _ hlogu
    exact le_trans hmain hsub
  ·
    have hu_le1 : u ≤ 1 := le_of_not_ge h1
    have hu0 : 0 ≤ u := le_of_lt hu

    have hΦbar0 : Φbar 0 = (1 / 2 : ℝ) := by
      have hIoi : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2) / 2)) =
          Real.sqrt (2 * Real.pi) / 2 := by
        have h := integral_gaussian_Ioi (1 / 2 : ℝ)
        simpa [mul_assoc, div_eq_mul_inv, mul_comm, mul_left_comm, mul_right_comm] using h
      have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by
        exact Real.sqrt_pos.2 (by positivity)
      have hφ0 : (∫ x in Set.Ioi (0 : ℝ), φ x) = (1 / 2 : ℝ) := by
        have : (∫ x in Set.Ioi (0 : ℝ), φ x) =
            (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
          simp [φ, DecreasingG.φ, MeasureTheory.integral_div]
        rw [this, hIoi]
        field_simp [hsqrt_pos.ne']
      simpa [Φbar, DecreasingG.Φbar, MeasureTheory.integral_Ici_eq_integral_Ioi] using hφ0

    have hanti : Antitone Φbar := by
      intro a b hab
      have hanti' := MillsBlueprint.Proof.Φbar_antitone hab
      simpa [Φbar_eq_mills a, Φbar_eq_mills b] using hanti'

    have hΦbar_le : Φbar u ≤ (1 / 2 : ℝ) := by
      have h := hanti (a := (0 : ℝ)) (b := u) hu0
      simpa [hΦbar0] using h

    have hΦbar_pos : 0 < Φbar u := by
      simpa [Φbar, Theorem1.Φbar] using DecreasingG.Φbar_pos u

    have hlog_le : Real.log (Φbar u) ≤ Real.log (1 / 2 : ℝ) :=
      Real.log_le_log hΦbar_pos hΦbar_le

    have hlog_half : Real.log (1 / 2 : ℝ) ≤ (-(1 / 2 : ℝ)) := by
      have hhalf_le_exp : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
        have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
        nlinarith
      exact (Real.log_le_iff_le_exp (by norm_num : 0 < (1 / 2 : ℝ))).2 hhalf_le_exp

    have hneg : (-(1 / 2 : ℝ)) ≤ -(u ^ 2) / 2 := by
      have hsq : u ^ 2 ≤ (1 : ℝ) := by
        nlinarith [hu_le1, hu0]
      nlinarith [hsq]

    have : Real.log (1 / 2 : ℝ) ≤ -(u ^ 2) / 2 := le_trans hlog_half hneg
    exact le_trans hlog_le this

/-! ### Auxiliary bounds for integrability of `log Φbar` -/

private lemma φ_antitone_on_Ici {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : φ b ≤ φ a := by
  have h' : MillsBlueprint.Proof.φ b ≤ MillsBlueprint.Proof.φ a := by
    have hsq : a ^ 2 ≤ b ^ 2 := by
      nlinarith [ha, hab]
    have hneg : (-(b ^ 2) / 2) ≤ (-(a ^ 2) / 2) := by
      nlinarith [hsq]
    have hexp : Real.exp (-(b ^ 2) / 2) ≤ Real.exp (-(a ^ 2) / 2) :=
      (Real.exp_le_exp).2 hneg
    have hconst : 0 ≤ (1 / Real.sqrt (2 * Real.pi) : ℝ) := by
      have hpi : (0 : ℝ) < Real.pi := by simpa using Real.pi_pos
      have h2pi : (0 : ℝ) < (2 * Real.pi : ℝ) := by nlinarith
      have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 h2pi
      exact (le_of_lt (one_div_pos.2 hsqrt))
    have :
        (1 / Real.sqrt (2 * Real.pi) : ℝ) * Real.exp (-(b ^ 2) / 2) ≤
          (1 / Real.sqrt (2 * Real.pi) : ℝ) * Real.exp (-(a ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hexp hconst
    simpa [MillsBlueprint.Proof.φ] using this
  simpa [φ_eq_mills] using h'

private lemma Φbar_ge_phi_add_one {u : ℝ} (hu : 0 ≤ u) : φ (u + 1) ≤ Φbar u := by
  have hΦbar : Φbar u = ∫ x in Set.Ioi u, φ x := by
    simp [Φbar, Theorem1.Φbar, DecreasingG.Φbar, MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hφ_int : Integrable (fun x : ℝ => φ x) := by
    have hφ : (fun x : ℝ => φ x) = ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) := by
      funext x
      simp [φ, Theorem1.φ, DecreasingG.φ, ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv,
        mul_comm, mul_left_comm]
    simpa [hφ] using
      (ProbabilityTheory.integrable_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
  have hpoint : ∀ x ∈ Set.Ioc u (u + 1), φ (u + 1) ≤ φ x := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1, hu]
    have hxle : x ≤ u + 1 := hx.2
    have hanti := φ_antitone_on_Ici (a := x) (b := u + 1) hx0 hxle
    simpa using hanti
  have hconst_int :
      Integrable (fun _x : ℝ => (φ (u + 1) : ℝ))
        (Measure.restrict volume (Set.Ioc u (u + 1))) := by
    simpa using
      (integrable_const (μ := Measure.restrict volume (Set.Ioc u (u + 1))) (φ (u + 1)))
  have hφ_int' :
      Integrable (fun x : ℝ => φ x) (Measure.restrict volume (Set.Ioc u (u + 1))) := by
    simpa using (hφ_int.restrict (s := Set.Ioc u (u + 1)))
  have hconst_le :
      ∫ x in Set.Ioc u (u + 1), (φ (u + 1) : ℝ) ≤ ∫ x in Set.Ioc u (u + 1), φ x := by
    refine MeasureTheory.integral_mono_ae (μ := Measure.restrict volume (Set.Ioc u (u + 1)))
      hconst_int hφ_int' ?_
    have hmem :
        ∀ᵐ x ∂(Measure.restrict volume (Set.Ioc u (u + 1))), x ∈ Set.Ioc u (u + 1) :=
      MeasureTheory.ae_restrict_mem measurableSet_Ioc
    refine hmem.mono ?_
    intro x hx
    exact hpoint x hx
  have hlen :
      ∫ x in Set.Ioc u (u + 1), (φ (u + 1) : ℝ) = φ (u + 1) := by
    have hlen' : (u + 1) - u = (1 : ℝ) := by ring
    simp [MeasureTheory.integral_const, hlen', one_mul]
  have h1 : φ (u + 1) ≤ ∫ x in Set.Ioc u (u + 1), φ x := by
    simpa [hlen] using hconst_le
  have hmono :
      ∫ x in Set.Ioc u (u + 1), φ x ≤ ∫ x in Set.Ioi u, φ x := by
    have hfi_on : IntegrableOn φ (Set.Ioi u) (volume : Measure ℝ) := hφ_int.integrableOn
    have h_nonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi u)] φ := by
      refine ae_of_all _ (fun x => (UniformBoundOfG.φ_pos x).le)
    have hst : (Set.Ioc u (u + 1) : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Ioi u := by
      refine ae_of_all _ (fun x hx => hx.1)
    exact MeasureTheory.setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := φ)
      (s := Set.Ioc u (u + 1)) (t := Set.Ioi u) hfi_on h_nonneg hst
  have h1' : φ (u + 1) ≤ ∫ x in Set.Ioi u, φ x := by
    exact le_trans h1 (by simpa [hΦbar] using hmono)
  simpa [hΦbar] using h1'

private def Cφ : ℝ := Real.log 2 + Real.log (Real.sqrt (2 * Real.pi))

private lemma Cφ_nonneg : 0 ≤ Cφ := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by
    have h6 : (6 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have h1 : (1 : ℝ) ≤ (6 : ℝ) := by norm_num
    exact le_trans h1 (le_of_lt h6)
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) :=
    (Real.one_le_sqrt (x := (2 * Real.pi))).2 h2pi
  have hlogsqrt : 0 ≤ Real.log (Real.sqrt (2 * Real.pi)) := Real.log_nonneg hsqrt_ge_one
  dsimp [Cφ]
  linarith

private lemma log_Φbar_abs_bound (u : ℝ) :
    ‖Real.log (Φbar u)‖ ≤ (u + 1) ^ 2 / 2 + Cφ := by
  by_cases hu : 0 ≤ u
  ·
    have hφ_le : φ (u + 1) ≤ Φbar u := Φbar_ge_phi_add_one (u := u) hu
    have hφ_pos : 0 < φ (u + 1) := by
      simpa [φ] using (UniformBoundOfG.φ_pos (u + 1))
    have hΦbar_pos : 0 < Φbar u := by
      simpa [Φbar, Theorem1.Φbar] using DecreasingG.Φbar_pos u
    have hlog_le : Real.log (φ (u + 1)) ≤ Real.log (Φbar u) :=
      Real.log_le_log hφ_pos hφ_le
    have hΦbar_le_one : Φbar u ≤ 1 := by
      have htotal : (∫ x : ℝ, φ x) = 1 := by
        have hv : (1 : ℝ≥0) ≠ 0 := by simp
        simpa [φ_eq_gaussianPDFReal] using
          (ProbabilityTheory.integral_gaussianPDFReal_eq_one (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)
      have hsubset : Set.Ici u ⊆ (Set.univ : Set ℝ) := by intro x hx; trivial
      have hφ_nonneg : ∀ x : ℝ, 0 ≤ φ x := by
        intro x; exact (UniformBoundOfG.φ_pos x).le
      have hφ_int : Integrable (fun x : ℝ => φ x) := by
        simpa [φ_eq_gaussianPDFReal] using
          (ProbabilityTheory.integrable_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
      have hmono :
          ∫ x in Set.Ici u, φ x ≤ ∫ x : ℝ, φ x := by
        have hfi : IntegrableOn φ (Set.univ : Set ℝ) (volume : Measure ℝ) := by
          simpa using (hφ_int.integrableOn (s := (Set.univ : Set ℝ)))
        have hnonneg : 0 ≤ᶠ[ae ((volume : Measure ℝ).restrict (Set.univ : Set ℝ))] φ :=
          Filter.Eventually.of_forall (fun x => hφ_nonneg x)
        have hst : (Set.Ici u : Set ℝ) ≤ᶠ[ae (volume : Measure ℝ)] (Set.univ : Set ℝ) :=
          Filter.Eventually.of_forall (fun x hx => hsubset hx)
        have h :=
          MeasureTheory.setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := φ)
            (s := Set.Ici u) (t := (Set.univ : Set ℝ)) hfi hnonneg hst
        simpa using h
      simpa [Φbar, Theorem1.Φbar, DecreasingG.Φbar, htotal] using hmono
    have hlog_nonpos : Real.log (Φbar u) ≤ 0 := by
      have hΦbar_pos' : 0 < Φbar u := hΦbar_pos
      have hExp : Φbar u ≤ Real.exp 0 := by simpa using hΦbar_le_one
      exact (Real.log_le_iff_le_exp hΦbar_pos').2 hExp
    have hnorm :
        ‖Real.log (Φbar u)‖ = -Real.log (Φbar u) := by
      simpa [Real.norm_eq_abs, abs_of_nonpos hlog_nonpos]
    have hlog_ge : Real.log (φ (u + 1)) ≤ Real.log (Φbar u) := hlog_le
    have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by
      have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) :=
        Real.sqrt_pos.2 (by positivity)
      exact hsqrt_pos.ne'
    have hlog_phi :
        -Real.log (φ (u + 1)) = (u + 1) ^ 2 / 2 + Real.log (Real.sqrt (2 * Real.pi)) := by
      have hlog :
          Real.log (Real.exp (-((u + 1) ^ 2) / 2) / Real.sqrt (2 * Real.pi)) =
            Real.log (Real.exp (-((u + 1) ^ 2) / 2)) - Real.log (Real.sqrt (2 * Real.pi)) := by
        simpa using Real.log_div (Real.exp_ne_zero (-((u + 1) ^ 2) / 2)) hsqrt_ne
      dsimp [φ, Theorem1.φ, DecreasingG.φ]
      rw [hlog]
      simp [Real.log_exp]
      ring
    have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hC :
        (u + 1) ^ 2 / 2 + Real.log (Real.sqrt (2 * Real.pi)) ≤ (u + 1) ^ 2 / 2 + Cφ := by
      dsimp [Cφ]
      linarith [hlog2_nonneg]
    have hneg : -Real.log (Φbar u) ≤ -Real.log (φ (u + 1)) := neg_le_neg hlog_ge
    have hbound1 :
        -Real.log (Φbar u) ≤ (u + 1) ^ 2 / 2 + Real.log (Real.sqrt (2 * Real.pi)) := by
      simpa [hlog_phi] using hneg
    have hbound' : -Real.log (Φbar u) ≤ (u + 1) ^ 2 / 2 + Cφ := le_trans hbound1 hC
    simpa [hnorm] using hbound'
  ·
    have hu' : u ≤ 0 := le_of_not_ge hu
    have hanti : Antitone Φbar := by
      intro a b hab
      have hanti' := MillsBlueprint.Proof.Φbar_antitone hab
      simpa [Φbar_eq_mills a, Φbar_eq_mills b] using hanti'
    have hΦbar0 : Φbar 0 = (1 / 2 : ℝ) := by
      have hIoi : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2) / 2)) =
          Real.sqrt (2 * Real.pi) / 2 := by
        have h := integral_gaussian_Ioi (1 / 2 : ℝ)
        simpa [mul_assoc, div_eq_mul_inv, mul_comm, mul_left_comm, mul_right_comm] using h
      have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by
        exact Real.sqrt_pos.2 (by positivity)
      have hφ0 : (∫ x in Set.Ioi (0 : ℝ), φ x) = (1 / 2 : ℝ) := by
        have : (∫ x in Set.Ioi (0 : ℝ), φ x) =
            (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
          simp [φ, DecreasingG.φ, MeasureTheory.integral_div]
        rw [this, hIoi]
        field_simp [hsqrt_pos.ne']
      simpa [Φbar, DecreasingG.Φbar, MeasureTheory.integral_Ici_eq_integral_Ioi] using hφ0
    have hΦbar_ge : (1 / 2 : ℝ) ≤ Φbar u := by
      have h := hanti (a := u) (b := 0) hu'
      simpa [hΦbar0] using h
    have hΦbar_pos : 0 < Φbar u := by
      simpa [Φbar, Theorem1.Φbar] using DecreasingG.Φbar_pos u
    have hlog_ge : Real.log (1 / 2 : ℝ) ≤ Real.log (Φbar u) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)) hΦbar_ge
    have hlog_nonpos : Real.log (Φbar u) ≤ 0 := by
      have hΦbar_le_one : Φbar u ≤ 1 := by
        have htotal : (∫ x : ℝ, φ x) = 1 := by
          have hv : (1 : ℝ≥0) ≠ 0 := by simp
          simpa [φ_eq_gaussianPDFReal] using
            (ProbabilityTheory.integral_gaussianPDFReal_eq_one (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)
        have hsubset : Set.Ici u ⊆ (Set.univ : Set ℝ) := by intro x hx; trivial
        have hφ_nonneg : ∀ x : ℝ, 0 ≤ φ x := by
          intro x; exact (UniformBoundOfG.φ_pos x).le
        have hφ_int : Integrable (fun x : ℝ => φ x) := by
          simpa [φ_eq_gaussianPDFReal] using
            (ProbabilityTheory.integrable_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
        have hmono :
            ∫ x in Set.Ici u, φ x ≤ ∫ x : ℝ, φ x := by
          have hfi : IntegrableOn φ (Set.univ : Set ℝ) (volume : Measure ℝ) := by
            simpa using (hφ_int.integrableOn (s := (Set.univ : Set ℝ)))
          have hnonneg : 0 ≤ᶠ[ae ((volume : Measure ℝ).restrict (Set.univ : Set ℝ))] φ :=
            Filter.Eventually.of_forall (fun x => hφ_nonneg x)
          have hst : (Set.Ici u : Set ℝ) ≤ᶠ[ae (volume : Measure ℝ)] (Set.univ : Set ℝ) :=
            Filter.Eventually.of_forall (fun x hx => hsubset hx)
          have h :=
            MeasureTheory.setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := φ)
              (s := Set.Ici u) (t := (Set.univ : Set ℝ)) hfi hnonneg hst
          simpa using h
        simpa [Φbar, Theorem1.Φbar, DecreasingG.Φbar, htotal] using hmono
      exact (Real.log_le_iff_le_exp hΦbar_pos).2 (by simpa using hΦbar_le_one)
    have hnorm :
        ‖Real.log (Φbar u)‖ = -Real.log (Φbar u) := by
      simpa [Real.norm_eq_abs, abs_of_nonpos hlog_nonpos]
    have hbound : -Real.log (Φbar u) ≤ Cφ := by
      have hneg : -Real.log (Φbar u) ≤ -Real.log (1 / 2 : ℝ) := neg_le_neg hlog_ge
      have hloghalf : -Real.log (1 / 2 : ℝ) = Real.log (2 : ℝ) := by
        have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
        have hlog : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
          simpa [hhalf] using (Real.log_inv (2 : ℝ))
        linarith [hlog]
      have hlogsqrt_nonneg : 0 ≤ Real.log (Real.sqrt (2 * Real.pi)) := by
        have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by
          have h6 : (6 : ℝ) < 2 * Real.pi := by
            nlinarith [Real.pi_gt_three]
          have h1 : (1 : ℝ) ≤ (6 : ℝ) := by norm_num
          exact le_trans h1 (le_of_lt h6)
        have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) :=
          (Real.one_le_sqrt (x := (2 * Real.pi))).2 h2pi
        exact Real.log_nonneg hsqrt_ge_one
      have hlog2_le_C : Real.log (2 : ℝ) ≤ Cφ := by
        dsimp [Cφ]
        linarith [hlogsqrt_nonneg]
      have hlog2 : -Real.log (Φbar u) ≤ Real.log (2 : ℝ) := by
        simpa [hloghalf] using hneg
      exact le_trans hlog2 hlog2_le_C
    have hnonneg : 0 ≤ (u + 1) ^ 2 / 2 := by
      have : 0 ≤ (u + 1) ^ 2 := sq_nonneg _
      nlinarith
    have hbound' : -Real.log (Φbar u) ≤ (u + 1) ^ 2 / 2 + Cφ := by
      linarith [hbound, hnonneg]
    simpa [hnorm] using hbound'

private lemma Φ_pos (u : ℝ) : 0 < Φ u := by
  have hφ_int : Integrable (fun x : ℝ => φ x) := by
    have hφ : (fun x : ℝ => φ x) = ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) := by
      funext x
      simp [φ, Theorem1.φ, DecreasingG.φ, ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv,
        mul_comm, mul_left_comm]
    simpa [hφ] using
      (ProbabilityTheory.integrable_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
  have htotal : (∫ x : ℝ, φ x) = 1 := by
    have hv : (1 : ℝ≥0) ≠ 0 := by simp
    simpa [φ, Theorem1.φ, DecreasingG.φ, ProbabilityTheory.gaussianPDFReal,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (ProbabilityTheory.integral_gaussianPDFReal_eq_one (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)
  have hsplit :
      (∫ x : ℝ, φ x) = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
    have hdis : Disjoint (Set.Iic u) (Set.Ioi u) := Set.Iic_disjoint_Ioi (a := u) (b := u) le_rfl
    have hunion :
        (∫ x in (Set.Iic u ∪ Set.Ioi u : Set ℝ), φ x) =
          (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
      simpa using
        (MeasureTheory.setIntegral_union (μ := (volume : Measure ℝ)) (f := φ)
          (s := Set.Iic u) (t := Set.Ioi u) hdis measurableSet_Ioi
          (hφ_int.integrableOn) (hφ_int.integrableOn))
    have hset : (Set.Iic u ∪ Set.Ioi u : Set ℝ) = Set.univ := by
      simpa using (Set.Iic_union_Ioi (a := u))
    calc
      (∫ x : ℝ, φ x) = ∫ x in (Set.Iic u ∪ Set.Ioi u : Set ℝ), φ x := by
        simp [hset]
      _ = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := hunion
  have hΦbar : Φbar u = ∫ x in Set.Ioi u, φ x := by
    simp [Φbar, Theorem1.Φbar, DecreasingG.Φbar, MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hfi : IntervalIntegrable φ volume (u - 1) u := by
    simpa using (hφ_int.intervalIntegrable)
  have hab : u - 1 < u := by linarith
  have hpos_interval : 0 < ∫ x : ℝ in (u - 1)..u, φ x := by
    exact
      intervalIntegral.intervalIntegral_pos_of_pos
        (f := φ) (a := u - 1) (b := u) hfi (fun x => UniformBoundOfG.φ_pos x) hab
  have hIoc :
      (∫ x in Set.Ioc (u - 1) u, φ x) = ∫ x : ℝ in (u - 1)..u, φ x := by
    have hle : u - 1 ≤ u := by linarith
    simpa using
      (intervalIntegral.integral_of_le (μ := volume) (f := φ) (a := u - 1) (b := u) hle).symm
  have hpos_Ioc : 0 < ∫ x in Set.Ioc (u - 1) u, φ x := by
    simpa [hIoc] using hpos_interval
  have hmono : (∫ x in Set.Ioc (u - 1) u, φ x) ≤ ∫ x in Set.Iic u, φ x := by
    have hfi_on : IntegrableOn φ (Set.Iic u) (volume : Measure ℝ) := hφ_int.integrableOn
    have h_nonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Iic u)] φ := by
      refine ae_of_all _ (fun x => (UniformBoundOfG.φ_pos x).le)
    have hst : (Set.Ioc (u - 1) u : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Iic u := by
      refine ae_of_all _ (fun x hx => ?_)
      exact hx.2
    exact MeasureTheory.setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := φ)
      (s := Set.Ioc (u - 1) u) (t := Set.Iic u) hfi_on h_nonneg hst
  have hIic_pos : 0 < ∫ x in Set.Iic u, φ x := lt_of_lt_of_le hpos_Ioc hmono
  have hIoi_eq : ∫ x in Set.Ioi u, φ x = 1 - ∫ x in Set.Iic u, φ x := by
    linarith [hsplit, htotal]
  have hΦbar_lt : Φbar u < 1 := by
    have : ∫ x in Set.Ioi u, φ x < 1 := by linarith [hIic_pos, hIoi_eq]
    simpa [hΦbar] using this
  have hΦpos : 0 < 1 - Φbar u := sub_pos.2 hΦbar_lt
  simpa [Φ] using hΦpos

/-! ### Step 2.5: compare `B(κ,q)` and `A_n` (and bound the gap) -/

lemma E_sq_ge_uplus_sq (u : ℝ) : (E u) ^ 2 ≥ (max u 0) ^ 2 := by
  by_cases hu : 0 < u
  ·
    have hΦbar_le : Φbar u ≤ φ u / u := Φbar_le_phi_div (u := u) hu
    have hΦbar_pos : 0 < Φbar u := by
      simpa [Φbar, Theorem1.Φbar] using DecreasingG.Φbar_pos u
    have hmul : u * Φbar u ≤ φ u := by
      have h := mul_le_mul_of_nonneg_left hΦbar_le (le_of_lt hu)
      have hu_ne : u ≠ 0 := ne_of_gt hu
      calc
        u * Φbar u ≤ u * (φ u / u) := h
        _ = φ u := by field_simp [hu_ne]
    have hE_ge : u ≤ φ u / Φbar u := by
      exact (le_div_iff₀ hΦbar_pos).2 hmul
    have hE_ge' : u ≤ E u := by
      simpa [E, Theorem1.E, DecreasingG.E] using hE_ge
    have hsq : u ^ 2 ≤ (E u) ^ 2 := by
      exact pow_le_pow_left₀ (le_of_lt hu) hE_ge' 2
    have hmax : max u 0 = u := by
      simp [max_eq_left, le_of_lt hu]
    simpa [hmax] using hsq
  ·
    have hu' : u ≤ 0 := le_of_not_gt hu
    have hmax : max u 0 = 0 := by simp [max_eq_right, hu']
    have : 0 ≤ (E u) ^ 2 := by nlinarith
    simpa [hmax] using this

lemma exists_C0_E_sq_sub_uplus_sq_le :
    ∃ C0 : ℝ, ∀ u : ℝ, 0 ≤ (E u) ^ 2 - (max u 0) ^ 2 ∧ (E u) ^ 2 - (max u 0) ^ 2 ≤ C0 := by
  refine ⟨(9 : ℝ), ?_⟩
  intro u
  constructor
  · have h := E_sq_ge_uplus_sq u
    linarith
  · by_cases h1 : u ≤ 1
    ·
      have hE : E u ≤ max u 0 + 2 := by
        simpa [E] using Theorem1.Theorem1.E_le_max_u_zero_add_two u
      have hmax_le : max u 0 ≤ 1 := by
        refine max_le_iff.mpr ?_
        constructor
        · exact h1
        · norm_num
      have hmax_plus : max u 0 + 2 ≤ 3 := by
        nlinarith [hmax_le]
      have hE_le3 : E u ≤ 3 := le_trans hE hmax_plus
      have hE_nonneg : 0 ≤ E u := (UniformBoundOfG.E_pos u).le
      have hE2 : (E u) ^ 2 ≤ 9 := by
        have h' : (E u) ^ 2 ≤ (3 : ℝ) ^ 2 := pow_le_pow_left₀ hE_nonneg hE_le3 2
        nlinarith [h']
      have hnonneg : 0 ≤ (max u 0) ^ 2 := sq_nonneg _
      have hsub : (E u) ^ 2 - (max u 0) ^ 2 ≤ (E u) ^ 2 := sub_le_self _ hnonneg
      exact le_trans hsub hE2
    ·
      have hu : 1 < u := lt_of_not_ge h1
      have hu_pos : 0 < u := lt_trans (by norm_num) hu
      have hE_le : E u ≤ u + 1 / u := by
        have h := MillsBlueprint.Proof.E_le_add_inv (u := u) hu_pos
        simpa [E, Theorem1.E, Theorem1.bridge_E_eq u] using h
      have hE2 : (E u) ^ 2 ≤ (u + 1 / u) ^ 2 := by
        exact pow_le_pow_left₀ (le_of_lt (UniformBoundOfG.E_pos u)) hE_le 2
      have hmax : max u 0 = u := by
        simp [max_eq_left, le_of_lt hu_pos]
      have hcalc : (u + 1 / u) ^ 2 - u ^ 2 ≤ 3 := by
        have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
        have h1u : (1 / u ^ 2 : ℝ) ≤ 1 := by
          have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith [hu1]
          have : (1 : ℝ) / u ^ 2 ≤ (1 : ℝ) / (1 : ℝ) :=
            one_div_le_one_div_of_le (by norm_num) hu2
          simpa using this
        have hEq : (u + 1 / u) ^ 2 - u ^ 2 = 2 + 1 / u ^ 2 := by
          have hu_ne : u ≠ 0 := ne_of_gt hu_pos
          field_simp [hu_ne]
          ring
        nlinarith [hEq, h1u]
      have hdiff : (E u) ^ 2 - u ^ 2 ≤ 3 := by
        have h' : (E u) ^ 2 - u ^ 2 ≤ (u + 1 / u) ^ 2 - u ^ 2 := by
          linarith [hE2]
        exact le_trans h' hcalc
      simpa [hmax] using (le_trans hdiff (by norm_num : (3 : ℝ) ≤ 9))

/-! ## 3. Sequential formulation (matches the proof in `main.tex`) -/

section Seq

variable (κ : ℝ) (hκ : 0 ≤ κ)
variable (α : ℕ → ℝ)
variable (hα : ∀ n, 0 < α n ∧ α n < αc κ)

abbrev qn (n : ℕ) : ℝ := qSol κ (α n) hκ (hα n).1 (hα n).2
abbrev rn (n : ℕ) : ℝ := rSol κ (α n) hκ (hα n).1 (hα n).2
abbrev εn (n : ℕ) : ℝ := 1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n

abbrev Un (n : ℕ) (z : ℝ) : ℝ :=
  U κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) z

abbrev An (n : ℕ) : ℝ :=
  Expect fun z => (max (κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * z) 0) ^ 2

private lemma integrable_log_Φbar_Un (n : ℕ) :
    Integrable (fun z : ℝ => Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) γ := by
  have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
    simpa [γ, Theorem1.γ] using
      (MeasureTheory.MemLp.integrable_sq
        (ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))))
  let ε : ℝ := εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
  let q : ℝ := qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
  have hq_lt1 : q < 1 := by
    simpa [q, qn] using
      (Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2).2.1
  have hεpos : 0 < ε := by
    have : 0 ≤ q := by
      simpa [q, qn] using
        (Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2).1
    simpa [ε, εn] using sub_pos.2 hq_lt1
  have hmeas :
      AEStronglyMeasurable
        (fun z : ℝ => Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) γ := by
    have hUn_meas :
        Measurable (fun z : ℝ => Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) := by
      dsimp [Un, U, Theorem1.U]
      fun_prop
    have hcontΦbar : Continuous Φbar := by
      simpa [Φbar, Theorem1.Φbar, UniformBoundOfG.Φbar] using
        (UniformBoundOfG.Φbar_continuous : Continuous UniformBoundOfG.Φbar)
    have hΦbar_meas : Measurable Φbar := hcontΦbar.measurable
    have hmeasΦbarU :
        Measurable (fun z : ℝ => Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) :=
      hΦbar_meas.comp hUn_meas
    have hmeasLog :
        Measurable (fun z : ℝ => Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) :=
      Real.measurable_log.comp hmeasΦbarU
    exact hmeasLog.aestronglyMeasurable
  let a : ℝ := κ / Real.sqrt ε + 1
  let b : ℝ := Real.sqrt q / Real.sqrt ε
  have hbound : ∀ᵐ z ∂γ,
      ‖Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))‖ ≤
        ((a - b * z) ^ 2) / 2 + Cφ := by
    refine ae_of_all _ (fun z => ?_)
    have hU :
        Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z + 1 = a - b * z := by
      dsimp [Un, U, Theorem1.U, ε, εn, q, qn, a, b]
      ring_nf
    simpa [hU] using
      (log_Φbar_abs_bound (u := Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))
  have hquad_int :
      Integrable (fun z : ℝ => ((a - b * z) ^ 2) / 2 + Cφ) γ := by
    have hbound' : ∀ᵐ z ∂γ, ‖((a - b * z) ^ 2) / 2 + Cφ‖ ≤
        (|a| + |b| * ‖z‖) ^ 2 + Cφ := by
      refine ae_of_all _ (fun z => ?_)
      have hnonneg : 0 ≤ ((a - b * z) ^ 2) / 2 + Cφ := by
        have hsq : 0 ≤ ((a - b * z) ^ 2) / 2 := by
          have : 0 ≤ (a - b * z) ^ 2 := sq_nonneg _
          nlinarith
        linarith [hsq, Cφ_nonneg]
      have hnorm : ‖((a - b * z) ^ 2) / 2 + Cφ‖ =
          ((a - b * z) ^ 2) / 2 + Cφ := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hle :
          ((a - b * z) ^ 2) / 2 ≤ (|a| + |b| * ‖z‖) ^ 2 := by
        have h1 : |a - b * z| ≤ |a| + |b| * ‖z‖ := by
          have h := abs_sub a (b * z)
          have hbz : |b * z| = |b| * ‖z‖ := by
            calc
              |b * z| = |b| * |z| := by
                simpa [abs_mul] using (abs_mul b z)
              _ = |b| * ‖z‖ := by
                rw [← Real.norm_eq_abs z]
          simpa [hbz] using h
        have h1' : |a - b * z| ≤ |(|a| + |b| * ‖z‖)| := by
          exact le_trans h1 (le_abs_self _)
        have h2 : (a - b * z) ^ 2 ≤ (|a| + |b| * ‖z‖) ^ 2 := by
          exact (sq_le_sq).2 h1'
        nlinarith [h2]
      nlinarith [hnorm, hle]
    have hpoly_int :
        Integrable (fun z : ℝ => (|a| + |b| * ‖z‖) ^ 2 + Cφ) γ := by
      have hnorm_int : Integrable (fun z : ℝ => ‖z‖ ^ 2) γ := by
        simpa [Real.norm_eq_abs, abs_pow] using hsq_int
      have hconst_int : Integrable (fun _z : ℝ => (Cφ : ℝ)) γ := integrable_const _
      have hlinear_int : Integrable (fun z : ℝ => (|a| + |b| * ‖z‖) ^ 2) γ := by
        have hbound'' : ∀ᵐ z ∂γ,
            ‖(|a| + |b| * ‖z‖) ^ 2‖ ≤ 2 * |a| ^ 2 + 2 * |b| ^ 2 * ‖z‖ ^ 2 := by
          refine ae_of_all _ (fun z => ?_)
          have hab :
              2 * |a| * (|b| * ‖z‖) ≤ |a| ^ 2 + (|b| * ‖z‖) ^ 2 :=
            two_mul_le_add_sq |a| (|b| * ‖z‖)
          have hsq :
              (|a| + |b| * ‖z‖) ^ 2 ≤ 2 * |a| ^ 2 + 2 * (|b| * ‖z‖) ^ 2 := by
            calc
              (|a| + |b| * ‖z‖) ^ 2 =
                  |a| ^ 2 + (|b| * ‖z‖) ^ 2 + 2 * |a| * (|b| * ‖z‖) := by
                ring
              _ ≤ |a| ^ 2 + (|b| * ‖z‖) ^ 2 + (|a| ^ 2 + (|b| * ‖z‖) ^ 2) := by
                have := add_le_add_left hab (|a| ^ 2 + (|b| * ‖z‖) ^ 2)
                simpa [add_assoc, add_left_comm, add_comm] using this
              _ = 2 * |a| ^ 2 + 2 * (|b| * ‖z‖) ^ 2 := by
                ring
          have h' : (|b| * ‖z‖) ^ 2 = |b| ^ 2 * ‖z‖ ^ 2 := by ring
          have hsq' :
              (|a| + |b| * ‖z‖) ^ 2 ≤ 2 * |a| ^ 2 + 2 * |b| ^ 2 * ‖z‖ ^ 2 := by
            nlinarith [hsq, h']
          simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (|a| + |b| * ‖z‖))] using hsq'
        have hpoly_int' :
            Integrable (fun z : ℝ => 2 * |a| ^ 2 + 2 * |b| ^ 2 * ‖z‖ ^ 2) γ := by
          have h1 : Integrable (fun _z : ℝ => (2 * |a| ^ 2 : ℝ)) γ := integrable_const _
          have h2 : Integrable (fun z : ℝ => (2 * |b| ^ 2) * ‖z‖ ^ 2) γ :=
            (hnorm_int.const_mul (2 * |b| ^ 2))
          simpa [add_comm, add_left_comm, add_assoc] using h1.add h2
        exact Integrable.mono' hpoly_int' (by fun_prop) hbound''
      simpa [add_comm, add_left_comm, add_assoc] using hlinear_int.add hconst_int
    exact Integrable.mono' hpoly_int (by fun_prop) hbound'
  exact Integrable.mono' hquad_int hmeas hbound

private lemma Expect_max_Un_sq (n : ℕ) :
    Expect (fun z : ℝ => (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) =
      An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n / εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
  have hspec := Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2
  have hq_lt1 : qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n < 1 := by
    simpa [qn] using hspec.2.1
  have hεpos : 0 < εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
    simpa [εn, qn] using sub_pos.2 hq_lt1
  have hεne :
      εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≠ 0 := ne_of_gt hεpos
  have hpoint :
      ∀ z : ℝ,
        (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 =
          (max (κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * z) 0) ^ 2 /
            εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
    intro z
    set ε : ℝ := εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
    set q : ℝ := qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
    have hεpos' : 0 < ε := by
      simpa [ε] using hεpos
    have hεpos'' : 0 < Real.sqrt ε := Real.sqrt_pos.2 hεpos'
    have hUn :
        Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z =
          (κ - Real.sqrt q * z) / Real.sqrt ε := by
      dsimp [Un, U, Theorem1.U, ε, εn, q, qn]
    by_cases h : 0 ≤ κ - Real.sqrt q * z
    ·
      have hUpos : 0 ≤ Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z := by
        have : 0 ≤ (κ - Real.sqrt q * z) := h
        have : 0 ≤ (κ - Real.sqrt q * z) / Real.sqrt ε := by
          exact div_nonneg this (le_of_lt hεpos'')
        simpa [hUn] using this
      have hmax1 : max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 =
          Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z := by
        simp [max_eq_left, hUpos]
      have hmax2 : max (κ - Real.sqrt q * z) 0 = κ - Real.sqrt q * z := by
        simp [max_eq_left, h]
      have hx : 0 ≤ κ - z * Real.sqrt q := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      have hmaxL :
          max ((κ - z * Real.sqrt q) * (Real.sqrt ε)⁻¹) 0 =
            (κ - z * Real.sqrt q) * (Real.sqrt ε)⁻¹ := by
        have hinv : 0 ≤ (Real.sqrt ε)⁻¹ := le_of_lt (inv_pos_of_pos hεpos'')
        have hprod : 0 ≤ (κ - z * Real.sqrt q) * (Real.sqrt ε)⁻¹ := mul_nonneg hx hinv
        simp [max_eq_left, hprod]
      have hmaxR : max (κ - z * Real.sqrt q) 0 = κ - z * Real.sqrt q := by
        simp [max_eq_left, hx]
      have hsqrt_inv_sq : ((Real.sqrt ε)⁻¹) ^ 2 = ε⁻¹ := by
        have hsq : (Real.sqrt ε) ^ 2 = ε := by
          simpa using (Real.sq_sqrt (le_of_lt hεpos'))
        calc
          ((Real.sqrt ε)⁻¹) ^ 2 = ((Real.sqrt ε) ^ 2)⁻¹ := by
            simpa using (inv_pow (Real.sqrt ε) 2)
          _ = ε⁻¹ := by
            simpa [hsq]
      have hscaled :
          max ((κ - z * Real.sqrt q) * (Real.sqrt ε)⁻¹) 0 ^ 2 =
            ε⁻¹ * max (κ - z * Real.sqrt q) 0 ^ 2 := by
        calc
          max ((κ - z * Real.sqrt q) * (Real.sqrt ε)⁻¹) 0 ^ 2 =
              ((κ - z * Real.sqrt q) * (Real.sqrt ε)⁻¹) ^ 2 := by
            simpa [hmaxL]
          _ = (κ - z * Real.sqrt q) ^ 2 * ((Real.sqrt ε)⁻¹) ^ 2 := by
            simpa using (mul_pow (κ - z * Real.sqrt q) ((Real.sqrt ε)⁻¹) 2)
          _ = (κ - z * Real.sqrt q) ^ 2 * ε⁻¹ := by
            simp [hsqrt_inv_sq]
          _ = ε⁻¹ * (κ - z * Real.sqrt q) ^ 2 := by
            simpa [mul_comm, mul_left_comm, mul_assoc]
          _ = ε⁻¹ * max (κ - z * Real.sqrt q) 0 ^ 2 := by
            simpa [hmaxR]
      simpa [hUn, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
    ·
      have h' : κ - Real.sqrt q * z ≤ 0 := le_of_not_ge h
      have hmax1 : max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 = 0 := by
        have hUneg : Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z ≤ 0 := by
          have : (κ - Real.sqrt q * z) / Real.sqrt ε ≤ 0 := by
            exact div_nonpos_of_nonpos_of_nonneg h' (le_of_lt hεpos'')
          simpa [hUn] using this
        simp [max_eq_right, hUneg]
      have hmax2 : max (κ - Real.sqrt q * z) 0 = 0 := by
        simp [max_eq_right, h']
      simp [hmax1, hmax2, div_eq_mul_inv]
  unfold An Expect Theorem1.Expect
  have hEq :
      (fun z : ℝ =>
          (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) =
        fun z : ℝ =>
          (max (κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * z) 0) ^ 2 /
            εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
    funext z
    simpa using hpoint z
  simp [hEq, div_eq_mul_inv, integral_const_mul, mul_assoc, mul_left_comm, mul_comm, hεne]

abbrev RSStarSeq (n : ℕ) : ℝ :=
  RSStar κ (α n) hκ (hα n).1 (hα n).2

lemma tendsto_rn_atTop (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    Tendsto (rn (κ := κ) (hκ := hκ) (α := α) (hα := hα)) atTop atTop := by
  simpa [rn] using (Theorem1.theorem_second_main_seq (κ := κ) hκ (α := α) (hα := hα) hlim).1

lemma tendsto_qn_one (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    Tendsto (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα)) atTop (𝓝 (1 : ℝ)) := by
  simpa [qn] using (Theorem1.theorem_second_main_seq (κ := κ) hκ (α := α) (hα := hα) hlim).2

lemma tendsto_εn_zero (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    Tendsto (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα)) atTop (𝓝 (0 : ℝ)) := by
  have hq :
      Tendsto (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_qn_one (κ := κ) (hκ := hκ) (α := α) (hα := hα) hlim
  have h1 : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hsub := h1.sub hq
  simpa [εn, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub

lemma qn_eq_P_rn (n : ℕ) :
    qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
      P (rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
  simpa [qn, rn] using
    (Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2).2.2.2.1

lemma rn_eq_alpha_mul_B_div_eps_sq (n : ℕ) :
    rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
      (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
        (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ^ 2 := by
  have hspec := Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2
  have hq_lt1 :
      qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n < 1 := by
    simpa [qn] using hspec.2.1
  have hr :
      rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
        R κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) (α n) := by
    simpa [rn, qn] using hspec.2.2.2.2
  calc
    rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
        R κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) (α n) := hr
    _ = (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
          (1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ^ 2 := by
        simpa using (Theorem1.R_eq (κ := κ) (α := α n)
          (q := qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) hq_lt1)
    _ = (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
          (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ^ 2 := by
        simp [εn, sub_eq_add_neg]

set_option maxHeartbeats 1000000 in
lemma RSStarSeq_le_main_bound
    (hlim : Tendsto α atTop (𝓝 (αc κ)))
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C0 : ℝ,
      ∀ᶠ n in atTop,
        RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
          ≤ (α n * (Φ (κ - δ)) / 2) * Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) + C0 := by
  classical
  obtain ⟨Cgap, hgap⟩ := exists_C0_E_sq_sub_uplus_sq_le
  refine ⟨Real.log 2 + (αc κ) * Cδ δ + (αc κ) * Cgap / 2, ?_⟩
  have hqevent :
      ∀ᶠ n in atTop,
        (1 / 2 : ℝ) ≤
          Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
    have hq :=
      tendsto_qn_one (κ := κ) (hκ := hκ) (α := α) (hα := hα) hlim
    have hnhds : Set.Ioi (1 / 4 : ℝ) ∈ 𝓝 (1 : ℝ) := by
      refine IsOpen.mem_nhds isOpen_Ioi ?_
      norm_num
    have hq_gt :
        ∀ᶠ n in atTop,
          (1 / 4 : ℝ) < qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n :=
      hq.eventually hnhds
    refine hq_gt.mono ?_
    intro n hq_gt
    have hspec := Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2
    have hq_nonneg :
        0 ≤ qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
      simpa [qn] using hspec.1
    have hsq : (1 / 2 : ℝ) ^ 2 ≤ qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
      have : (1 / 4 : ℝ) ≤ qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := le_of_lt hq_gt
      nlinarith
    exact (Real.le_sqrt (by norm_num) hq_nonneg).2 hsq
  refine hqevent.mono ?_
  intro n hsqrt
  have hspec := Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2
  have hq_nonneg :
      0 ≤ qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
    simpa [qn] using hspec.1
  have hq_lt1 : qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n < 1 := by
    simpa [qn] using hspec.2.1
  have hεpos :
      0 < εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
    simpa [εn, qn] using sub_pos.2 hq_lt1
  have hεne :
      εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≠ 0 := ne_of_gt hεpos
  have hRS :
      RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
        RSFunctionalSplit κ (α n) (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)
          (rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
    simp [RSStarSeq, RSStar_eq_split, RSFunctionalSplit, qn, rn, Un, U]
  have hspin_term :
      RSFunctionalSplit κ (α n) (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)
          (rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)
        ≤ Real.log 2 +
          (rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n *
            (1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) / 2) +
          (α n) *
            Expect (fun z : ℝ =>
              Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) := by
    have hr_nonneg :
        0 ≤ rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
      simpa [rn] using hspec.2.2.1
    have hqPr :
        qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
          P (rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
      simpa [qn, rn] using hspec.2.2.2.1
    have h := spin_term_bound_RSStar (κ := κ) (α := α n)
      (q := qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)
      (r := rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)
      hr_nonneg hqPr
    simpa [Un, U] using h
  have hspin :
      RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤
        Real.log 2 +
          (rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n *
            (1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) / 2) +
          (α n) *
            Expect (fun z : ℝ =>
              Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) := by
    simpa [hRS] using hspin_term
  have hRS_le :
      RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤
        Real.log 2 +
          (α n) *
            Expect (fun z : ℝ =>
              Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) +
          (rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n *
            (1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) / 2) := by
    linarith [hspin]
  have hR : rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
      (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
        (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ^ 2 :=
    rn_eq_alpha_mul_B_div_eps_sq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
  have hspin_term' :
      rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n *
          (1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) / 2 =
        (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
          (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
    have hεne' :
        εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≠ 0 := ne_of_gt hεpos
    calc
      rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n *
          (1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) / 2 =
        ((α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
          (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ^ 2) *
            (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) / 2 := by
          simp [hR, εn, sub_eq_add_neg]
      _ = (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
          (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
          field_simp [hεne']
  have hRS_le' :
      RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤
        Real.log 2 +
          (α n) *
            Expect (fun z : ℝ =>
              Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) +
          (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
            (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
    simpa [hspin_term'] using hRS_le
  have hconstraint :
      Expect (fun z : ℝ =>
        Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) ≤
        (-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
          (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
          (Φ (κ - δ) / 2) *
            Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
          Cδ δ := by
    let s : Set ℝ := Set.Iic (κ - δ)
    have hconstraint_point :
        ∀ z : ℝ,
          Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ≤
            -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2
              - Set.indicator s (fun _ => (1 : ℝ)) z *
                Real.log (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0)
              := by
      intro z
      by_cases hz : z ≤ κ - δ
      ·
        have hq : (1 / 2 : ℝ) ≤ Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := hsqrt
        have hnum : κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * z ≥ δ / 2 := by
          have hq' : Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ≤ 1 := by
            have hq1 : qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤ 1 := le_of_lt hq_lt1
            exact (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using hq1⟩
          have hκterm_nonneg :
              0 ≤ κ * (1 - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) := by
            have : 0 ≤ 1 - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) :=
              sub_nonneg_of_le hq'
            exact mul_nonneg hκ this
          have hδ_nonneg : 0 ≤ δ := le_of_lt hδ.1
          have hmul' :
              δ / 2 ≤
                Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * δ := by
            have := mul_le_mul_of_nonneg_right hq hδ_nonneg
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
          have hcalc :
              κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * (κ - δ) =
                κ * (1 - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) +
                  Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * δ := by
            ring
          have hpos1 :
              δ / 2 ≤
                κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * (κ - δ) := by
            have :
                (δ / 2 : ℝ) ≤
                  κ * (1 - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) +
                    Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * δ := by
              have :
                  Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * δ ≤
                    κ * (1 - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) +
                      Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * δ := by
                linarith [hκterm_nonneg]
              exact le_trans hmul' this
            simpa [hcalc] using this
          have hsub :
              κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * (κ - δ) ≤
                κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * z := by
            have hmul :
                Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * z ≤
                  Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * (κ - δ) := by
              have hq0 : 0 ≤ Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) :=
                Real.sqrt_nonneg _
              exact mul_le_mul_of_nonneg_left hz hq0
            linarith
          exact le_trans hpos1 hsub
        have hUpos :
            0 < Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z := by
          have hden : 0 < Real.sqrt (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) :=
            Real.sqrt_pos.2 hεpos
          have hδ2_pos : 0 < (δ / 2 : ℝ) := by
            nlinarith [hδ.1]
          have hnum' : 0 < κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * z :=
            lt_of_lt_of_le hδ2_pos hnum
          have : 0 < (κ - Real.sqrt (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) * z) /
              Real.sqrt (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
            exact div_pos hnum' hden
          simpa [Un, U] using this
        have hlog := log_Φbar_le_neg_sq_div_two_sub_log (u := Un (κ := κ) (hκ := hκ) (α := α)
          (hα := hα) n z) hUpos
        have hmax : max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 =
            Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z := by
          simp [max_eq_left, le_of_lt hUpos]
        have hind : Set.indicator s (fun _ => (1 : ℝ)) z = 1 := by
          simp [s, hz]
        simpa [hmax, hind] using hlog
      ·
        have hind : Set.indicator s (fun _ => (1 : ℝ)) z = 0 := by
          simp [s, hz]
        by_cases hu : 0 < Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z
        ·
          have hlog := log_Φbar_le_neg_sq_div_two (u := Un (κ := κ) (hκ := hκ) (α := α)
            (hα := hα) n z) hu
          have hmax : max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 =
              Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z := by
            simp [max_eq_left, le_of_lt hu]
          simpa [hmax, hind] using hlog
        ·
          have hnonpos : Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z ≤ 0 := le_of_not_gt hu
          have hlog_nonpos : Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ≤ 0 := by
            have hΦbar_pos : 0 < Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) := by
              simpa [Φbar, Theorem1.Φbar] using
                DecreasingG.Φbar_pos (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)
            have hΦbar_le_one : Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) ≤ 1 := by
              have htotal : (∫ x : ℝ, φ x) = 1 := by
                have hv : (1 : ℝ≥0) ≠ 0 := by simp
                simpa [φ, Theorem1.φ, DecreasingG.φ, ProbabilityTheory.gaussianPDFReal,
                  div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                  (ProbabilityTheory.integral_gaussianPDFReal_eq_one (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)
              have hφ_nonneg : ∀ x : ℝ, 0 ≤ φ x := by
                intro x; exact (UniformBoundOfG.φ_pos x).le
              have hφ_int : Integrable (fun x : ℝ => φ x) := by
                have hφ_eq : φ = ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) := by
                  funext x
                  simp [φ, Theorem1.φ, DecreasingG.φ, ProbabilityTheory.gaussianPDFReal,
                    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
                simpa [hφ_eq] using
                  (ProbabilityTheory.integrable_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
              have hmono :
                  ∫ x in Set.Ici (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z), φ x ≤ ∫ x : ℝ, φ x := by
                refine MeasureTheory.setIntegral_le_integral (μ := (volume : Measure ℝ)) (f := φ)
                  (s := Set.Ici (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ?_ ?_
                · simpa using hφ_int
                · exact ae_of_all _ (fun x => hφ_nonneg x)
              have hΦbar_le :
                  Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) ≤ 1 := by
                simpa [Φbar, Theorem1.Φbar, DecreasingG.Φbar, htotal] using hmono
              exact hΦbar_le
            exact (Real.log_le_iff_le_exp hΦbar_pos).2 (by simpa using hΦbar_le_one)
          have hmax : max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 = 0 := by
            simp [max_eq_right, hnonpos]
          simpa [hmax, hind] using hlog_nonpos
    have hInt :
        Integrable
          (fun z : ℝ =>
            Real.log
              (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) γ :=
      integrable_log_Φbar_Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n

    let q : ℝ := qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
    let ε : ℝ := 1 - q
    let K : ℝ := Cδ δ + Real.log ε / 2

    have hlog_term_bound :
        ∀ z : ℝ,
          -Set.indicator s (fun _ => (1 : ℝ)) z *
              Real.log
                (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ≤
            Set.indicator s (fun _ => (1 : ℝ)) z * K := by
      intro z
      by_cases hz : z ≤ κ - δ
      ·
        have hind : Set.indicator s (fun _ => (1 : ℝ)) z = 1 := by
          simp [s, hz]
        have hsqrt_half : (1 / 2 : ℝ) ≤ Real.sqrt q := by
          simpa [q] using hsqrt
        have hq_nonneg_q : 0 ≤ q := by
          simpa [q] using hq_nonneg
        have hq_lt1_q : q < 1 := by
          simpa [q] using hq_lt1
        have hεpos_ε : 0 < ε := by
          simpa [ε] using sub_pos.2 hq_lt1_q
        have hsqrt_le_one : Real.sqrt q ≤ 1 := by
          have hq_le : q ≤ 1 := le_of_lt hq_lt1_q
          exact (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using hq_le⟩
        have hδ_nonneg : 0 ≤ δ := le_of_lt hδ.1
        have hκterm_nonneg : 0 ≤ κ * (1 - Real.sqrt q) := by
          have : 0 ≤ 1 - Real.sqrt q := sub_nonneg_of_le hsqrt_le_one
          exact mul_nonneg hκ this
        have hδterm : δ / 2 ≤ Real.sqrt q * δ := by
          have := mul_le_mul_of_nonneg_right hsqrt_half hδ_nonneg
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
        have hcalc :
            κ - Real.sqrt q * (κ - δ) =
              κ * (1 - Real.sqrt q) + Real.sqrt q * δ := by
          ring
        have hnum1 : δ / 2 ≤ κ - Real.sqrt q * (κ - δ) := by
          have hδterm' :
              δ / 2 ≤ κ * (1 - Real.sqrt q) + Real.sqrt q * δ := by
            have :
                Real.sqrt q * δ ≤
                  κ * (1 - Real.sqrt q) + Real.sqrt q * δ := by
              linarith [hκterm_nonneg]
            exact le_trans hδterm this
          simpa [hcalc] using hδterm'
        have hsub : κ - Real.sqrt q * (κ - δ) ≤ κ - Real.sqrt q * z := by
          have hmul : Real.sqrt q * z ≤ Real.sqrt q * (κ - δ) := by
            have hq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
            exact mul_le_mul_of_nonneg_left hz hq0
          linarith
        have hnum : δ / 2 ≤ κ - Real.sqrt q * z := le_trans hnum1 hsub
        have hsqrtε_pos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hεpos_ε
        have hUn_eq :
            Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z =
              (κ - Real.sqrt q * z) / Real.sqrt ε := by
          simp [Un, U, Theorem1.U, q, ε]
        have hUn_ge :
            (δ / 2) / Real.sqrt ε ≤
              Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z := by
          have :
              (δ / 2) / Real.sqrt ε ≤
                (κ - Real.sqrt q * z) / Real.sqrt ε :=
            div_le_div_of_nonneg_right hnum (le_of_lt hsqrtε_pos)
          simpa [hUn_eq] using this
        have hpos_const : 0 < (δ / 2) / Real.sqrt ε := by
          have hδ2_pos : 0 < (δ / 2 : ℝ) := by
            nlinarith [hδ.1]
          exact div_pos hδ2_pos hsqrtε_pos
        have hUn_pos :
            0 < Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z :=
          lt_of_lt_of_le hpos_const hUn_ge
        have hmax :
            max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 =
              Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z := by
          simp [max_eq_left, le_of_lt hUn_pos]
        have hconst_le :
            (δ / 2) / Real.sqrt ε ≤
              max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 := by
          simpa [hmax] using hUn_ge
        have hlog_le :
            Real.log ((δ / 2) / Real.sqrt ε) ≤
              Real.log
                (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) :=
          Real.log_le_log hpos_const hconst_le
        have hδ2_ne : (δ / 2 : ℝ) ≠ 0 := by
          exact div_ne_zero (ne_of_gt hδ.1) (by norm_num)
        have hsqrt_ne : (Real.sqrt ε) ≠ 0 := ne_of_gt hsqrtε_pos
        have hlog_div :
            Real.log ((δ / 2) / Real.sqrt ε) =
              Real.log (δ / 2) - Real.log (Real.sqrt ε) := by
          exact Real.log_div hδ2_ne hsqrt_ne
        have hlog_sqrt : Real.log (Real.sqrt ε) = Real.log ε / 2 := by
          exact Real.log_sqrt (le_of_lt hεpos_ε)
        have hK : -Real.log ((δ / 2) / Real.sqrt ε) = K := by
          dsimp [K]
          have h1 :
              -Real.log ((δ / 2) / Real.sqrt ε) =
                -Real.log (δ / 2) + Real.log (Real.sqrt ε) := by
            linarith [hlog_div]
          calc
            -Real.log ((δ / 2) / Real.sqrt ε) =
                -Real.log (δ / 2) + Real.log (Real.sqrt ε) := h1
            _ = -Real.log (δ / 2) + Real.log ε / 2 := by
              simpa [hlog_sqrt]
            _ = Cδ δ + Real.log ε / 2 := by
              simp [Cδ]
        have hneg_log :
            -Real.log
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ≤
                K := by
          have :
              -Real.log
                    (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ≤
                  -Real.log ((δ / 2) / Real.sqrt ε) := by
            linarith [hlog_le]
          simpa [hK] using this
        simpa [hind] using hneg_log
      ·
        have hind : Set.indicator s (fun _ => (1 : ℝ)) z = 0 := by
          simp [s, hz]
        simp [hind]

    have hpoint :
        ∀ z : ℝ,
          Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ≤
            -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2 +
              Set.indicator s (fun _ => (1 : ℝ)) z * K := by
      intro z
      have h1 := hconstraint_point z
      have h2 := hlog_term_bound z
      have h3 :=
        add_le_add_left h2
          (-(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2)
      have h4 :
          -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2 -
              Set.indicator s (fun _ => (1 : ℝ)) z *
                Real.log
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ≤
            -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2 +
              Set.indicator s (fun _ => (1 : ℝ)) z * K := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, neg_mul] using h3
      exact le_trans h1 h4

    have hmem : MeasureTheory.MemLp (fun z : ℝ => z) (2 : ℝ≥0) γ := by
      simpa [γ, Theorem1.γ] using
        (ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0)))
    have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
      simpa using (MeasureTheory.MemLp.integrable_sq hmem)
    let a : ℝ := κ / Real.sqrt ε
    let b : ℝ := Real.sqrt q / Real.sqrt ε

    have hmax_sq_int :
        Integrable
          (fun z : ℝ =>
            (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) γ := by
      have hbound : ∀ᵐ z ∂γ,
          ‖(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2‖ ≤
              (2 : ℝ) * (a ^ 2) + (2 : ℝ) * (b ^ 2) * (z ^ 2) := by
        refine ae_of_all _ (fun z => ?_)
        have hUn :
            Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z = a - b * z := by
          have hUn1 :
              Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z =
                (κ - Real.sqrt q * z) / Real.sqrt ε := by
            simp [Un, U, Theorem1.U, q, ε]
          have hab :
              a - b * z = (κ - Real.sqrt q * z) / Real.sqrt ε := by
            dsimp [a, b]
            calc
              κ / Real.sqrt ε - Real.sqrt q / Real.sqrt ε * z =
                  κ / Real.sqrt ε - (Real.sqrt q * z) / Real.sqrt ε := by
                    simp [div_mul_eq_mul_div]
              _ = (κ - Real.sqrt q * z) / Real.sqrt ε := by
                    simpa using (sub_div κ (Real.sqrt q * z) (Real.sqrt ε)).symm
          calc
            Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z =
                (κ - Real.sqrt q * z) / Real.sqrt ε := hUn1
            _ = a - b * z := by
              simpa using hab.symm
        have hmax :
            max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 ≤
              |Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z| := by
          refine max_le (le_abs_self _) ?_
          simpa using abs_nonneg
            (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)
        have habs' : |a - b * z| ≤ |a| + |b| * |z| := by
          simpa [abs_mul] using (abs_sub a (b * z))
        have habs :
            |Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z| ≤
              |a| + |b| * |z| := by
          simpa [hUn] using habs'
        have hle' :
            max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 ≤
              |a| + |b| * |z| := le_trans hmax habs
        have hnonneg :
            0 ≤ max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0 :=
          le_max_right _ _
        have hnonneg' : 0 ≤ |a| + |b| * |z| := by
          positivity
        have hle :
            (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 ≤
              (|a| + |b| * |z|) ^ 2 := by
          simpa [pow_two] using mul_le_mul hle' hle' hnonneg hnonneg'
        have hsq :
            (|a| + |b| * |z|) ^ 2 ≤
              (2 : ℝ) * (a ^ 2) + (2 : ℝ) * (b ^ 2) * (z ^ 2) := by
          have hab :
              2 * |a| * (|b| * |z|) ≤ |a| ^ 2 + (|b| * |z|) ^ 2 :=
            two_mul_le_add_sq |a| (|b| * |z|)
          calc
            (|a| + |b| * |z|) ^ 2 =
                |a| ^ 2 + (|b| * |z|) ^ 2 + 2 * |a| * (|b| * |z|) := by
              ring
            _ ≤ |a| ^ 2 + (|b| * |z|) ^ 2 + (|a| ^ 2 + (|b| * |z|) ^ 2) := by
              have := add_le_add_left hab (|a| ^ 2 + (|b| * |z|) ^ 2)
              simpa [add_assoc, add_left_comm, add_comm] using this
            _ = (2 : ℝ) * |a| ^ 2 + (2 : ℝ) * (|b| * |z|) ^ 2 := by
              ring
            _ = (2 : ℝ) * (a ^ 2) + (2 : ℝ) * (b ^ 2) * (z ^ 2) := by
              simp [mul_pow, sq_abs, mul_assoc, mul_left_comm, mul_comm]
        have hle_total :
            (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 ≤
              (2 : ℝ) * (a ^ 2) + (2 : ℝ) * (b ^ 2) * (z ^ 2) :=
          le_trans hle hsq
        have hnonneg_sq :
            0 ≤ (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 := by
          exact sq_nonneg (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0)
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg_sq] using hle_total

      have hconst : Integrable (fun _z : ℝ => (2 : ℝ) * (a ^ 2)) γ :=
        integrable_const _
      have h_rhs_int :
          Integrable
            (fun z : ℝ =>
              (2 : ℝ) * (a ^ 2) + (2 : ℝ) * (b ^ 2) * (z ^ 2)) γ := by
        have h2 : Integrable (fun z : ℝ => (2 : ℝ) * (b ^ 2) * (z ^ 2)) γ :=
          (hsq_int.const_mul ((2 : ℝ) * (b ^ 2)))
        exact hconst.add h2
      exact h_rhs_int.mono'
        (by
          have hUn_meas :
              Measurable
                (fun z : ℝ =>
                  Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) := by
            dsimp [Un, U, Theorem1.U]
            fun_prop
          have hmax_meas :
              Measurable
                (fun z : ℝ =>
                  max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) := by
            exact hUn_meas.max measurable_const
          have hsq_meas :
              Measurable
                (fun z : ℝ =>
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) := by
            exact hmax_meas.pow_const 2
          exact hsq_meas.aestronglyMeasurable)
        hbound

    have hmax_neg_int :
        Integrable
          (fun z : ℝ =>
            -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2) γ := by
      have := hmax_sq_int.const_mul (- (1 / 2 : ℝ))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

    have hind_int :
        Integrable
          (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) γ := by
      have hconst : Integrable (fun _z : ℝ => (|K| : ℝ)) γ := integrable_const _
      have hmeas :
          AEStronglyMeasurable
            (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) γ := by
        have hs : MeasurableSet s := by
          simpa [s] using (measurableSet_Iic (a := κ - δ))
        have hind_meas :
            Measurable (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z) := by
          simpa using (Measurable.indicator (hf := measurable_const) hs)
        have hmul_meas :
            Measurable (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) := by
          exact hind_meas.mul_const K
        exact hmul_meas.aestronglyMeasurable
      have hbound : ∀ᵐ z ∂γ, ‖Set.indicator s (fun _ => (1 : ℝ)) z * K‖ ≤ |K| := by
        refine ae_of_all _ (fun z => ?_)
        by_cases hz : z ≤ κ - δ
        ·
          have hind : Set.indicator s (fun _ => (1 : ℝ)) z = 1 := by
            simp [s, hz]
          simp [hind, Real.norm_eq_abs]
        ·
          have hind : Set.indicator s (fun _ => (1 : ℝ)) z = 0 := by
            simp [s, hz]
          have : 0 ≤ |K| := abs_nonneg K
          simp [hind, Real.norm_eq_abs, this]
      exact Integrable.mono' hconst hmeas hbound

    have hInt_rhs :
        Integrable
          (fun z : ℝ =>
            -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2 +
              Set.indicator s (fun _ => (1 : ℝ)) z * K) γ :=
      hmax_neg_int.add hind_int

    have hInt_le :
        Expect
            (fun z : ℝ =>
              Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) ≤
          Expect
            (fun z : ℝ =>
              -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2 +
                Set.indicator s (fun _ => (1 : ℝ)) z * K) := by
      unfold Expect Theorem1.Expect
      refine MeasureTheory.integral_mono_ae hInt hInt_rhs ?_
      exact ae_of_all _ (fun z => hpoint z)

    have hmax_expect :
        Expect
            (fun z : ℝ =>
              -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2) =
          (-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
            (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
      have h := Expect_max_Un_sq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
      have hεne' :
          εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≠ 0 := ne_of_gt hεpos
      have hfun :
          (fun z : ℝ =>
                -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2) =
              fun z : ℝ =>
                (- (1 / 2 : ℝ)) *
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 := by
        funext z
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      calc
        Expect
              (fun z : ℝ =>
                -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2) =
            (- (1 / 2 : ℝ)) *
              Expect
                (fun z : ℝ =>
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) := by
          unfold Expect Theorem1.Expect
          simpa [hfun] using
            (MeasureTheory.integral_const_mul (μ := γ) (- (1 / 2 : ℝ))
              (fun z : ℝ =>
                (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2))
        _ = (- (1 / 2 : ℝ)) *
              (An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n /
                εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
          simp [h]
        _ =
            (-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
              (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
          field_simp [hεne']

    have hind :
        Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z) = Φ (κ - δ) := by
      have hs : MeasurableSet s := by
        simp [s]
      have hE :
          Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z) =
            γ.real s := by
        unfold Expect Theorem1.Expect
        simpa using
          (MeasureTheory.integral_indicator_const (μ := γ) (e := (1 : ℝ)) hs)
      have hv : (1 : ℝ≥0) ≠ 0 := by
        simp
      have hφ_eq :
          (fun x : ℝ => ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x) = φ := by
        funext x
        simp [φ, Theorem1.φ, DecreasingG.φ, ProbabilityTheory.gaussianPDFReal,
          div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      have hγ_Ioi : γ.real (Set.Ioi (κ - δ)) = Φbar (κ - δ) := by
        have hμ :
            γ (Set.Ioi (κ - δ)) =
              ENNReal.ofReal
                (∫ x in Set.Ioi (κ - δ),
                  ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x) := by
          simpa [γ] using
            (ProbabilityTheory.gaussianReal_apply_eq_integral (μ := (0 : ℝ))
              (v := (1 : ℝ≥0)) hv (Set.Ioi (κ - δ)))
        have hnonneg :
            0 ≤
              ∫ x in Set.Ioi (κ - δ),
                ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x := by
          refine MeasureTheory.integral_nonneg ?_
          intro x
          exact
            ProbabilityTheory.gaussianPDFReal_nonneg (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) x
        have hreal :
            γ.real (Set.Ioi (κ - δ)) =
              ∫ x in Set.Ioi (κ - δ),
                ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x := by
          simp [Measure.real, hμ, hnonneg]
        have hΦbar :
            Φbar (κ - δ) =
              ∫ x in Set.Ioi (κ - δ),
                ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x := by
          simpa [Φbar, Theorem1.Φbar, DecreasingG.Φbar,
            MeasureTheory.integral_Ici_eq_integral_Ioi, hφ_eq]
        simpa [hΦbar] using hreal
      have hIoi_meas : MeasurableSet (Set.Ioi (κ - δ)) := by
        simp
      have hcompl :
          γ.real (Set.Ioi (κ - δ))ᶜ =
            γ.real Set.univ - γ.real (Set.Ioi (κ - δ)) :=
        MeasureTheory.measureReal_compl (μ := γ) hIoi_meas
      have hIic :
          γ.real (Set.Iic (κ - δ)) = 1 - γ.real (Set.Ioi (κ - δ)) := by
        simpa [Set.compl_Ioi, MeasureTheory.probReal_univ, sub_eq_add_neg] using hcompl
      have hγ_Iic : γ.real s = Φ (κ - δ) := by
        calc
          γ.real s = γ.real (Set.Iic (κ - δ)) := by
            simp [s]
          _ = 1 - γ.real (Set.Ioi (κ - δ)) := hIic
          _ = Φ (κ - δ) := by
            simp [Φ, hγ_Ioi]
      simpa [hE] using hγ_Iic

    have hind_mul :
        Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) =
          Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z) * K := by
      unfold Expect Theorem1.Expect
      simpa using
        (MeasureTheory.integral_mul_const (μ := γ) K
          (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z))

    have hΦ_le : Φ (κ - δ) ≤ 1 := by
      have hΦbar_pos : 0 < Φbar (κ - δ) := by
        simpa [Φbar, Theorem1.Φbar] using DecreasingG.Φbar_pos (κ - δ)
      have : 1 - Φbar (κ - δ) ≤ 1 := by
        linarith [hΦbar_pos.le]
      simpa [Φ] using this

    have hCδ_nonneg : 0 ≤ Cδ δ := by
      unfold Cδ
      have hδ2_pos : 0 < (δ / 2 : ℝ) := by
        nlinarith [hδ.1]
      have hδ2_le_one : (δ / 2 : ℝ) ≤ 1 := by
        have : δ ≤ 1 := le_of_lt hδ.2
        nlinarith
      have hlog_le : Real.log (δ / 2) ≤ 0 := by
        have := Real.log_le_log hδ2_pos hδ2_le_one
        simpa using this
      exact (neg_nonneg.2 hlog_le)

    have hindK_le :
        Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) ≤
          Cδ δ + (Φ (κ - δ) / 2) * Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
      have hE :
          Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) =
            Φ (κ - δ) * K := by
        calc
          Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) =
              Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z) * K :=
            hind_mul
          _ = Φ (κ - δ) * K := by
            simpa [hind]
      have hmul : Cδ δ * Φ (κ - δ) ≤ Cδ δ := by
        have := mul_le_mul_of_nonneg_left hΦ_le hCδ_nonneg
        simpa using this
      have hle : Φ (κ - δ) * K ≤ Cδ δ + (Φ (κ - δ) / 2) * Real.log ε := by
        calc
          Φ (κ - δ) * K = Cδ δ * Φ (κ - δ) + (Φ (κ - δ) / 2) * Real.log ε := by
            simp [K, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
          _ ≤ Cδ δ + (Φ (κ - δ) / 2) * Real.log ε := by
            exact add_le_add_left hmul _
      have :
          Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) ≤
            Cδ δ + (Φ (κ - δ) / 2) * Real.log ε := by
        simpa [hE] using hle
      simpa [ε] using this

    have hsum :
        Expect
            (fun z : ℝ =>
              -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2 +
                Set.indicator s (fun _ => (1 : ℝ)) z * K) =
          Expect
              (fun z : ℝ =>
                -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2) +
            Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) := by
      unfold Expect Theorem1.Expect
      simpa using
        (MeasureTheory.integral_add (μ := γ)
          (f := fun z : ℝ =>
            -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2)
          (g := fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K)
          hmax_neg_int hind_int)

    have hconst_le :
        Expect
            (fun z : ℝ =>
              -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2 +
                Set.indicator s (fun _ => (1 : ℝ)) z * K) ≤
          (-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
              (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
            (Φ (κ - δ) / 2) *
                Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
              Cδ δ := by
      calc
        Expect
              (fun z : ℝ =>
                -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2 +
                  Set.indicator s (fun _ => (1 : ℝ)) z * K) =
            Expect
                (fun z : ℝ =>
                  -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2) +
              Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) :=
          hsum
        _ ≤
            (-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
              (Cδ δ +
                (Φ (κ - δ) / 2) *
                    Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) := by
          have h1 :
              Expect
                    (fun z : ℝ =>
                      -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2) =
                  (-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                    (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) :=
            hmax_expect
          have h2 :
              Expect (fun z : ℝ => Set.indicator s (fun _ => (1 : ℝ)) z * K) ≤
                Cδ δ +
                  (Φ (κ - δ) / 2) *
                    Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) :=
            hindK_le
          simpa [h1] using
            (add_le_add_right h2
              (Expect
                (fun z : ℝ =>
                  -(max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 / 2)))
        _ =
            (-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
              (Φ (κ - δ) / 2) *
                  Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
                Cδ δ := by
          ring

    exact le_trans hInt_le hconst_le

  have hRS_le :
      RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤
        Real.log 2 +
          (α n) *
            ((-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
              (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
              (Φ (κ - δ) / 2) *
                Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
              Cδ δ) +
          (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
            (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
    refine le_trans hRS_le' ?_
    have hα_nonneg : 0 ≤ α n := le_of_lt (hα n).1
    have hconstraint_mul :
        (α n) *
            Expect (fun z : ℝ =>
              Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) ≤
          (α n) *
            ((-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
              (Φ (κ - δ) / 2) *
                  Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
                Cδ δ) := by
      exact mul_le_mul_of_nonneg_left hconstraint hα_nonneg
    have hsum :
        (α n) *
              Expect (fun z : ℝ =>
                Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) +
            (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ≤
          (α n) *
                ((-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                    (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
                  (Φ (κ - δ) / 2) *
                      Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
                    Cδ δ) +
              (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                  (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
      exact add_le_add hconstraint_mul le_rfl
    have hsum' :
        Real.log 2 +
              ((α n) *
                    Expect (fun z : ℝ =>
                      Real.log (Φbar (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z))) +
                  (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                      (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) ≤
          Real.log 2 +
              ((α n) *
                    ((-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                        (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
                      (Φ (κ - δ) / 2) *
                          Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
                        Cδ δ) +
                  (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                      (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) := by
      exact add_le_add_right hsum (Real.log 2)
    simpa [add_assoc] using hsum'
  have hgap_exp :
      (α n) *
        (B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) -
          An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
          (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ≤
        (αc κ) * Cgap / 2 := by
    have hα_le : α n ≤ αc κ := (hα n).2.le
    have hgap_point :
        (B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) -
          An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
            (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ≤ Cgap := by
      have hgap_int :
          (B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) -
            An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
              (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) =
            Expect (fun z : ℝ =>
              (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
                (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) := by
        have hB :
            B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) =
              εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n *
                Expect (fun z : ℝ =>
                  (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2) := by
          simp [B, Theorem1.B, Un, U, Theorem1.U, εn, qn, Expect, Theorem1.Expect, mul_assoc, mul_left_comm, mul_comm]
        have hA :
            An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
              εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n *
                Expect (fun z : ℝ =>
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) := by
          have h := Expect_max_Un_sq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
          field_simp [hεne] at h
          simpa [εn, mul_assoc, mul_left_comm, mul_comm] using h.symm
        let f1 : ℝ → ℝ := fun z : ℝ =>
          (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2
        let f2 : ℝ → ℝ := fun z : ℝ =>
          (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2
        have hf2_int : Integrable f2 γ := by
          have hspec := Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2
          have hq_nonneg :
              0 ≤ qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
            simpa [qn] using hspec.1
          have hq_lt1 :
              qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n < 1 := by
            simpa [qn] using hspec.2.1
          have hεpos :
              0 < εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
            simpa [εn] using sub_pos.2 hq_lt1
          have hε_nonneg :
              0 ≤ εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n :=
            le_of_lt hεpos
          have hmem : MeasureTheory.MemLp (fun z : ℝ => z) (2 : ℝ≥0) γ := by
            simpa [γ, Theorem1.γ] using
              (ProbabilityTheory.memLp_id_gaussianReal
                (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0)))
          have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
            simpa using (MeasureTheory.MemLp.integrable_sq hmem)
          have hnum_int :
              Integrable
                (fun z : ℝ =>
                  (2 * κ ^ 2 : ℝ) +
                    2 * qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * (z ^ 2)) γ := by
            have hconst : Integrable (fun _z : ℝ => (2 * κ ^ 2 : ℝ)) γ := integrable_const _
            have h2 :
                Integrable
                  (fun z : ℝ =>
                    2 * qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * (z ^ 2)) γ :=
              hsq_int.const_mul (2 * qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)
            exact hconst.add h2
          have hdom_int :
              Integrable
                (fun z : ℝ =>
                  ((2 * κ ^ 2 : ℝ) +
                      2 * qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * (z ^ 2)) /
                    εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) γ := by
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              (hnum_int.mul_const
                ((εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ⁻¹))
          have hmeas : AEStronglyMeasurable f2 γ := by
            have hcontUn :
                Continuous
                  (fun z : ℝ =>
                    Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) := by
              unfold Un
              unfold U
              have hnum :
                  Continuous
                    (fun z : ℝ =>
                      κ -
                        Real.sqrt
                            (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                          z) :=
                continuous_const.sub (continuous_const.mul continuous_id)
              simpa using
                hnum.div_const
                  (Real.sqrt (1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n))
            have hmax :
                Continuous
                  (fun z : ℝ =>
                    max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) :=
              hcontUn.max continuous_const
            have hcont : Continuous f2 := by
              simpa [f2] using hmax.pow 2
            exact hcont.aestronglyMeasurable
          have hbound :
              ∀ᵐ z ∂γ,
                ‖f2 z‖ ≤
                  ((2 * κ ^ 2 : ℝ) +
                      2 * qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * (z ^ 2)) /
                    εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
            refine ae_of_all _ (fun z => ?_)
            have hmax_le :
                f2 z ≤
                  (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) ^ 2 := by
              by_cases hu :
                  0 ≤ Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z
              · simp [f2, max_eq_left, hu]
              ·
                have hu' :
                    Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z ≤ 0 :=
                  le_of_not_ge hu
                have : f2 z = 0 := by
                  simp [f2, max_eq_right, hu']
                simp [this, sq_nonneg]
            have hUn_sq :
                (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) ^ 2 =
                  (κ -
                      Real.sqrt
                          (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                        z) ^ 2 /
                    εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
              have hUn :
                  Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z =
                    (κ -
                        Real.sqrt
                            (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                          z) /
                      Real.sqrt (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
                dsimp [Un, U, Theorem1.U, εn, qn]
              calc
                (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) ^ 2 =
                    ((κ -
                          Real.sqrt
                              (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                            z) /
                        Real.sqrt (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) ^ 2 := by
                  simp [hUn]
                _ =
                    (κ -
                        Real.sqrt
                            (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                          z) ^ 2 /
                      (Real.sqrt (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) ^ 2 := by
                  simp [div_pow]
                _ =
                    (κ -
                        Real.sqrt
                            (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                          z) ^ 2 /
                      εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
                  simp [Real.sq_sqrt hε_nonneg]
            have hnum_le :
                (κ -
                    Real.sqrt
                        (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                      z) ^ 2 ≤
                  (2 * κ ^ 2 : ℝ) +
                    2 * qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * (z ^ 2) := by
              have hnonneg :
                  0 ≤
                      (κ +
                          Real.sqrt
                              (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                            z) ^ 2 :=
                sq_nonneg _
              nlinarith [hnonneg, Real.mul_self_sqrt hq_nonneg]
            have hdiv_le :
                (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) ^ 2 ≤
                  ((2 * κ ^ 2 : ℝ) +
                      2 * qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * (z ^ 2)) /
                    εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
              have := div_le_div_of_nonneg_right hnum_le hε_nonneg
              simpa [hUn_sq] using this
            have hf2_le :
                f2 z ≤
                  ((2 * κ ^ 2 : ℝ) +
                      2 * qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * (z ^ 2)) /
                    εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n :=
              le_trans hmax_le hdiv_le
            have hnonneg_f2 : 0 ≤ f2 z := by
              simp [f2]
            simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg_f2] using hf2_le
          exact Integrable.mono' hdom_int hmeas hbound
        have hf1_int : Integrable f1 γ := by
          have hconst : Integrable (fun _z : ℝ => (Cgap : ℝ)) γ := integrable_const _
          have hdom : Integrable (fun z : ℝ => f2 z + Cgap) γ := hf2_int.add hconst
          have hcontE : Continuous E := by
            simpa [Theorem1.E, UniformBoundOfG.E] using
              (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E)
          have hcontUn :
              Continuous
                (fun z : ℝ =>
                  Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) := by
            unfold Un
            unfold U
            have hnum :
                Continuous
                  (fun z : ℝ =>
                    κ -
                      Real.sqrt
                          (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                        z) :=
              continuous_const.sub (continuous_const.mul continuous_id)
            simpa using
              hnum.div_const
                (Real.sqrt (1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n))
          have hmeas : AEStronglyMeasurable f1 γ := by
            have hcont : Continuous f1 := by
              simpa [f1] using (hcontE.comp hcontUn).pow 2
            exact hcont.aestronglyMeasurable
          have hbound : ∀ᵐ z ∂γ, ‖f1 z‖ ≤ f2 z + Cgap := by
            refine ae_of_all _ (fun z => ?_)
            have h := hgap (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)
            have hf1_le : f1 z ≤ f2 z + Cgap := by
              linarith [h.2]
            have hnonneg : 0 ≤ f1 z := by
              simpa [f1] using
                (sq_nonneg (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)))
            simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hf1_le
          exact Integrable.mono' hdom hmeas hbound
        have hsub :
            Expect (fun z : ℝ => f1 z - f2 z) = Expect f1 - Expect f2 := by
          unfold Expect Theorem1.Expect
          simpa [f1, f2] using (MeasureTheory.integral_sub hf1_int hf2_int)
        calc
          (B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) -
              An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
              (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) =
              (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * Expect f1 -
                  εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * Expect f2) /
                (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
            simp [hB, hA, f1, f2]
          _ = Expect f1 - Expect f2 := by
            have hmul :
                εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * Expect f1 -
                    εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n * Expect f2 =
                  εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n *
                    (Expect f1 - Expect f2) := by
              ring
            simp [hmul, hεne]
          _ = Expect (fun z : ℝ => f1 z - f2 z) := by
            simpa using hsub.symm
          _ =
              Expect (fun z : ℝ =>
                (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) := by
            simp [f1, f2]

      have hInt_le :
          Expect (fun z : ℝ =>
            (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
              (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) ≤ Cgap := by
        have hconst : Integrable (fun _z : ℝ => (Cgap : ℝ)) γ := integrable_const _
        have hmeas :
            AEStronglyMeasurable
              (fun z : ℝ =>
                (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) γ := by
          have hcontE : Continuous E := by
            simpa [Theorem1.E, UniformBoundOfG.E] using
              (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E)
          have hcontUn :
              Continuous
                (fun z : ℝ =>
                  Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) := by
            unfold Un
            unfold U
            have hnum :
                Continuous
                  (fun z : ℝ =>
                    κ -
                      Real.sqrt
                          (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) *
                        z) :=
              continuous_const.sub (continuous_const.mul continuous_id)
            simpa using
              hnum.div_const
                (Real.sqrt (1 - qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n))
          have hcont1 :
              Continuous
                (fun z : ℝ =>
                  (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2) := by
            simpa using (hcontE.comp hcontUn).pow 2
          have hcont2 :
              Continuous
                (fun z : ℝ =>
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) := by
            have hmax :
                Continuous
                  (fun z : ℝ =>
                    max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) :=
              hcontUn.max continuous_const
            simpa using hmax.pow 2
          have hcont :
              Continuous
                (fun z : ℝ =>
                  (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
                    (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) :=
            hcont1.sub hcont2
          exact hcont.aestronglyMeasurable
        have hbound' : ∀ᵐ z ∂γ,
            ‖(E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
              (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2‖ ≤ Cgap := by
          refine ae_of_all _ (fun z => ?_)
          have h := hgap (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)
          have hnonneg : 0 ≤ (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
              (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 := h.1
          have hnorm :
              ‖(E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
                (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2‖ =
                (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 := by
            simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
          simpa [hnorm] using h.2
        have hInt :
            Integrable
              (fun z : ℝ =>
                (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2) γ :=
          Integrable.mono' hconst hmeas hbound'
        unfold Expect Theorem1.Expect
        have hle :
            (∫ z : ℝ,
                (E (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)) ^ 2 -
                  (max (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z) 0) ^ 2 ∂γ) ≤
              (∫ _z : ℝ, (Cgap : ℝ) ∂γ) := by
          refine MeasureTheory.integral_mono_ae hInt hconst ?_
          exact ae_of_all _ (fun z => (hgap (Un (κ := κ) (hκ := hκ) (α := α) (hα := hα) n z)).2)
        simpa [MeasureTheory.integral_const, MeasureTheory.probReal_univ] using hle
      simpa [hgap_int] using hInt_le
    have hCgap_nonneg : 0 ≤ Cgap := by
      have h0 := hgap 0
      exact le_trans h0.1 h0.2
    let Gap : ℝ :=
      B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) -
        An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
    let ε : ℝ := εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
    have hmul : α n / 2 * (Gap / ε) ≤ α n / 2 * Cgap := by
      simpa [Gap, ε] using
        (mul_le_mul_of_nonneg_left hgap_point (div_nonneg ( (hα n).1.le) (by norm_num)))
    have hBound : α n * Gap / (2 * ε) ≤ α n * Cgap / 2 := by
      have hLHS : (α n / 2) * (Gap / ε) = α n * Gap / (2 * ε) := by
        simp [Gap, ε, div_eq_mul_inv]
        ring
      have hRHS : (α n / 2) * Cgap = α n * Cgap / 2 := by
        simp [div_eq_mul_inv]
        ring
      simpa [hLHS, hRHS] using hmul
    have hαCgap : α n * Cgap ≤ αc κ * Cgap := by
      exact mul_le_mul_of_nonneg_right hα_le hCgap_nonneg
    have hαCgap_div : α n * Cgap / 2 ≤ αc κ * Cgap / 2 := by
      exact div_le_div_of_nonneg_right hαCgap (by norm_num)
    have : α n * Gap / (2 * ε) ≤ αc κ * Cgap / 2 := le_trans hBound hαCgap_div
    simpa [Gap, ε] using this
  have hα_le : α n ≤ αc κ := (hα n).2.le
  have hCδ_nonneg : 0 ≤ Cδ δ := by
    unfold Cδ
    have hδ2_pos : 0 < (δ / 2 : ℝ) := by
      nlinarith [hδ.1]
    have hδ2_le_one : (δ / 2 : ℝ) ≤ 1 := by
      have : δ ≤ 1 := le_of_lt hδ.2
      nlinarith
    have hlog_le : Real.log (δ / 2) ≤ 0 := by
      have := Real.log_le_log hδ2_pos hδ2_le_one
      simpa using this
    exact (neg_nonneg.2 hlog_le)
  have hαCδ : (α n) * Cδ δ ≤ (αc κ) * Cδ δ := by
    exact mul_le_mul_of_nonneg_right hα_le hCδ_nonneg
  have hRS_le_exp :
      RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤
        Real.log 2 +
          (α n) *
            ((Φ (κ - δ) / 2) *
              Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) +
          (α n) * Cδ δ +
          (α n) *
            (B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) -
              An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
              (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
    have hEq :
        Real.log 2 +
            (α n) *
              ((-An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                  (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
                (Φ (κ - δ) / 2) *
                  Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
                Cδ δ) +
            (α n) *
              B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) =
          Real.log 2 +
              (α n) *
                ((Φ (κ - δ) / 2) *
                  Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) +
              (α n) * Cδ δ +
              (α n) *
                (B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) -
                  An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                  (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
      simp [div_eq_mul_inv]
      ring
    simpa [hEq] using hRS_le
  have hlog_term :
      (α n) * ((Φ (κ - δ) / 2) *
        Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n)) =
      (α n * Φ (κ - δ) / 2) *
        Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
    simp [div_eq_mul_inv]
    ring
  have hRS_tmp :
      RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤
        Real.log 2 +
          (α n * Φ (κ - δ) / 2) *
            Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
          (αc κ) * Cδ δ + (αc κ) * Cgap / 2 := by
    refine le_trans hRS_le_exp ?_
    have hrest :
        (α n) * Cδ δ +
            (α n) *
              (B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) -
                An (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
                (2 * εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ≤
          (αc κ) * Cδ δ + (αc κ) * Cgap / 2 := by
      exact add_le_add hαCδ hgap_exp
    simpa [add_assoc, hlog_term] using hrest
  have hRS_le'' :
      RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤
        (α n * Φ (κ - δ) / 2) *
          Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
          (Real.log 2 + (αc κ) * Cδ δ + (αc κ) * Cgap / 2) := by
    have hEq :
        Real.log 2 +
            (α n * Φ (κ - δ) / 2) *
              Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
            (αc κ) * Cδ δ + (αc κ) * Cgap / 2 =
          (α n * Φ (κ - δ) / 2) *
              Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) +
            (Real.log 2 + (αc κ) * Cδ δ + (αc κ) * Cgap / 2) := by
      ac_rfl
    simpa [hEq] using hRS_tmp
  simpa using hRS_le''

theorem theorem_three_seq (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    Tendsto (RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα)) atTop atBot := by
  classical
  have hδ : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  obtain ⟨C0, hRS⟩ :=
    RSStarSeq_le_main_bound (κ := κ) (hκ := hκ) (α := α) (hα := hα) hlim (δ := (1 / 2 : ℝ)) hδ
  have hαpos : 0 < αc κ := Theorem1.αc_pos κ
  set Φ0 : ℝ := Φ (κ - (1 / 2 : ℝ))
  have hΦpos : 0 < Φ0 := by
    simpa [Φ0] using (Φ_pos (κ - (1 / 2 : ℝ)))
  have hαevent : ∀ᶠ n in atTop, αc κ / 2 ≤ α n := by
    have hnhds : Set.Ioi (αc κ / 2) ∈ 𝓝 (αc κ) := by
      refine IsOpen.mem_nhds isOpen_Ioi ?_
      simpa [Set.mem_Ioi] using (half_lt_self hαpos)
    have hIoi : ∀ᶠ n in atTop, α n ∈ Set.Ioi (αc κ / 2) := hlim.eventually hnhds
    refine hIoi.mono ?_
    intro n hn
    exact le_of_lt hn
  have hεpos : ∀ n, 0 < εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := by
    intro n
    have hspec := Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2
    have hq_lt1 : qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n < 1 := by
      simpa [qn] using hspec.2.1
    simpa [εn, qn] using sub_pos.2 hq_lt1
  have hlog_event :
      ∀ b : ℝ, ∀ᶠ n in atTop,
        Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ≤ b := by
    intro b
    have hε := tendsto_εn_zero (κ := κ) (hκ := hκ) (α := α) (hα := hα) hlim
    have hnhds : Set.Iio (Real.exp b) ∈ 𝓝 (0 : ℝ) := by
      refine IsOpen.mem_nhds isOpen_Iio ?_
      have : (0 : ℝ) < Real.exp b := by positivity
      simpa using this
    have hIio :
        ∀ᶠ n in atTop,
          εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ∈ Set.Iio (Real.exp b) :=
      hε.eventually hnhds
    refine hIio.mono ?_
    intro n hn
    have hpos : 0 < εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n := hεpos n
    have hle :
        εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤ Real.exp b := le_of_lt hn
    exact (Real.log_le_iff_le_exp hpos).2 hle
  refine tendsto_atBot.2 ?_
  intro b
  set c : ℝ := (αc κ / 2) * Φ0 / 2
  have hcpos : 0 < c := by
    have h1 : 0 < αc κ / 2 := by nlinarith [hαpos]
    have h2 : 0 < Φ0 / 2 := by nlinarith [hΦpos]
    dsimp [c]
    nlinarith [h1, h2]
  set m : ℝ := min ((b - C0) / c) 0
  have hm_le : m ≤ (b - C0) / c := by
    dsimp [m]; exact min_le_left _ _
  have hm_nonpos : m ≤ 0 := by
    dsimp [m]; exact min_le_right _ _
  have hlogm :
      ∀ᶠ n in atTop,
        Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ≤ m :=
    hlog_event m
  refine (hRS.and (hαevent.and hlogm)).mono ?_
  intro n h
  rcases h with ⟨hRSn, hαn, hlogn⟩
  have hΦ0_nonneg : 0 ≤ Φ0 / 2 := by nlinarith [hΦpos]
  have hcoeff_ge : c ≤ α n * Φ0 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hαn hΦ0_nonneg
    simpa [c, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hmul
  have hcoeff_nonneg : 0 ≤ α n * Φ0 / 2 := by
    have hαn_nonneg : 0 ≤ α n := (hα n).1.le
    nlinarith [hαn_nonneg, hΦ0_nonneg]
  have hmul1 :
      (α n * Φ0 / 2) * Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ≤
        (α n * Φ0 / 2) * m := by
    exact mul_le_mul_of_nonneg_left hlogn hcoeff_nonneg
  have hmul2 : (α n * Φ0 / 2) * m ≤ c * m := by
    exact mul_le_mul_of_nonpos_right hcoeff_ge hm_nonpos
  have hprod :
      (α n * Φ0 / 2) * Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ≤
        c * m := by
    exact le_trans hmul1 hmul2
  have hcm_le : c * m ≤ b - C0 := by
    have hcm_le' := mul_le_mul_of_nonneg_left hm_le (le_of_lt hcpos)
    have hcm_eq : c * ((b - C0) / c) = b - C0 := by
      field_simp [hcpos.ne']
    simpa [hcm_eq] using hcm_le'
  have hRS' :
      RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n ≤ c * m + C0 := by
    linarith [hRSn, hprod]
  linarith [hRS', hcm_le]

end Seq

end
end Theorem3
