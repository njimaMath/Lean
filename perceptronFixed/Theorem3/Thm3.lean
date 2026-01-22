import Mathlib

import perceptronFixed.Theorem1.Theorem
import perceptronFixed.Prop_A_P.Prop_A_P
import perceptronFixed.derivative_of_B.derivative_B

/-!
# Theorem 3 (RS* → -∞ as α ↑ αc)

This file follows the blueprint `perceptronFixed/Theorem3/blueprint.txt`.

Paper target: `main.tex` Theorem `\label{thm: bound for threshold}`.

We work with the canonical solution `(qSol κ α, rSol κ α)` from `Theorem1/Theorem.lean`
for `0 < α < αc κ` and define the replica-symmetric free energy
`RSStar κ α = 𝓕κ(α; qSol, rSol)`.

All nontrivial proofs are left as `sorry`. The goal is a Lean-friendly scaffold.
-/

open scoped BigOperators Topology NNReal Real ENNReal Interval
open MeasureTheory Filter

namespace Theorem3

noncomputable section

/-! ## 0. Aliases (from `Theorem1`) -/

abbrev γ : Measure ℝ := Theorem1.γ
abbrev Expect (f : ℝ → ℝ) : ℝ := Theorem1.Expect f

abbrev Φbar : ℝ → ℝ := Theorem1.Φbar
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

/-! ### Standard normal CDF (defined from the tail) -/

def Φ (u : ℝ) : ℝ := 1 - Φbar u

/-! ## 1. RS functional and RS* -/

/-- Replica-symmetric functional `𝓕κ(α;q,r)` (main.tex (RSfunctional)). -/
def RSFunctional (κ α q r : ℝ) : ℝ :=
  -(r * (1 - q) / 2)
    + Expect (fun z => Real.log (2 * Real.cosh (Real.sqrt r * z)))
    + α * Expect (fun z => Real.log (Φbar ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))))

/-- Same functional, but with `log(2cosh x) = log 2 + log(cosh x)` split out. -/
def RSFunctionalSplit (κ α q r : ℝ) : ℝ :=
  Real.log 2
    - (r * (1 - q) / 2)
    + Expect (fun z => Real.log (Real.cosh (Real.sqrt r * z)))
    + α * Expect (fun z => Real.log (Φbar ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))))

lemma RSFunctional_eq_RSFunctionalSplit (κ α q r : ℝ) :
    RSFunctional κ α q r = RSFunctionalSplit κ α q r := by
  -- Blueprint Step 2.2: expand `log(2cosh)` as `log 2 + log(cosh)`.
  classical
  haveI : IsProbabilityMeasure γ := by infer_instance
  have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
    simpa [γ] using
      (MeasureTheory.MemLp.integrable_sq
        (ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))))
  have hsq_int' : Integrable (fun z : ℝ => (Real.sqrt r * z) ^ 2) γ := by
    have hEq : (fun z : ℝ => (Real.sqrt r * z) ^ 2) = fun z => (Real.sqrt r) ^ 2 * (z ^ 2) := by
      funext z
      ring
    simpa [hEq] using (hsq_int.const_mul ((Real.sqrt r) ^ 2))
  have hbound_int : Integrable (fun z : ℝ => (Real.sqrt r * z) ^ 2 / 2) γ := by
    simpa [div_eq_mul_inv] using (hsq_int'.mul_const (1 / (2 : ℝ)))
  have hlogcosh_int : Integrable (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) γ := by
    refine hbound_int.mono ?_ ?_
    · have : Measurable fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z)) := by
        fun_prop
      exact this.aestronglyMeasurable
    · refine ae_of_all _ (fun z => ?_)
      have hxpos : 0 < Real.cosh (Real.sqrt r * z) := Real.cosh_pos _
      have hlog_nonneg :
          0 ≤ Real.log (Real.cosh (Real.sqrt r * z)) := by
        have := Real.log_le_log (x := (1 : ℝ)) (y := Real.cosh (Real.sqrt r * z))
          (by norm_num) (Real.one_le_cosh _)
        simpa using this
      have hx_le : Real.log (Real.cosh (Real.sqrt r * z)) ≤ (Real.sqrt r * z) ^ 2 / 2 := by
        -- `cosh x ≤ exp(x^2/2)` implies `log(cosh x) ≤ x^2/2`.
        have hcosh : Real.cosh (Real.sqrt r * z) ≤ Real.exp ((Real.sqrt r * z) ^ 2 / 2) := by
          simpa using (Real.cosh_le_exp_half_sq (Real.sqrt r * z))
        exact (Real.log_le_iff_le_exp hxpos).2 hcosh
      -- turn into a norm bound
      have hR_nonneg : 0 ≤ (Real.sqrt r * z) ^ 2 / 2 := by
        have : 0 ≤ (Real.sqrt r * z) ^ 2 := sq_nonneg _
        nlinarith
      -- `log(cosh)` is nonnegative, so its norm is itself.
      have hnormL :
          ‖Real.log (Real.cosh (Real.sqrt r * z))‖ = Real.log (Real.cosh (Real.sqrt r * z)) := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
      have hnormR :
          ‖(Real.sqrt r * z) ^ 2 / 2‖ = (Real.sqrt r * z) ^ 2 / 2 := by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg hR_nonneg
      simpa [hnormL, hnormR] using hx_le

  have hconst_int : Integrable (fun _z : ℝ => (Real.log 2 : ℝ)) γ :=
    integrable_const (Real.log 2)

  have hsplit :
      Expect (fun z => Real.log (2 * Real.cosh (Real.sqrt r * z))) =
        Real.log 2 + Expect (fun z => Real.log (Real.cosh (Real.sqrt r * z))) := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hpoint :
        (fun z : ℝ => Real.log (2 * Real.cosh (Real.sqrt r * z))) =
          fun z : ℝ => Real.log 2 + Real.log (Real.cosh (Real.sqrt r * z)) := by
      funext z
      have hcosh : Real.cosh (Real.sqrt r * z) ≠ 0 := (Real.cosh_pos _).ne'
      simpa [Real.log_mul h2 hcosh]
    -- Rewrite the integral using `integral_add`.
    unfold Expect Theorem1.Expect
    simp [hpoint, MeasureTheory.integral_add hconst_int hlogcosh_int, MeasureTheory.integral_const,
      MeasureTheory.probReal_univ]

  unfold RSFunctional RSFunctionalSplit
  rw [hsplit]
  ring

/-- `RSStar(α,κ) = 𝓕κ(α; qα, rα)` at the canonical fixed point solution. -/
def RSStar (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  RSFunctional κ α (qSol κ α hκ hα0 hα) (rSol κ α hκ hα0 hα)

lemma RSStar_eq_split
    (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) :
    RSStar κ α hκ hα0 hα =
      RSFunctionalSplit κ α (qSol κ α hκ hα0 hα) (rSol κ α hκ hα0 hα) := by
  simp [RSStar, RSFunctional_eq_RSFunctionalSplit]

/-! ## 2. Core analytic inequalities (stated as lemmas) -/

/-! ### Step 2.3: spin term bound -/

lemma log_cosh_le_mul_tanh (x : ℝ) : Real.log (Real.cosh x) ≤ x * Real.tanh x := by
  -- Blueprint Step 2.3 (S1).
  classical
  -- Work with `f x := x*tanh x - log(cosh x)` and show `0 ≤ f x`.
  let f : ℝ → ℝ := fun x => x * Real.tanh x - Real.log (Real.cosh x)

  have hf_cont : Continuous f := by
    have hmul : Continuous fun x : ℝ => x * Real.tanh x := by
      simpa using (continuous_id.mul PropAP.continuous_tanh)
    have hlogcosh : Continuous fun x : ℝ => Real.log (Real.cosh x) := by
      simpa using
        (Real.continuous_cosh.log (fun x => (Real.cosh_pos x).ne'))
    simpa [f] using hmul.sub hlogcosh

  have hf_deriv : ∀ x : ℝ, HasDerivAt f (x * (sech x) ^ 2) x := by
    intro x
    have htanh' : HasDerivAt Real.tanh ((sech x) ^ 2) x := by
      -- `tanh' x = 1 / cosh(x)^2 = sech(x)^2`.
      simpa [sech, Theorem1.sech, div_pow] using (PropAP.hasDerivAt_tanh x)
    have hmul' :
        HasDerivAt (fun x : ℝ => x * Real.tanh x) (Real.tanh x + x * (sech x) ^ 2) x := by
      -- product rule for `x * tanh x`
      simpa [one_mul, add_assoc, add_left_comm, add_comm] using
        (hasDerivAt_id x).mul htanh'
    have hlogcosh' :
        HasDerivAt (fun x : ℝ => Real.log (Real.cosh x)) (Real.tanh x) x := by
      have hcosh_ne : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
      have hlog : HasDerivAt Real.log (Real.cosh x)⁻¹ (Real.cosh x) :=
        Real.hasDerivAt_log hcosh_ne
      have hcosh : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
      -- simplify `(cosh x)⁻¹ * sinh x` to `tanh x`
      simpa [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (hlog.comp x hcosh)
    -- Combine and simplify the derivative.
    have hsub := hmul'.sub hlogcosh'
    -- `(tanh x + x*sech^2 x) - tanh x = x*sech^2 x`
    have hEq : (Real.tanh x + x * (sech x) ^ 2) - Real.tanh x = x * (sech x) ^ 2 := by ring
    simpa [f, hEq] using hsub

  have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    -- `f' x = x * sech(x)^2 ≥ 0` on `(0,∞)`, so `f` is monotone on `[0,∞)`.
    refine
      monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Ici (0 : ℝ)) (f := f)
        (f' := fun x => x * (sech x) ^ 2) (convex_Ici (0 : ℝ)) ?_ ?_ ?_
    · exact hf_cont.continuousOn
    · intro x hx
      -- `hx : x ∈ interior (Ici 0) = Ioi 0`
      exact (hf_deriv x).hasDerivWithinAt
    · intro x hx
      have hx' : 0 < x := by
        simpa [interior_Ici, Set.mem_Ioi] using hx
      have hx0 : 0 ≤ x := le_of_lt hx'
      exact mul_nonneg hx0 (sq_nonneg (sech x))

  have hpos : ∀ {y : ℝ}, 0 ≤ y → Real.log (Real.cosh y) ≤ y * Real.tanh y := by
    intro y hy
    have hy_mem : y ∈ Set.Ici (0 : ℝ) := hy
    have h0_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
    have hfy : f 0 ≤ f y := hmono h0_mem hy_mem hy
    have hf0 : f 0 = 0 := by simp [f]
    have hfy0 : 0 ≤ f y := by simpa [hf0] using hfy
    -- `0 ≤ y*tanh y - log(cosh y)` ↔ `log(cosh y) ≤ y*tanh y`.
    exact (sub_nonneg).1 (by simpa [f] using hfy0)

  by_cases hx : 0 ≤ x
  · exact hpos hx
  ·
    have hx' : 0 ≤ -x := by linarith
    have h := hpos (y := -x) hx'
    -- use evenness/oddness of `cosh`/`tanh`
    simpa [Real.cosh_neg, Real.tanh_neg, mul_assoc, mul_left_comm, mul_comm] using h

lemma gaussian_ibp_tanh
    (r : ℝ) :
    Expect (fun z => z * Real.tanh (Real.sqrt r * z)) =
      Real.sqrt r * Expect (fun z => (sech (Real.sqrt r * z)) ^ 2) := by
  -- Blueprint Step 2.3 (S2): Stein / Gaussian integration by parts.
  classical
  -- Reduce to an integration-by-parts identity for the Gaussian pdf on `ℝ`.
  let a : ℝ := Real.sqrt r
  let pdf : ℝ → ℝ := ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : ℝ≥0)
  have hv : (1 : ℝ≥0) ≠ 0 := by simp

  -- Rewrite `Expect` as a Lebesgue integral against the density.
  have hExpect (f : ℝ → ℝ) :
      Expect f = ∫ x : ℝ, pdf x * f x := by
    -- `∫ f d(gaussianReal 0 1) = ∫ pdf • f dvolume`.
    unfold Expect Theorem1.Expect
    -- `γ` is `gaussianReal 0 1`.
    simp [γ, Theorem1.γ, ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := (0 : ℝ))
      (v := (1 : ℝ≥0)) (f := f) hv, pdf, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

  -- Derivative of the test function `u(x) = tanh(a*x)`.
  have hu : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => Real.tanh (a * x)) (a * (sech (a * x)) ^ 2) x := by
    intro x
    have htanh' : HasDerivAt Real.tanh ((sech (a * x)) ^ 2) (a * x) := by
      simpa [sech, Theorem1.sech, div_pow] using (PropAP.hasDerivAt_tanh (a * x))
    have hcomp := htanh'.comp x (hasDerivAt_const_mul a)
    have hmul : (sech (a * x)) ^ 2 * a = a * (sech (a * x)) ^ 2 := by ring
    -- `HasDerivAt.comp` gives the derivative as `sech^2 * a`; commute the scalar.
    simpa [Function.comp, hmul, mul_assoc] using hcomp

  -- Derivative of the standard normal pdf: `pdf' x = -x * pdf x`.
  have hv' : ∀ x : ℝ, HasDerivAt pdf (-x * pdf x) x := by
    intro x
    -- `pdf x = c * exp (-(x^2)/2)` for `c = (√(2π))⁻¹`.
    have hpdf :
        pdf = fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2) := by
      funext y
      simp [pdf, ProbabilityTheory.gaussianPDFReal, mul_assoc, mul_left_comm, mul_comm]
    -- Differentiate `c * exp (-(x^2)/2)`.
    have hg :
        HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
      have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using (hasDerivAt_pow (n := 2) (x := x))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using (hpow.neg.div_const (2 : ℝ))
    have hexp :
        HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
          (Real.exp (-(x ^ 2) / 2) * (-x)) x := by
      simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
        (Real.hasDerivAt_exp (x := (-(x ^ 2) / 2))).comp x hg
    -- Multiply by the constant.
    have := hexp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
    -- simplify to `-x * pdf x`
    simpa [hpdf, mul_assoc, mul_left_comm, mul_comm, neg_mul, mul_neg, sub_eq_add_neg] using this

  -- Integrability helpers (with respect to Lebesgue measure).
  have hpdf_int : Integrable pdf := by
    simpa [pdf] using ProbabilityTheory.integrable_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))

  have hzpdf_int : Integrable (fun x : ℝ => x * pdf x) := by
    -- Reduce to integrability of `x * exp (-(x^2)/2)`.
    have hbase :
        Integrable (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) := by
      -- `∫ |x| exp(-x^2/2)` is finite.
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (integrable_mul_exp_neg_mul_sq (b := (2 : ℝ)⁻¹) (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹))
    -- `x * pdf x` differs from `x * exp` by a constant factor.
    have hEq :
        (fun x : ℝ => x * pdf x) =
          fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * (x * Real.exp (-(x ^ 2) / 2)) := by
      funext x
      simp [pdf, ProbabilityTheory.gaussianPDFReal, mul_assoc, mul_left_comm, mul_comm]
    simpa [hEq, mul_assoc] using (hbase.const_mul ((Real.sqrt (2 * Real.pi))⁻¹))

  -- Bounds: `‖tanh(a*x)‖ ≤ 1` and `‖a*sech(a*x)^2‖ ≤ |a|`.
  have htanh_bound :
      ∀ x : ℝ, ‖Real.tanh (a * x)‖ ≤ (1 : ℝ) := by
    intro x
    have hsq : (Real.tanh (a * x)) ^ 2 ≤ (1 : ℝ) := by
      -- from `tanh^2 + sech^2 = 1`
      have hId := PropAP.tanh_sq_add_sech_sq (a * x)
      have hsech : 0 ≤ (PropAP.sech (a * x)) ^ 2 := sq_nonneg _
      linarith
    have habs : |Real.tanh (a * x)| ≤ 1 := (sq_le_one_iff_abs_le_one (Real.tanh (a * x))).1 hsq
    simpa [Real.norm_eq_abs] using habs

  have huv_int : Integrable (fun x : ℝ => Real.tanh (a * x) * pdf x) := by
    -- bounded-by-1 times an integrable function
    refine Integrable.bdd_mul (c := (1 : ℝ)) hpdf_int (by
      have : Continuous (fun x : ℝ => Real.tanh (a * x)) := by fun_prop
      exact this.aestronglyMeasurable) ?_
    refine ae_of_all _ (fun x => ?_)
    simpa using htanh_bound x

  have huv'_int :
      Integrable (fun x : ℝ => Real.tanh (a * x) * (-x * pdf x)) := by
    have hg : Integrable (fun x : ℝ => -x * pdf x) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (hzpdf_int.const_mul (-1 : ℝ))
    refine Integrable.bdd_mul (c := (1 : ℝ)) hg (by
      have : Continuous (fun x : ℝ => Real.tanh (a * x)) := by fun_prop
      exact this.aestronglyMeasurable) ?_
    refine ae_of_all _ (fun x => ?_)
    simpa using htanh_bound x

  have hu'v_int :
      Integrable (fun x : ℝ => (a * (sech (a * x)) ^ 2) * pdf x) := by
    -- bounded-by-`|a|` times an integrable function
    refine Integrable.bdd_mul (c := |a|) hpdf_int (by
      have hcont_sech : Continuous sech := by
        -- `sech x = 1 / cosh x`
        have hcosh : Continuous Real.cosh := by simpa using Real.continuous_cosh
        have h0 : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => (Real.cosh_pos x).ne'
        have hsech_eq : sech = fun x : ℝ => (Real.cosh x)⁻¹ := by
          funext x
          simp [sech, Theorem1.sech, one_div]
        simpa [hsech_eq] using (Continuous.inv₀ hcosh h0)
      have hcont_inner : Continuous (fun x : ℝ => a * x) := continuous_const.mul continuous_id
      have hcont_sech_comp : Continuous (fun x : ℝ => sech (a * x)) := hcont_sech.comp hcont_inner
      have hcont_pow : Continuous (fun x : ℝ => (sech (a * x)) ^ 2) := by
        simpa using hcont_sech_comp.pow 2
      have : Continuous (fun x : ℝ => a * (sech (a * x)) ^ 2) := continuous_const.mul hcont_pow
      exact this.aestronglyMeasurable) ?_
    refine ae_of_all _ (fun x => ?_)
    have hsech_le_one : (sech (a * x)) ^ 2 ≤ (1 : ℝ) := by
      have hcosh_pos : 0 < Real.cosh (a * x) := Real.cosh_pos _
      have hcosh_ge : (1 : ℝ) ≤ Real.cosh (a * x) := Real.one_le_cosh _
      have hsech_le : sech (a * x) ≤ 1 := by
        -- `sech = 1/cosh` and `cosh ≥ 1`
        have : (1 : ℝ) / Real.cosh (a * x) ≤ (1 : ℝ) / (1 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num) hcosh_ge
        simpa [sech, Theorem1.sech] using this
      have hsech_nonneg : 0 ≤ sech (a * x) := by
        -- `sech = 1/cosh` and `cosh > 0`
        have : 0 ≤ (1 : ℝ) / Real.cosh (a * x) := by
          exact div_nonneg (by norm_num) hcosh_pos.le
        simpa [sech, Theorem1.sech] using this
      have hmul : sech (a * x) * sech (a * x) ≤ (1 : ℝ) * (1 : ℝ) := by
        exact mul_le_mul hsech_le hsech_le hsech_nonneg (by norm_num)
      simpa [pow_two] using hmul
    -- `‖a * sech^2‖ ≤ |a| * 1`
    have hnonneg : 0 ≤ (sech (a * x)) ^ 2 := sq_nonneg _
    have habs_sech : |(sech (a * x)) ^ 2| ≤ (1 : ℝ) := by
      simpa [abs_of_nonneg hnonneg] using hsech_le_one
    -- turn into a norm statement
    have : ‖a * (sech (a * x)) ^ 2‖ ≤ |a| := by
      -- `|a * sech^2| = |a| * |sech^2| ≤ |a| * 1`
      have hmul : |a| * |(sech (a * x)) ^ 2| ≤ |a| * (1 : ℝ) :=
        mul_le_mul_of_nonneg_left habs_sech (abs_nonneg a)
      simpa [Real.norm_eq_abs, abs_mul, mul_assoc] using hmul
    simpa [Real.norm_eq_abs] using this

  have huv_int' : Integrable (fun x : ℝ => Real.tanh (a * x) * pdf x) := huv_int

  -- Apply integration by parts: `∫ u * v' = - ∫ u' * v`.
  have hibp :=
    MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun x : ℝ => Real.tanh (a * x))
      (u' := fun x : ℝ => a * (sech (a * x)) ^ 2)
      (v := pdf)
      (v' := fun x : ℝ => -x * pdf x)
      hu hv' huv'_int hu'v_int huv_int'

  -- Rearrange to the desired Stein identity in `ℝ`.
  have hstein :
      (∫ x : ℝ, (pdf x) * (x * Real.tanh (a * x))) =
        a * ∫ x : ℝ, (pdf x) * (sech (a * x)) ^ 2 := by
    -- From `hibp`: `∫ tanh(a*x) * (-x*pdf x) = - ∫ (a*sech^2) * pdf x`.
    -- Cancel the minus sign using `integral_neg`.
    have hibp' :
        (∫ x : ℝ, Real.tanh (a * x) * (x * pdf x)) =
          ∫ x : ℝ, (a * (sech (a * x)) ^ 2) * pdf x := by
      have hneg :
          -(∫ x : ℝ, Real.tanh (a * x) * (x * pdf x)) =
            -∫ x : ℝ, (a * (sech (a * x)) ^ 2) * pdf x := by
        have hL :
            (fun x : ℝ => Real.tanh (a * x) * (-x * pdf x)) =
              fun x : ℝ => -(Real.tanh (a * x) * (x * pdf x)) := by
          funext x
          ring
        have h1 :
            (∫ x : ℝ, -(Real.tanh (a * x) * (x * pdf x))) =
              -∫ x : ℝ, (a * (sech (a * x)) ^ 2) * pdf x := by
          simpa [hL] using hibp
        -- `∫ -f = -∫ f`
        simpa [MeasureTheory.integral_neg] using h1
      exact (neg_inj).1 hneg

    calc
      (∫ x : ℝ, pdf x * (x * Real.tanh (a * x))) =
          ∫ x : ℝ, Real.tanh (a * x) * (x * pdf x) := by
            congr with x
            ring
      _ = ∫ x : ℝ, (a * (sech (a * x)) ^ 2) * pdf x := by
            simpa using hibp'
      _ = a * ∫ x : ℝ, pdf x * (sech (a * x)) ^ 2 := by
            calc
              (∫ x : ℝ, (a * (sech (a * x)) ^ 2) * pdf x) =
                  ∫ x : ℝ, a * (pdf x * (sech (a * x)) ^ 2) := by
                    congr with x
                    ring
              _ = a * ∫ x : ℝ, pdf x * (sech (a * x)) ^ 2 := by
                    simpa using
                      (MeasureTheory.integral_const_mul a (fun x : ℝ => pdf x * (sech (a * x)) ^ 2))

  -- Convert back to `Expect`.
  -- Left side:
  have hL :
      Expect (fun z => z * Real.tanh (a * z)) = ∫ x : ℝ, pdf x * (x * Real.tanh (a * x)) := by
    simpa [a] using (hExpect (fun z => z * Real.tanh (a * z)))
  -- Right side:
  have hR :
      Expect (fun z => (sech (a * z)) ^ 2) = ∫ x : ℝ, pdf x * (sech (a * x)) ^ 2 := by
    simpa [a] using (hExpect (fun z => (sech (a * z)) ^ 2))
  -- Finish.
  -- Put everything together.
  simpa [a, hL, hR] using hstein

lemma expect_log_cosh_le_r_mul_S (r : ℝ) (hr : 0 ≤ r) :
    Expect (fun z => Real.log (Real.cosh (Real.sqrt r * z))) ≤ r * S r := by
  -- Blueprint Step 2.3 (combine S1+S2 and `S(r)=E[sech^2]`).
  classical
  haveI : IsProbabilityMeasure γ := by infer_instance
  -- pointwise inequality `log(cosh x) ≤ x*tanh x`
  have hpoint :
      ∀ z : ℝ,
        Real.log (Real.cosh (Real.sqrt r * z)) ≤
          (Real.sqrt r * z) * Real.tanh (Real.sqrt r * z) := by
    intro z
    simpa using (log_cosh_le_mul_tanh (Real.sqrt r * z))

  -- integrability of the RHS (bounded by `|sqrt r| * |z|`).
  have hz_mem :
      MeasureTheory.MemLp (fun z : ℝ => z) (2 : ℝ≥0∞) γ := by
    simpa [γ, Theorem1.γ] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0)))
  have hz_int : Integrable (fun z : ℝ => z) γ := by
    have hq1 : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
    exact MeasureTheory.MemLp.integrable (μ := γ) (q := (2 : ℝ≥0∞)) hq1 hz_mem

  have hR_int : Integrable (fun z : ℝ => (Real.sqrt r * z) * Real.tanh (Real.sqrt r * z)) γ := by
    -- dominate by `|sqrt r| * |z|`
    have hdom : ∀ᵐ z ∂γ, ‖(Real.sqrt r * z) * Real.tanh (Real.sqrt r * z)‖ ≤
        ‖Real.sqrt r‖ * ‖z‖ := by
      refine ae_of_all _ (fun z => ?_)
      -- `|tanh| ≤ 1`
      have htanh_sq : (Real.tanh (Real.sqrt r * z)) ^ 2 ≤ (1 : ℝ) := by
        have hId := PropAP.tanh_sq_add_sech_sq (Real.sqrt r * z)
        have hsech : 0 ≤ (PropAP.sech (Real.sqrt r * z)) ^ 2 := sq_nonneg _
        linarith
      have htanh_abs : |Real.tanh (Real.sqrt r * z)| ≤ 1 :=
        (sq_le_one_iff_abs_le_one (Real.tanh (Real.sqrt r * z))).1 htanh_sq
      -- now
      calc
        ‖(Real.sqrt r * z) * Real.tanh (Real.sqrt r * z)‖ =
            |Real.sqrt r * z| * |Real.tanh (Real.sqrt r * z)| := by
              simp [Real.norm_eq_abs, abs_mul]
        _ ≤ |Real.sqrt r * z| * (1 : ℝ) :=
              mul_le_mul_of_nonneg_left htanh_abs (abs_nonneg _)
        _ = |Real.sqrt r * z| := by simp
        _ = |Real.sqrt r| * |z| := by simp [abs_mul]
        _ = ‖Real.sqrt r‖ * ‖z‖ := by simp [Real.norm_eq_abs]
    have hbound_int : Integrable (fun z : ℝ => ‖Real.sqrt r‖ * ‖z‖) γ := by
      simpa using (hz_int.norm.const_mul ‖Real.sqrt r‖)
    exact hbound_int.mono' (by fun_prop) hdom

  -- integrability of the LHS (same bound as in `RSFunctional_eq_RSFunctionalSplit`).
  have hsq_int : Integrable (fun z : ℝ => z ^ 2) γ := by
    simpa [γ, Theorem1.γ] using
      (MeasureTheory.MemLp.integrable_sq
        (ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))))
  have hlogcosh_int :
      Integrable (fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z))) γ := by
    -- `log(cosh x) ≤ x^2/2` and `x^2` is integrable.
    have hsq_int' :
        Integrable (fun z : ℝ => (Real.sqrt r * z) ^ 2 / 2) γ := by
      have hEq :
          (fun z : ℝ => (Real.sqrt r * z) ^ 2 / 2) =
            fun z => ((Real.sqrt r) ^ 2 / 2) * (z ^ 2) := by
        funext z
        ring
      simpa [hEq] using (hsq_int.const_mul ((Real.sqrt r) ^ 2 / 2))
    refine hsq_int'.mono ?_ ?_
    ·
      have : Measurable fun z : ℝ => Real.log (Real.cosh (Real.sqrt r * z)) := by fun_prop
      exact this.aestronglyMeasurable
    ·
      refine ae_of_all _ (fun z => ?_)
      have hxpos : 0 < Real.cosh (Real.sqrt r * z) := Real.cosh_pos _
      have hlog_nonneg :
          0 ≤ Real.log (Real.cosh (Real.sqrt r * z)) := by
        have := Real.log_le_log (x := (1 : ℝ)) (y := Real.cosh (Real.sqrt r * z))
          (by norm_num) (Real.one_le_cosh _)
        simpa using this
      have hx_le :
          Real.log (Real.cosh (Real.sqrt r * z)) ≤ (Real.sqrt r * z) ^ 2 / 2 := by
        have hcosh : Real.cosh (Real.sqrt r * z) ≤ Real.exp ((Real.sqrt r * z) ^ 2 / 2) := by
          simpa using (Real.cosh_le_exp_half_sq (Real.sqrt r * z))
        exact (Real.log_le_iff_le_exp hxpos).2 hcosh
      have hR_nonneg : 0 ≤ (Real.sqrt r * z) ^ 2 / 2 := by
        have : 0 ≤ (Real.sqrt r * z) ^ 2 := sq_nonneg _
        nlinarith
      have hnormL :
          ‖Real.log (Real.cosh (Real.sqrt r * z))‖ = Real.log (Real.cosh (Real.sqrt r * z)) := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
      have hnormR :
          ‖(Real.sqrt r * z) ^ 2 / 2‖ = (Real.sqrt r * z) ^ 2 / 2 := by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg hR_nonneg
      simpa [hnormL, hnormR] using hx_le

  -- Apply `integral_mono_ae` and the IBP identity.
  have hle_int :
      Expect (fun z => Real.log (Real.cosh (Real.sqrt r * z))) ≤
        Expect (fun z => (Real.sqrt r * z) * Real.tanh (Real.sqrt r * z)) := by
    unfold Expect Theorem1.Expect
    refine MeasureTheory.integral_mono_ae hlogcosh_int hR_int ?_
    exact ae_of_all _ hpoint

  -- Rewrite the RHS using the Gaussian IBP and `S`.
  have hR :
      Expect (fun z => (Real.sqrt r * z) * Real.tanh (Real.sqrt r * z)) =
        r * S r := by
    -- pull out `sqrt r` and apply `gaussian_ibp_tanh`
    unfold S Theorem1.S
    have hpull :
        Expect (fun z => (Real.sqrt r * z) * Real.tanh (Real.sqrt r * z)) =
          Real.sqrt r * Expect (fun z => z * Real.tanh (Real.sqrt r * z)) := by
      unfold Expect Theorem1.Expect
      -- rearrange and pull out the constant
      have hEq :
          (fun z : ℝ => (Real.sqrt r * z) * Real.tanh (Real.sqrt r * z)) =
            fun z : ℝ => Real.sqrt r * (z * Real.tanh (Real.sqrt r * z)) := by
        funext z
        ring
      -- `∫ c * f = c * ∫ f`
      simpa [hEq] using
        (MeasureTheory.integral_const_mul (μ := γ) (Real.sqrt r)
          (fun z : ℝ => z * Real.tanh (Real.sqrt r * z)))
    -- Apply the Stein identity.
    have hibp : Expect (fun z => z * Real.tanh (Real.sqrt r * z)) =
        Real.sqrt r * Expect (fun z => (sech (Real.sqrt r * z)) ^ 2) :=
      gaussian_ibp_tanh (r := r)
    -- combine and use `sq_sqrt` (requires `r ≥ 0`).
    calc
      Expect (fun z => (Real.sqrt r * z) * Real.tanh (Real.sqrt r * z))
          = Real.sqrt r * Expect (fun z => z * Real.tanh (Real.sqrt r * z)) := hpull
      _ = Real.sqrt r * (Real.sqrt r * Expect (fun z => (sech (Real.sqrt r * z)) ^ 2)) := by
            simp [hibp]
      _ = (Real.sqrt r) ^ 2 * Expect (fun z => (sech (Real.sqrt r * z)) ^ 2) := by ring
      _ = r * Expect (fun z => (sech (Real.sqrt r * z)) ^ 2) := by
            simpa [pow_two, Real.sq_sqrt hr] using rfl
      _ = r * S r := by simp [S, Theorem1.S, Expect, Theorem1.Expect]

  exact le_trans hle_int (by simpa [hR])

lemma spin_term_bound
    (r q : ℝ) (hr : 0 ≤ r) (hq : q = P r) :
    -(r * (1 - q) / 2) + Expect (fun z => Real.log (Real.cosh (Real.sqrt r * z))) ≤
      (r * (1 - q) / 2) := by
  -- Blueprint Step 2.3 (S3) + algebra.
  -- Use `expect_log_cosh_le_r_mul_S` and `Theorem1.S_eq_one_sub_P`.
  have hlog : Expect (fun z => Real.log (Real.cosh (Real.sqrt r * z))) ≤ r * S r :=
    expect_log_cosh_le_r_mul_S (r := r) hr
  have hS : S r = 1 - P r := Theorem1.S_eq_one_sub_P (r := r)
  -- Replace `S` and `q`.
  have hlog' : Expect (fun z => Real.log (Real.cosh (Real.sqrt r * z))) ≤ r * (1 - q) := by
    simpa [hS, hq, mul_assoc] using hlog
  -- Finish by algebra.
  linarith

/-! ### Step 2.4: constraint term bound -/

def Cδ (δ : ℝ) : ℝ := -Real.log (δ / 2)

lemma log_Φbar_le_neg_sq_div_two {u : ℝ} (hu : 0 < u) :
    Real.log (Φbar u) ≤ -(u ^ 2) / 2 := by
  -- Blueprint Step 2.4 (C2.i): Chernoff bound for Gaussian tails.
  sorry

lemma log_Φbar_le_neg_sq_div_two_sub_log {u : ℝ} (hu : 0 < u) :
    Real.log (Φbar u) ≤ -(u ^ 2) / 2 - Real.log u := by
  -- Blueprint Step 2.4 (C2.ii): Mills bound refinement `Φbar(u) ≤ φ(u)/u`.
  sorry

/-! ### Step 2.5: compare `B(κ,q)` and `A_n` (and bound the gap) -/

lemma E_sq_ge_uplus_sq (u : ℝ) : (E u) ^ 2 ≥ (max u 0) ^ 2 := by
  -- Blueprint Step 2.5 (BA1): for u>0 use Mills lower bound `E(u) ≥ u`.
  sorry

lemma exists_C0_E_sq_sub_uplus_sq_le :
    ∃ C0 : ℝ, ∀ u : ℝ, 0 ≤ (E u) ^ 2 - (max u 0) ^ 2 ∧ (E u) ^ 2 - (max u 0) ^ 2 ≤ C0 := by
  -- Blueprint Step 2.5 (BA2): case split u≤0 / u≥1 / u∈[0,1].
  sorry

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
  -- Blueprint Step 2.1: εₙ = 1 - qₙ and qₙ → 1.
  have hq :
      Tendsto (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_qn_one (κ := κ) (hκ := hκ) (α := α) (hα := hα) hlim
  have h1 : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hsub := h1.sub hq
  simpa [εn, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub

lemma qn_eq_P_rn (n : ℕ) :
    qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
      P (rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) := by
  -- From `Theorem1.qSol_spec`.
  simpa [qn, rn] using
    (Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2).2.2.2.1

lemma rn_eq_alpha_mul_B_div_eps_sq (n : ℕ) :
    rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
      (α n) * B κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) /
        (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) ^ 2 := by
  -- Combine `Theorem1.qSol_spec` (gives `r = R κ q α`) with `Theorem1.R_eq`.
  have hspec := Theorem1.qSol_spec κ (α n) hκ (hα n).1 (hα n).2
  have hq_lt1 :
      qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n < 1 := by
    simpa [qn] using hspec.2.1
  have hr :
      rn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n =
        R κ (qn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) (α n) := by
    simpa [rn, qn] using hspec.2.2.2.2
  -- Expand `R` via `R_eq` and rewrite `1 - qn = εn`.
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

lemma RSStarSeq_le_main_bound
    (hlim : Tendsto α atTop (𝓝 (αc κ)))
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C0 : ℝ,
      ∀ᶠ n in atTop,
        RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα) n
          ≤ (α n * (Φ (κ - δ)) / 2) * Real.log (εn (κ := κ) (hκ := hκ) (α := α) (hα := hα) n) + C0 := by
  -- Blueprint Steps 2.2–2.6: spin bound + constraint bound + (B-A)/ε bound.
  sorry

theorem theorem_three_seq (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    Tendsto (RSStarSeq (κ := κ) (hκ := hκ) (α := α) (hα := hα)) atTop atBot := by
  -- Blueprint Step 2.7:
  -- use `RSStarSeq_le_main_bound`, `εₙ → 0` so `log εₙ → -∞`,
  -- and positivity of `αc κ` and `Φ(κ-δ)`.
  sorry

end Seq

end
end Theorem3
