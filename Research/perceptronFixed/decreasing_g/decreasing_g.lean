import Mathlib

import perceptronFixed.conditionalGaussianMoments.CGM
import Main

open scoped BigOperators Topology NNReal
open MeasureTheory

namespace DecreasingG

noncomputable section

/-!
This file is a Lean skeleton (with `sorry`) for the blueprint
`decreasing_g/blueprint.txt`.

Goal (main.tex Lemma “g-decreasing-positive”):
  `g` is strictly decreasing on `[0, ∞)`.

The proof strategy is:
  1. Differentiate `g` and show `deriv g u = 2 * (E u)^2 * H u`.
  2. Rewrite `d(u) * H(u)` as a bivariate polynomial `F(x,y)` in
     `x = u * d(u)` and `y = d(u)^2`.
  3. Use moment-positivity constraints to show `(x,y)` lies in the feasible
     region where `F(x,y) < 0` (via the lemma in `negative_F_bound`).
  4. Conclude `H(u) < 0`, hence `deriv g u < 0` for `u ≥ 0`, hence strict
     decrease on `[0,∞)`.
-/

/-! ## Definitions (matching `main.tex`) -/

/-- Standard normal density `φ(u) = exp(-u^2/2) / sqrt(2π)`. -/
def φ (u : ℝ) : ℝ :=
  Real.exp (-(u ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- Standard normal upper tail `Φ̄(u) = ∫_{x≥u} φ(x) dx`. -/
def Φbar (u : ℝ) : ℝ :=
  ∫ x in Set.Ici u, φ x

/-- Inverse Mills ratio `E(u) = φ(u) / Φ̄(u)`. -/
def E (u : ℝ) : ℝ :=
  φ u / Φbar u

/-- Mean excess `d(u) = E(u) - u`. -/
def d (u : ℝ) : ℝ :=
  E u - u

/-- The auxiliary function `g` from `main.tex` (equation `g-expanded`). -/
def g (u : ℝ) : ℝ :=
  (E u) ^ 2 * (3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2)

/-- The polynomial expression controlling the sign of `g'`. -/
def H (u : ℝ) : ℝ :=
  u ^ 2 * d u + 6 * u * (d u) ^ 2 + 6 * (d u) ^ 3 - u - 4 * d u

/-- Coordinates used in the reduction `d(u) * H(u) = F(x,y)`. -/
def x (u : ℝ) : ℝ :=
  u * d u

def y (u : ℝ) : ℝ :=
  (d u) ^ 2

/-- The bivariate polynomial appearing after the change of variables. -/
def F (x y : ℝ) : ℝ :=
  x ^ 2 + 6 * x * y + 6 * y ^ 2 - x - 4 * y

/-- The quadratic constraint used in the `F < 0` lemma. -/
def q (x y : ℝ) : ℝ :=
  x ^ 2 + x * y - 3 * x - 3 * y + 2

/-! ## Analytic / probabilistic inputs (placeholders) -/

lemma Φbar_pos (u : ℝ) : 0 < Φbar u := by
  -- This is exactly `TruncatedNormalMoments.tail_pos` (same integrand).
  simpa [Φbar, φ, TruncatedNormalMoments.tail, TruncatedNormalMoments.φ] using
    (TruncatedNormalMoments.tail_pos u)

lemma E_pos (u : ℝ) : 0 < E u := by
  -- Uses `φ(u) > 0` and `Φbar_pos`.
  have hφ : 0 < φ u := by
    have hnum : 0 < Real.exp (-(u ^ 2) / 2) := Real.exp_pos _
    have hden : 0 < Real.sqrt (2 * Real.pi) := by
      have h2pi : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
      exact Real.sqrt_pos.2 h2pi
    simpa [φ] using div_pos hnum hden
  exact div_pos hφ (Φbar_pos u)

/-! ## Helper lemmas for `φ` and integrals -/

private lemma φ_eq_gaussianPDFReal : φ = ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) := by
  funext x
  simp [φ, ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

private lemma integral_φ_eq_one : (∫ x : ℝ, φ x) = 1 := by
  have hv : (1 : ℝ≥0) ≠ 0 := by simp
  simpa [φ_eq_gaussianPDFReal] using
    (ProbabilityTheory.integral_gaussianPDFReal_eq_one (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)

private lemma continuous_φ : Continuous φ := by
  unfold φ
  fun_prop

private lemma integrable_φ : Integrable φ := by
  change Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi))
  have h : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
    have h' :
        (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) =
          fun x : ℝ => Real.exp (-((1 / 2 : ℝ) * x ^ 2)) := by
      funext x
      ring_nf
    simpa [h'] using (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num))
  exact h.div_const (Real.sqrt (2 * Real.pi))

private lemma tendsto_φ_atTop : Filter.Tendsto φ Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)) Filter.atTop (𝓝 0)
  have hpow : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop := by
    simpa using (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hneg : Filter.Tendsto (fun x : ℝ => -(x ^ 2)) Filter.atTop Filter.atBot :=
    (Filter.tendsto_neg_atTop_atBot).comp hpow
  have hneg_div : Filter.Tendsto (fun x : ℝ => -(x ^ 2) / (2 : ℝ)) Filter.atTop Filter.atBot :=
    hneg.atBot_div_const (by norm_num)
  have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg_div
  simpa using hexp.div_const (Real.sqrt (2 * Real.pi))

private lemma hasDerivAt_φ (u : ℝ) : HasDerivAt φ (-u * φ u) u := by
  change
    HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi))
      (-u * (Real.exp (-(u ^ 2) / 2) / Real.sqrt (2 * Real.pi))) u
  have h_inner : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-u) u := by
    have h_pow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
      simpa using (hasDerivAt_pow (n := 2) (x := u))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using (h_pow.neg.div_const (2 : ℝ))
  have h_exp :
      HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2))
        (Real.exp (-(u ^ 2) / 2) * (-u)) u := by
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (x := (-(u ^ 2) / 2))).comp u h_inner
  have h_div :
      HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi))
        (Real.exp (-(u ^ 2) / 2) * (-u) / Real.sqrt (2 * Real.pi)) u := by
    simpa [div_eq_mul_inv] using h_exp.div_const (Real.sqrt (2 * Real.pi))
  -- simplify the derivative expression into `-u * φ u`
  simpa [mul_assoc, mul_left_comm, mul_comm, mul_div_assoc, div_eq_mul_inv, neg_mul, neg_div] using
    h_div

private lemma deriv_φ (u : ℝ) : deriv φ u = -u * φ u :=
  (hasDerivAt_φ u).deriv

private lemma integrable_mul_φ : Integrable (fun x : ℝ => x * φ x) := by
  have h : Integrable (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) := by
    have h' :
        (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) =
          fun x : ℝ => x * Real.exp (-((1 / 2 : ℝ) * x ^ 2)) := by
      funext x
      ring_nf
    simpa [h'] using (integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num))
  -- divide by the (nonzero) normalizing constant
  simpa [φ, mul_div_assoc, mul_assoc] using h.div_const (Real.sqrt (2 * Real.pi))

private lemma integral_mul_φ_eq (u : ℝ) : (∫ x in Set.Ici u, x * φ x) = φ u := by
  -- Compute `∫_{u}^{∞} x φ(x) dx` by integrating `φ' = -x φ`.
  have hderiv : ∀ x ∈ Set.Ici u, HasDerivAt φ (-x * φ x) x := by
    intro x _hx
    simpa using (hasDerivAt_φ x)
  have hint : IntegrableOn (fun x : ℝ => -x * φ x) (Set.Ioi u) := by
    simpa [neg_mul] using (integrable_mul_φ.neg).integrableOn
  have hIoi :
      (∫ x in Set.Ioi u, -x * φ x) = -φ u := by
    simpa using
      (MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
        (a := u) (f := φ) (f' := fun x : ℝ => -x * φ x) (m := (0 : ℝ)) hderiv hint tendsto_φ_atTop)
  have hIoi' : (∫ x in Set.Ioi u, x * φ x) = φ u := by
    have : -(∫ x in Set.Ioi u, -x * φ x) = φ u := by
      simpa using congrArg Neg.neg hIoi
    simpa [MeasureTheory.integral_neg, neg_mul] using this
  simpa [MeasureTheory.integral_Ici_eq_integral_Ioi] using hIoi'

  lemma d_pos (u : ℝ) : 0 < d u := by
  -- `d(u) > 0` for all `u`.
  have hΦbar : 0 < Φbar u := Φbar_pos u

  have hφpos : ∀ x : ℝ, 0 < φ x := by
    intro x
    have hnum : 0 < Real.exp (-(x ^ 2) / 2) := Real.exp_pos _
    have hden : 0 < Real.sqrt (2 * Real.pi) := by
      have h2pi : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
      exact Real.sqrt_pos.2 h2pi
    simpa [φ] using div_pos hnum hden

  have hnum : φ u - u * Φbar u = ∫ x in Set.Ici u, (x - u) * φ x := by
    have h₁ : (∫ x in Set.Ici u, x * φ x) = φ u := integral_mul_φ_eq (u := u)
    calc
      φ u - u * Φbar u
          = (∫ x in Set.Ici u, x * φ x) - u * (∫ x in Set.Ici u, φ x) := by
              simp [h₁, Φbar]
      _ = (∫ x in Set.Ici u, x * φ x) - ∫ x in Set.Ici u, u * φ x := by
            simp [MeasureTheory.integral_const_mul]
      _ = ∫ x in Set.Ici u, (x * φ x - u * φ x) := by
            have hi₁ : IntegrableOn (fun x : ℝ => x * φ x) (Set.Ici u) :=
              integrable_mul_φ.integrableOn
            have hi₂ : IntegrableOn (fun x : ℝ => u * φ x) (Set.Ici u) :=
              (integrable_φ.const_mul u).integrableOn
            simpa using (MeasureTheory.integral_sub hi₁ hi₂).symm
      _ = ∫ x in Set.Ici u, (x - u) * φ x := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun x _hx => ?_)
            ring

  have hpos_int : 0 < ∫ x in Set.Ici u, (x - u) * φ x := by
    -- Use the `support` characterization for nonnegative integrals.
    set μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici u)
    have hnonneg : 0 ≤ᶠ[ae μ] fun x : ℝ => (x - u) * φ x := by
      show ∀ᵐ x ∂μ, 0 ≤ (x - u) * φ x
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      refine ae_of_all _ (fun x hx => ?_)
      exact mul_nonneg (sub_nonneg.2 hx) (le_of_lt (hφpos x))
    have hint : Integrable (fun x : ℝ => (x - u) * φ x) μ := by
      simpa [μ, φ, TruncatedNormalMoments.φ, pow_one] using
        (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 1) u)
    have hsupp : 0 < μ (Function.support fun x : ℝ => (x - u) * φ x) := by
      have hsub : Set.Ioc u (u + 1) ⊆ Function.support fun x : ℝ => (x - u) * φ x := by
        intro x hx
        have hx0 : x - u ≠ 0 := sub_ne_zero.2 (ne_of_gt hx.1)
        have hφx : φ x ≠ 0 := (hφpos x).ne'
        exact mul_ne_zero hx0 hφx
      have hIoc_pos : 0 < μ (Set.Ioc u (u + 1)) := by
        have hsubset : Set.Ioc u (u + 1) ⊆ Set.Ici u := by
          intro x hx
          exact le_of_lt hx.1
        have hab : (0 : ℝ) < u + 1 - u := by linarith
        have hvol : 0 < (volume : Measure ℝ) (Set.Ioc u (u + 1)) := by
          simpa [Real.volume_Ioc] using (ENNReal.ofReal_pos.2 hab)
        simpa [μ, Measure.restrict_apply, measurableSet_Ioc, Set.inter_eq_left.2 hsubset] using hvol
      exact lt_of_lt_of_le hIoc_pos (MeasureTheory.measure_mono hsub)
    have : 0 < ∫ x : ℝ, (x - u) * φ x ∂μ :=
      (MeasureTheory.integral_pos_iff_support_of_nonneg_ae (μ := μ)
            (f := fun x : ℝ => (x - u) * φ x) hnonneg hint).2 hsupp
    simpa [μ] using this

  have hd : d u = (φ u - u * Φbar u) / Φbar u := by
    have hΦ : Φbar u ≠ 0 := hΦbar.ne'
    unfold d E
    field_simp [hΦ]
  rw [hd, hnum]
  exact div_pos hpos_int hΦbar

  /-! ## Derivatives of `Φbar`, `E`, and monotonicity of `d` -/

  /-- Standard normal CDF `Φ(u) = ∫_{x≤u} φ(x) dx` (auxiliary definition). -/
  private def Φ (u : ℝ) : ℝ :=
    ∫ x in Set.Iic u, φ x

  private lemma Φ_eq_const_add_intervalIntegral (u : ℝ) :
      Φ u = (∫ x in Set.Iic (0 : ℝ), φ x) + ∫ x : ℝ in (0 : ℝ)..u, φ x := by
    classical
    by_cases hu : 0 ≤ u
    ·
      have hset : Set.Iic u = Set.Iic (0 : ℝ) ∪ Set.Ioc (0 : ℝ) u := by
        ext x
        constructor
        · intro hx
          rcases le_or_lt x 0 with hx0 | hx0
          · exact Or.inl hx0
          · exact Or.inr ⟨hx0, hx⟩
        · intro hx
          rcases hx with hx | hx
          · exact le_trans hx hu
          · exact hx.2
      have hdis : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioc (0 : ℝ) u) := by
        refine Set.disjoint_left.2 ?_
        intro x hx0 hxoc
        exact (not_lt_of_ge hx0) hxoc.1
      have hunion :
          (∫ x in Set.Iic u, φ x) =
            (∫ x in Set.Iic (0 : ℝ), φ x) + ∫ x in Set.Ioc (0 : ℝ) u, φ x := by
        simpa [Φ, hset] using
          (MeasureTheory.setIntegral_union (μ := (volume : Measure ℝ)) (f := φ) hdis
            measurableSet_Ioc (integrable_φ.integrableOn) (integrable_φ.integrableOn))
      have hint : (∫ x in Set.Ioc (0 : ℝ) u, φ x) = ∫ x : ℝ in (0 : ℝ)..u, φ x := by
        simpa [intervalIntegral.integral_of_le (μ := volume) (f := φ) hu] using
          (intervalIntegral.integral_of_le (μ := volume) (f := φ) (a := (0 : ℝ)) (b := u) hu).symm
      simpa [Φ, hunion, hint]
    ·
      have hu' : u ≤ 0 := le_of_not_ge hu
      have hset : Set.Iic (0 : ℝ) = Set.Iic u ∪ Set.Ioc u (0 : ℝ) := by
        ext x
        constructor
        · intro hx0
          by_cases hx : x ≤ u
          · exact Or.inl hx
          · have hxgt : u < x := lt_of_not_ge hx
            exact Or.inr ⟨hxgt, hx0⟩
        · intro hx
          rcases hx with hx | hx
          · exact le_trans hx hu'
          · exact hx.2
      have hdis : Disjoint (Set.Iic u) (Set.Ioc u (0 : ℝ)) := by
        refine Set.disjoint_left.2 ?_
        intro x hxu hxoc
        exact (not_lt_of_ge hxu) hxoc.1
      have hunion :
          (∫ x in Set.Iic (0 : ℝ), φ x) =
            (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioc u (0 : ℝ), φ x := by
        simpa [hset] using
          (MeasureTheory.setIntegral_union (μ := (volume : Measure ℝ)) (f := φ) hdis
            measurableSet_Ioc (integrable_φ.integrableOn) (integrable_φ.integrableOn))
      have hsolve :
          (∫ x in Set.Iic u, φ x) =
            (∫ x in Set.Iic (0 : ℝ), φ x) - ∫ x in Set.Ioc u (0 : ℝ), φ x := by
        linarith
      have hint : (∫ x in (0 : ℝ)..u, φ x) = -∫ x in Set.Ioc u (0 : ℝ), φ x := by
        simpa using
          (intervalIntegral.integral_of_ge (μ := volume) (f := φ) (a := (0 : ℝ)) (b := u) hu')
      simp [Φ, hsolve, hint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

  private lemma hasDerivAt_Φ (u : ℝ) : HasDerivAt Φ (φ u) u := by
    -- Rewrite `Φ` as a constant plus an interval integral, then apply FTC-1.
    let C : ℝ := ∫ x in Set.Iic (0 : ℝ), φ x
    have hfun : Φ = fun s : ℝ => C + ∫ x : ℝ in (0 : ℝ)..s, φ x := by
      funext s
      simpa [C, Φ_eq_const_add_intervalIntegral (u := s)]
    have hInt :
        HasDerivAt (fun s : ℝ => ∫ x : ℝ in (0 : ℝ)..s, φ x) (φ u) u :=
      intervalIntegral.integral_hasDerivAt_right
        (hf := (continuous_φ.intervalIntegrable _ _))
        (hmeas := (continuous_φ.stronglyMeasurableAtFilter _ _))
        (hb := (continuous_φ.continuousAt))
    have hsum : HasDerivAt (fun s : ℝ => C + ∫ x : ℝ in (0 : ℝ)..s, φ x) (φ u) u := by
      simpa using hInt.const_add C
    simpa [hfun] using hsum

  private lemma deriv_Φ (u : ℝ) : deriv Φ u = φ u :=
    (hasDerivAt_Φ u).deriv

  private lemma Φbar_eq_one_sub_Φ (u : ℝ) : Φbar u = 1 - Φ u := by
    have hIci : Φbar u = ∫ x in Set.Ioi u, φ x := by
      simpa [Φbar] using
        (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := (volume : Measure ℝ)) (f := φ)
          (x := u))
    have hdis : Disjoint (Set.Iic u) (Set.Ioi u) := Set.Iic_disjoint_Ioi (a := u) (b := u) le_rfl
    have hunion :
        (∫ x in (Set.Iic u ∪ Set.Ioi u : Set ℝ), φ x) =
          (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
      simpa using
        (MeasureTheory.setIntegral_union (μ := (volume : Measure ℝ)) (f := φ)
          (s := Set.Iic u) (t := Set.Ioi u) hdis
          measurableSet_Ioi (integrable_φ.integrableOn) (integrable_φ.integrableOn))
    have hset : (Set.Iic u ∪ Set.Ioi u : Set ℝ) = Set.univ := by
      simpa using (Set.Iic_union_Ioi (a := u))
    have hsplit :
        (∫ x : ℝ, φ x) = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
      calc
        (∫ x : ℝ, φ x) = ∫ x in (Set.Iic u ∪ Set.Ioi u : Set ℝ), φ x := by
          simp [hset]
        _ = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := hunion
    -- Solve for the tail integral.
    have hIoi : ∫ x in Set.Ioi u, φ x = 1 - Φ u := by
      have : (∫ x in Set.Ioi u, φ x) = (∫ x : ℝ, φ x) - (∫ x in Set.Iic u, φ x) := by
        linarith [hsplit]
      simpa [Φ, integral_φ_eq_one] using this
    simpa [hIci, hIoi]

  private lemma hasDerivAt_Φbar (u : ℝ) : HasDerivAt Φbar (-φ u) u := by
    have hfun : Φbar = fun s : ℝ => 1 - Φ s := by
      funext s
      simpa [Φbar_eq_one_sub_Φ (u := s), Φ]
    -- Differentiate `Φbar = 1 - Φ`.
    simpa [hfun] using (hasDerivAt_Φ u).const_sub (1 : ℝ)

  lemma deriv_Φbar (u : ℝ) : deriv Φbar u = -φ u :=
    (hasDerivAt_Φbar u).deriv

  lemma deriv_E (u : ℝ) : deriv E u = (E u) ^ 2 - u * E u := by
    have hφ : DifferentiableAt ℝ φ u := (hasDerivAt_φ u).differentiableAt
    have hΦbar : DifferentiableAt ℝ Φbar u := (hasDerivAt_Φbar u).differentiableAt
    have h_div :
        deriv E u =
          (deriv φ u * Φbar u - φ u * deriv Φbar u) / (Φbar u) ^ 2 := by
      simpa [E] using (deriv_div hφ hΦbar (Φbar_pos u).ne')
    -- Substitute derivatives and simplify.
    rw [h_div, deriv_φ (u := u), deriv_Φbar (u := u)]
    have hΦ : Φbar u ≠ 0 := (Φbar_pos u).ne'
    -- Unfold `E` on the right-hand side before clearing denominators.
    simp [E, hΦ]
    field_simp [hΦ]
    ring_nf

lemma d0_eq_sqrt_two_div_pi : d 0 = Real.sqrt (2 / Real.pi) := by
  -- E(0) = √(2/π).
  have hφ_even : ∀ x : ℝ, φ (-x) = φ x := by
    intro x
    simp [φ]

  have hIci : Φbar 0 = ∫ x in Set.Ioi (0 : ℝ), φ x := by
    simpa [Φbar] using
      (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := (volume : Measure ℝ)) (f := φ) (x := (0 : ℝ)))

  have hsymm : (∫ x in Set.Iic (0 : ℝ), φ x) = ∫ x in Set.Ioi (0 : ℝ), φ x := by
    simpa [hφ_even] using (integral_comp_neg_Iic (c := (0 : ℝ)) (f := φ))

  have hunion :
      (∫ x in (Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ)), φ x) =
        (∫ x in Set.Iic (0 : ℝ), φ x) + ∫ x in Set.Ioi (0 : ℝ), φ x := by
    simpa using
      (MeasureTheory.setIntegral_union (μ := (volume : Measure ℝ)) (f := φ)
        (s := Set.Iic (0 : ℝ)) (t := Set.Ioi (0 : ℝ))
        (hst := Set.Iic_disjoint_Ioi (a := (0 : ℝ)) (b := (0 : ℝ)) le_rfl)
        measurableSet_Ioi (integrable_φ.integrableOn) (integrable_φ.integrableOn))

  have hset : (Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) : Set ℝ) = Set.univ := by
    simpa using (Set.Iic_union_Ioi (a := (0 : ℝ)))

  have hsplit :
      (∫ x : ℝ, φ x) = (∫ x in Set.Iic (0 : ℝ), φ x) + ∫ x in Set.Ioi (0 : ℝ), φ x := by
    calc
      (∫ x : ℝ, φ x) = ∫ x in (Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ)), φ x := by
          simp [hset]
      _ = (∫ x in Set.Iic (0 : ℝ), φ x) + ∫ x in Set.Ioi (0 : ℝ), φ x := hunion

  have hIoi : (∫ x in Set.Ioi (0 : ℝ), φ x) = (1 : ℝ) / 2 := by
    have htmp : (1 : ℝ) = 2 * ∫ x in Set.Ioi (0 : ℝ), φ x := by
      have : (∫ x : ℝ, φ x) = 2 * ∫ x in Set.Ioi (0 : ℝ), φ x := by
        calc
          (∫ x : ℝ, φ x) =
              (∫ x in Set.Iic (0 : ℝ), φ x) + ∫ x in Set.Ioi (0 : ℝ), φ x := hsplit
          _ = (∫ x in Set.Ioi (0 : ℝ), φ x) + ∫ x in Set.Ioi (0 : ℝ), φ x := by
              simpa [hsymm]
          _ = 2 * ∫ x in Set.Ioi (0 : ℝ), φ x := by ring
      simpa [integral_φ_eq_one] using this
    nlinarith

  have hΦbar0 : Φbar 0 = (1 : ℝ) / 2 := by
    calc
      Φbar 0 = ∫ x in Set.Ioi (0 : ℝ), φ x := hIci
      _ = (1 : ℝ) / 2 := hIoi

  have hE0 : E 0 = Real.sqrt (2 / Real.pi) := by
    have hsqrt2 : (Real.sqrt 2) ≠ 0 := (Real.sqrt_ne_zero').2 (by norm_num)
    have hsqrt2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
      simpa using (Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) Real.pi)
    calc
      E 0 = 2 / Real.sqrt (2 * Real.pi) := by
            simp [E, hΦbar0, φ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = 2 / (Real.sqrt 2 * Real.sqrt Real.pi) := by
            simpa [hsqrt2pi]
      _ = (Real.sqrt 2 * Real.sqrt 2) / (Real.sqrt 2 * Real.sqrt Real.pi) := by
            have htwo : (2 : ℝ) = Real.sqrt 2 * Real.sqrt 2 := by
              symm
              simpa using (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ)))
            -- rewrite `2` as `(Real.sqrt 2) * (Real.sqrt 2)`
            -- rewrite only the numerator `2`
            nth_rw 1 [htwo]
      _ = Real.sqrt 2 / Real.sqrt Real.pi := by
            simpa using
              (mul_div_mul_left (c := Real.sqrt 2) (a := Real.sqrt 2) (b := Real.sqrt Real.pi) hsqrt2)
      _ = Real.sqrt (2 / Real.pi) := by
            symm
            simpa using (Real.sqrt_div (x := (2 : ℝ)) (hx := by norm_num) Real.pi)

  simpa [d] using hE0

  /-! ## Algebraic identities used in the reduction -/

lemma d_mul_H_eq_F (u : ℝ) : d u * H u = F (x u) (y u) := by
  -- Pure algebra: expand both sides and use `x = u*d`, `y = d^2`.
  simp [H, F, x, y]
  ring

lemma H_neg_of_F_neg {u : ℝ} (hd : 0 < d u) (hF : F (x u) (y u) < 0) : H u < 0 := by
  have hmul : d u * H u < 0 := by
    simpa [d_mul_H_eq_F (u := u)] using hF
  -- Since `d u > 0`, divide the inequality `d u * H u < 0` by `d u`.
  have : d u * H u < d u * 0 := by simpa using hmul
  exact lt_of_mul_lt_mul_left this (le_of_lt hd)

  /-! ## Moment-positivity constraints (placeholders) -/

  private lemma tnm_tail_eq_Φbar (u : ℝ) :
      TruncatedNormalMoments.tail u = Φbar u := by
    simp [TruncatedNormalMoments.tail, Φbar, TruncatedNormalMoments.φ, φ]

  private lemma φ_sub_mul_Φbar_eq_tnm_J_one (u : ℝ) :
      φ u - u * Φbar u = TruncatedNormalMoments.J 1 u := by
    have h₁ : (∫ x in Set.Ici u, x * φ x) = φ u := integral_mul_φ_eq (u := u)
    have h :
        φ u - u * Φbar u = ∫ x in Set.Ici u, (x - u) * φ x := by
      calc
        φ u - u * Φbar u
            = (∫ x in Set.Ici u, x * φ x) - u * (∫ x in Set.Ici u, φ x) := by
                simp [h₁, Φbar]
        _ = (∫ x in Set.Ici u, x * φ x) - ∫ x in Set.Ici u, u * φ x := by
              simp [MeasureTheory.integral_const_mul]
        _ = ∫ x in Set.Ici u, (x * φ x - u * φ x) := by
              have hi₁ : IntegrableOn (fun x : ℝ => x * φ x) (Set.Ici u) :=
                integrable_mul_φ.integrableOn
              have hi₂ : IntegrableOn (fun x : ℝ => u * φ x) (Set.Ici u) :=
                (integrable_φ.const_mul u).integrableOn
              simpa using (MeasureTheory.integral_sub hi₁ hi₂).symm
        _ = ∫ x in Set.Ici u, (x - u) * φ x := by
              refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun x _hx => ?_)
              ring
    -- rewrite the integral as `TruncatedNormalMoments.J 1 u`
    simpa [TruncatedNormalMoments.J, pow_one, TruncatedNormalMoments.φ, φ, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using h

  private lemma tnm_d_eq_d (u : ℝ) : TruncatedNormalMoments.d u = d u := by
    have htail : TruncatedNormalMoments.tail u = Φbar u := tnm_tail_eq_Φbar (u := u)
    have hJ1 : TruncatedNormalMoments.J 1 u = φ u - u * Φbar u := by
      simpa [φ_sub_mul_Φbar_eq_tnm_J_one (u := u)] using (φ_sub_mul_Φbar_eq_tnm_J_one (u := u)).symm
    have hΦ : Φbar u ≠ 0 := (Φbar_pos u).ne'
    -- `TruncatedNormalMoments.d u = J 1 u / tail u`
    -- rewrite `J 1 u` using the integral identity and simplify.
    calc
      TruncatedNormalMoments.d u = TruncatedNormalMoments.J 1 u / TruncatedNormalMoments.tail u := rfl
      _ = (φ u - u * Φbar u) / Φbar u := by simp [hJ1, htail]
      _ = φ u / Φbar u - u := by
            field_simp [hΦ]
      _ = d u := rfl

  lemma constraint_detM1 {u : ℝ} (hu : 0 ≤ u) : 1 ≤ x u + 2 * y u := by
    -- Moment positivity: `det [[μ₁,μ₂],[μ₂,μ₃]] ≥ 0`.
    -- We derive `μ₂^2 ≤ μ₁ μ₃` by integrating the nonnegative function `Y*(t-Y)^2`.
    set J₁ : ℝ := TruncatedNormalMoments.J 1 u
    set J₂ : ℝ := TruncatedNormalMoments.J 2 u
    set J₃ : ℝ := TruncatedNormalMoments.J 3 u
    set T : ℝ := TruncatedNormalMoments.tail u
    have hT : 0 < T := TruncatedNormalMoments.tail_pos u
    have hTne : T ≠ 0 := hT.ne'
    have hJ₁_div : J₁ / T = d u := by
      -- `d(u) = J₁/T` via `tnm_d_eq_d`.
      simpa [J₁, T, TruncatedNormalMoments.d, TruncatedNormalMoments.μ] using (tnm_d_eq_d (u := u))
    have hJ₁ : J₁ = d u * T := (div_eq_iff hTne).1 hJ₁_div
    have hJ₁pos : 0 < J₁ := by nlinarith [hJ₁, d_pos u, hT]
    have hJ₁ne : J₁ ≠ 0 := hJ₁pos.ne'
    set t : ℝ := J₂ / J₁
    have hnonneg :
        0 ≤ ∫ x in Set.Ici u, ((x - u) * (t - (x - u)) ^ 2) * φ x := by
      refine MeasureTheory.setIntegral_nonneg (μ := (volume : Measure ℝ)) (s := Set.Ici u)
        measurableSet_Ici ?_
      intro x hx
      have hx0 : 0 ≤ x - u := sub_nonneg.2 hx
      have hsq : 0 ≤ (t - (x - u)) ^ 2 := sq_nonneg _
      have hφx : 0 ≤ φ x := by
        have hnum : 0 < Real.exp (-(x ^ 2) / 2) := Real.exp_pos _
        have hden : 0 < Real.sqrt (2 * Real.pi) := by
          have h2pi : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
          exact Real.sqrt_pos.2 h2pi
        exact le_of_lt (by simpa [φ] using div_pos hnum hden)
      exact mul_nonneg (mul_nonneg hx0 hsq) hφx
    have hIeq :
        (∫ x in Set.Ici u, ((x - u) * (t - (x - u)) ^ 2) * φ x) =
          ((t ^ 2) * J₁ - (2 * t) * J₂) + J₃ := by
      -- Short proof: expand and use integral linearity.
      have hi1 : IntegrableOn (fun x : ℝ => (x - u) * φ x) (Set.Ici u) := by
        simpa [φ, TruncatedNormalMoments.φ, pow_one] using
          (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 1) u)
      have hi2 : IntegrableOn (fun x : ℝ => (x - u) ^ 2 * φ x) (Set.Ici u) := by
        simpa [φ, TruncatedNormalMoments.φ] using
          (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 2) u)
      have hi3 : IntegrableOn (fun x : ℝ => (x - u) ^ 3 * φ x) (Set.Ici u) := by
        simpa [φ, TruncatedNormalMoments.φ] using
          (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 3) u)
      have h1 :
          IntegrableOn (fun x : ℝ => (t ^ 2) * ((x - u) * φ x)) (Set.Ici u) :=
        hi1.const_mul _
      have h2 :
          IntegrableOn (fun x : ℝ => (2 * t) * ((x - u) ^ 2 * φ x)) (Set.Ici u) :=
        hi2.const_mul _
      have h12 :
          IntegrableOn
            (fun x : ℝ => (t ^ 2) * ((x - u) * φ x) - (2 * t) * ((x - u) ^ 2 * φ x))
            (Set.Ici u) :=
        h1.sub h2
      calc
        (∫ x in Set.Ici u, ((x - u) * (t - (x - u)) ^ 2) * φ x) =
            ∫ x in Set.Ici u,
              (((t ^ 2) * ((x - u) * φ x) - (2 * t) * ((x - u) ^ 2 * φ x)) +
                    (x - u) ^ 3 * φ x) := by
              refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun x _hx => ?_)
              ring
        _ =
            (∫ x in Set.Ici u,
                  (t ^ 2) * ((x - u) * φ x) - (2 * t) * ((x - u) ^ 2 * φ x)) +
                ∫ x in Set.Ici u, (x - u) ^ 3 * φ x := by
              simpa using (MeasureTheory.integral_add h12 hi3)
        _ =
            ((∫ x in Set.Ici u, (t ^ 2) * ((x - u) * φ x)) -
                  ∫ x in Set.Ici u, (2 * t) * ((x - u) ^ 2 * φ x)) +
                ∫ x in Set.Ici u, (x - u) ^ 3 * φ x := by
              -- Rewrite the first integral using `integral_sub` (avoid `simp` cancelling `+ ∫ ...`).
              rw [MeasureTheory.integral_sub h1 h2]
        _ =
            (((t ^ 2) * (∫ x in Set.Ici u, (x - u) * φ x)) -
                  ((2 * t) * (∫ x in Set.Ici u, (x - u) ^ 2 * φ x))) +
                ∫ x in Set.Ici u, (x - u) ^ 3 * φ x := by
              simp [MeasureTheory.integral_const_mul, sub_eq_add_neg, add_assoc, mul_assoc]
        _ = ((t ^ 2) * J₁ - (2 * t) * J₂) + J₃ := by
              simp [J₁, J₂, J₃, TruncatedNormalMoments.J, TruncatedNormalMoments.φ, φ,
                pow_one, sub_eq_add_neg, add_assoc, mul_assoc]
    have hJdet : 0 ≤ J₁ * J₃ - J₂ ^ 2 := by
      have : 0 ≤ ((t ^ 2) * J₁ - (2 * t) * J₂) + J₃ := by simpa [hIeq] using hnonneg
      have : 0 ≤ J₁ * (((t ^ 2) * J₁ - (2 * t) * J₂) + J₃) :=
        mul_nonneg (le_of_lt hJ₁pos) this
      have hsim : J₁ * (((t ^ 2) * J₁ - (2 * t) * J₂) + J₃) = J₁ * J₃ - J₂ ^ 2 := by
        -- Expand `t = J₂/J₁`, clear denominators, and normalize.
        simp [t]
        field_simp [hJ₁ne]
        ring_nf
      simpa [hsim] using this
    have hμineq :
        (TruncatedNormalMoments.μ 2 u) ^ 2 ≤ (TruncatedNormalMoments.μ 1 u) * (TruncatedNormalMoments.μ 3 u) := by
      -- clear denominators in `μ k = J k / T`
      have : (J₂ / T) ^ 2 ≤ (J₁ / T) * (J₃ / T) := by
        field_simp [hTne]
        nlinarith [hJdet]
      simpa [TruncatedNormalMoments.μ, J₁, J₂, J₃, T] using this
    have hμ₁ : TruncatedNormalMoments.μ 1 u = d u := by
      simpa [TruncatedNormalMoments.μ_one, tnm_d_eq_d (u := u)] using rfl
    have hμ₂ : TruncatedNormalMoments.μ 2 u = 1 - u * d u := by
      simpa [tnm_d_eq_d (u := u)] using (TruncatedNormalMoments.μ_two u)
    have hμ₃ : TruncatedNormalMoments.μ 3 u = (u ^ 2 + 2) * d u - u := by
      simpa [tnm_d_eq_d (u := u)] using (TruncatedNormalMoments.μ_three u)
    have : 1 ≤ u * d u + 2 * (d u) ^ 2 := by
      have : (1 - u * d u) ^ 2 ≤ d u * ((u ^ 2 + 2) * d u - u) := by
        simpa [hμ₁, hμ₂, hμ₃] using hμineq
      nlinarith
    simpa [x, y, pow_two] using this

  lemma constraint_detM2 {u : ℝ} (hu : 0 ≤ u) : 0 ≤ q (x u) (y u) := by
    -- Comes from det [[μ0,μ1,μ2],[μ1,μ2,μ3],[μ2,μ3,μ4]] ≥ 0 using moment formulas.
    classical
    -- Tail and the two Hankel matrices of moments (unnormalized `J` and normalized `μ`).
    set T : ℝ := TruncatedNormalMoments.tail u
    have hT : 0 < T := TruncatedNormalMoments.tail_pos u
    have hTne : T ≠ 0 := hT.ne'

    let M : Matrix (Fin 3) (Fin 3) ℝ :=
      !![TruncatedNormalMoments.J 0 u, TruncatedNormalMoments.J 1 u, TruncatedNormalMoments.J 2 u;
        TruncatedNormalMoments.J 1 u, TruncatedNormalMoments.J 2 u, TruncatedNormalMoments.J 3 u;
        TruncatedNormalMoments.J 2 u, TruncatedNormalMoments.J 3 u, TruncatedNormalMoments.J 4 u]

    let A : Matrix (Fin 3) (Fin 3) ℝ :=
      !![TruncatedNormalMoments.μ 0 u, TruncatedNormalMoments.μ 1 u, TruncatedNormalMoments.μ 2 u;
        TruncatedNormalMoments.μ 1 u, TruncatedNormalMoments.μ 2 u, TruncatedNormalMoments.μ 3 u;
        TruncatedNormalMoments.μ 2 u, TruncatedNormalMoments.μ 3 u, TruncatedNormalMoments.μ 4 u]

    -- `M` is positive semidefinite since it is a moment (Gram) matrix.
    have hMherm : M.IsHermitian := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [M]

    have hMpos : ∀ z : Fin 3 → ℝ, 0 ≤ star z ⬝ᵥ M.mulVec z := by
      intro z
      set a : ℝ := z 0
      set b : ℝ := z 1
      set c : ℝ := z 2

      have hnonneg :
          0 ≤ ∫ t in Set.Ici u,
              (a + b * (t - u) + c * (t - u) ^ 2) ^ 2 * TruncatedNormalMoments.φ t := by
        refine
          MeasureTheory.setIntegral_nonneg (μ := (volume : Measure ℝ)) (s := Set.Ici u)
            measurableSet_Ici ?_
        intro t _ht
        have hs : 0 ≤ (a + b * (t - u) + c * (t - u) ^ 2) ^ 2 := sq_nonneg _
        have hφ : 0 ≤ TruncatedNormalMoments.φ t := by
          have hnum : 0 ≤ Real.exp (-(t ^ 2) / 2) := Real.exp_nonneg _
          have hden : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
          exact div_nonneg hnum hden
        exact mul_nonneg hs hφ

      let f0 : ℝ → ℝ := fun t => (a ^ 2) * ((t - u) ^ 0 * TruncatedNormalMoments.φ t)
      let f1 : ℝ → ℝ := fun t => (2 * a * b) * ((t - u) ^ 1 * TruncatedNormalMoments.φ t)
      let f2 : ℝ → ℝ :=
        fun t => (b ^ 2 + 2 * a * c) * ((t - u) ^ 2 * TruncatedNormalMoments.φ t)
      let f3 : ℝ → ℝ := fun t => (2 * b * c) * ((t - u) ^ 3 * TruncatedNormalMoments.φ t)
      let f4 : ℝ → ℝ := fun t => (c ^ 2) * ((t - u) ^ 4 * TruncatedNormalMoments.φ t)

      have hf0 : IntegrableOn f0 (Set.Ici u) := by
        simpa [f0] using
          (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 0) u).const_mul (a ^ 2)
      have hf1 : IntegrableOn f1 (Set.Ici u) := by
        simpa [f1] using
          (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 1) u).const_mul (2 * a * b)
      have hf2 : IntegrableOn f2 (Set.Ici u) := by
        simpa [f2] using
          (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 2) u).const_mul (b ^ 2 + 2 * a * c)
      have hf3 : IntegrableOn f3 (Set.Ici u) := by
        simpa [f3] using
          (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 3) u).const_mul (2 * b * c)
      have hf4 : IntegrableOn f4 (Set.Ici u) := by
        simpa [f4] using
          (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 4) u).const_mul (c ^ 2)
      have hf01 : IntegrableOn (fun t => f0 t + f1 t) (Set.Ici u) := hf0.add hf1
      have hf012 : IntegrableOn (fun t => f0 t + f1 t + f2 t) (Set.Ici u) := hf01.add hf2
      have hf0123 : IntegrableOn (fun t => f0 t + f1 t + f2 t + f3 t) (Set.Ici u) := hf012.add hf3

      have hI0 : (∫ t in Set.Ici u, f0 t) = a ^ 2 * TruncatedNormalMoments.J 0 u := by
        unfold f0
        rw [TruncatedNormalMoments.J]
        exact
          (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ).restrict (Set.Ici u)) (a ^ 2)
            (fun t : ℝ => (t - u) ^ 0 * TruncatedNormalMoments.φ t))
      have hI1 : (∫ t in Set.Ici u, f1 t) = (2 * a * b) * TruncatedNormalMoments.J 1 u := by
        unfold f1
        rw [TruncatedNormalMoments.J]
        exact
          (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ).restrict (Set.Ici u)) (2 * a * b)
            (fun t : ℝ => (t - u) ^ 1 * TruncatedNormalMoments.φ t))
      have hI2 :
          (∫ t in Set.Ici u, f2 t) = (b ^ 2 + 2 * a * c) * TruncatedNormalMoments.J 2 u := by
        unfold f2
        rw [TruncatedNormalMoments.J]
        exact
          (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ).restrict (Set.Ici u)) (b ^ 2 + 2 * a * c)
            (fun t : ℝ => (t - u) ^ 2 * TruncatedNormalMoments.φ t))
      have hI3 : (∫ t in Set.Ici u, f3 t) = (2 * b * c) * TruncatedNormalMoments.J 3 u := by
        unfold f3
        rw [TruncatedNormalMoments.J]
        exact
          (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ).restrict (Set.Ici u)) (2 * b * c)
            (fun t : ℝ => (t - u) ^ 3 * TruncatedNormalMoments.φ t))
      have hI4 : (∫ t in Set.Ici u, f4 t) = c ^ 2 * TruncatedNormalMoments.J 4 u := by
        unfold f4
        rw [TruncatedNormalMoments.J]
        exact
          (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ).restrict (Set.Ici u)) (c ^ 2)
            (fun t : ℝ => (t - u) ^ 4 * TruncatedNormalMoments.φ t))

      have hInt :
          (∫ t in Set.Ici u,
                (a + b * (t - u) + c * (t - u) ^ 2) ^ 2 * TruncatedNormalMoments.φ t) =
            a ^ 2 * TruncatedNormalMoments.J 0 u +
              (2 * a * b) * TruncatedNormalMoments.J 1 u +
                (b ^ 2 + 2 * a * c) * TruncatedNormalMoments.J 2 u +
                  (2 * b * c) * TruncatedNormalMoments.J 3 u +
                    c ^ 2 * TruncatedNormalMoments.J 4 u := by
        calc
          (∫ t in Set.Ici u,
                (a + b * (t - u) + c * (t - u) ^ 2) ^ 2 * TruncatedNormalMoments.φ t) =
              ∫ t in Set.Ici u, f0 t + f1 t + f2 t + f3 t + f4 t := by
                refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun t _ht => ?_)
                simp [f0, f1, f2, f3, f4]
                ring_nf
          _ =
              (∫ t in Set.Ici u, f0 t + f1 t + f2 t + f3 t) + ∫ t in Set.Ici u, f4 t := by
                simpa using (MeasureTheory.integral_add hf0123 hf4)
          _ =
              ((∫ t in Set.Ici u, f0 t + f1 t + f2 t) + ∫ t in Set.Ici u, f3 t) +
                ∫ t in Set.Ici u, f4 t := by
                have := MeasureTheory.integral_add hf012 hf3
                simpa [add_assoc] using congrArg (fun x => x + ∫ t in Set.Ici u, f4 t) this
          _ =
              (((∫ t in Set.Ici u, f0 t + f1 t) + ∫ t in Set.Ici u, f2 t) +
                ∫ t in Set.Ici u, f3 t) + ∫ t in Set.Ici u, f4 t := by
                have := MeasureTheory.integral_add hf01 hf2
                simpa [add_assoc] using
                  congrArg (fun x => (x + ∫ t in Set.Ici u, f3 t) + ∫ t in Set.Ici u, f4 t) this
          _ =
              ((((∫ t in Set.Ici u, f0 t) + ∫ t in Set.Ici u, f1 t) + ∫ t in Set.Ici u, f2 t) +
                ∫ t in Set.Ici u, f3 t) + ∫ t in Set.Ici u, f4 t := by
                have := MeasureTheory.integral_add hf0 hf1
                simpa [add_assoc] using
                  congrArg (fun x => ((x + ∫ t in Set.Ici u, f2 t) + ∫ t in Set.Ici u, f3 t) +
                    ∫ t in Set.Ici u, f4 t) this
          _ =
              a ^ 2 * TruncatedNormalMoments.J 0 u +
                (2 * a * b) * TruncatedNormalMoments.J 1 u +
                  (b ^ 2 + 2 * a * c) * TruncatedNormalMoments.J 2 u +
                    (2 * b * c) * TruncatedNormalMoments.J 3 u +
                      c ^ 2 * TruncatedNormalMoments.J 4 u := by
                simp [hI0, hI1, hI2, hI3, hI4, add_assoc]

      have hdot :
          star z ⬝ᵥ M.mulVec z =
            a ^ 2 * TruncatedNormalMoments.J 0 u +
              (2 * a * b) * TruncatedNormalMoments.J 1 u +
                (b ^ 2 + 2 * a * c) * TruncatedNormalMoments.J 2 u +
                  (2 * b * c) * TruncatedNormalMoments.J 3 u +
                    c ^ 2 * TruncatedNormalMoments.J 4 u := by
        simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, a, b, c]
        ring_nf

      have : 0 ≤
          a ^ 2 * TruncatedNormalMoments.J 0 u +
            (2 * a * b) * TruncatedNormalMoments.J 1 u +
              (b ^ 2 + 2 * a * c) * TruncatedNormalMoments.J 2 u +
                (2 * b * c) * TruncatedNormalMoments.J 3 u +
                  c ^ 2 * TruncatedNormalMoments.J 4 u := by
        simpa [hInt] using hnonneg
      have hdot' :
          z ⬝ᵥ M.mulVec z =
            a ^ 2 * TruncatedNormalMoments.J 0 u +
              (2 * a * b) * TruncatedNormalMoments.J 1 u +
                (b ^ 2 + 2 * a * c) * TruncatedNormalMoments.J 2 u +
                  (2 * b * c) * TruncatedNormalMoments.J 3 u +
                    c ^ 2 * TruncatedNormalMoments.J 4 u := by
        simpa using hdot
      simpa [hdot'] using this

    have hMpsd : M.PosSemidef :=
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hMherm hMpos

    have hdetM : 0 ≤ M.det := by
      classical
      simpa using (Matrix.PosSemidef.det_nonneg (A := M) hMpsd)

    -- Relate `M.det` to `A.det` via scaling: `M = T • A`.
    have hM_eq_smul : M = T • A := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [M, A, TruncatedNormalMoments.μ, T, hTne, mul_div_cancel₀]
    have hdet_scale : M.det = T ^ 3 * A.det := by
      -- `det (T • A) = T^3 * det A` for `Fin 3`.
      simpa [hM_eq_smul, Fintype.card_fin] using (Matrix.det_smul (A := A) T)

    -- Compute `A.det` using the explicit formulas for `μ₀,…,μ₄`.
    have hμ0 : TruncatedNormalMoments.μ 0 u = 1 := by simpa using TruncatedNormalMoments.μ_zero u
    have hμ1 : TruncatedNormalMoments.μ 1 u = d u := by
      simpa [TruncatedNormalMoments.μ_one, tnm_d_eq_d (u := u)] using rfl
    have hμ2 : TruncatedNormalMoments.μ 2 u = 1 - u * d u := by
      simpa [tnm_d_eq_d (u := u)] using (TruncatedNormalMoments.μ_two u)
    have hμ3 : TruncatedNormalMoments.μ 3 u = (u ^ 2 + 2) * d u - u := by
      simpa [tnm_d_eq_d (u := u)] using (TruncatedNormalMoments.μ_three u)
    have hμ4 :
        TruncatedNormalMoments.μ 4 u = u ^ 2 + 3 - u * (u ^ 2 + 5) * d u := by
      simpa [tnm_d_eq_d (u := u)] using (TruncatedNormalMoments.μ_four u)
    have hdetA : A.det = q (x u) (y u) := by
      -- Expand `det` of a `3×3` matrix and simplify.
      classical
      simp [A, Matrix.det_fin_three, hμ0, hμ1, hμ2, hμ3, hμ4, q, x, y]
      ring_nf

    -- Finish: `0 ≤ M.det = T^3 * A.det = T^3 * q(x,y)`, and `T^3 > 0`.
    have hmul : 0 ≤ T ^ 3 * q (x u) (y u) := by
      -- Rewrite `hdetM` using the scaling and determinant computation.
      have : 0 ≤ T ^ 3 * A.det := by
        simpa [hdet_scale] using hdetM
      simpa [hdetA] using this
    have hTpow : 0 < T ^ 3 := pow_pos hT 3
    exact nonneg_of_mul_nonneg_right hmul hTpow

  lemma constraint_varY {u : ℝ} (hu : 0 ≤ u) : x u + y u < 1 := by
    -- Comes from Var(Y_u) = μ2 - μ1^2 > 0.
    -- Work with truncated-normal moments `J_k` and tail `T`.
    set J₁ : ℝ := TruncatedNormalMoments.J 1 u
    set J₂ : ℝ := TruncatedNormalMoments.J 2 u
    set T : ℝ := TruncatedNormalMoments.tail u
    have hT : 0 < T := TruncatedNormalMoments.tail_pos u
    have hTne : T ≠ 0 := hT.ne'
    -- `c` is the conditional mean `μ₁(u) = J₁/T`.
    set c : ℝ := J₁ / T
    -- Analytic facts: nonnegativity + integrability of the variance integrand.
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici u)
    have hnonneg :
        0 ≤ᵐ[μ] fun x : ℝ => ((x - u) - c) ^ 2 * φ x := by
      refine ae_of_all _ fun x => ?_
      have hsq : 0 ≤ ((x - u) - c) ^ 2 := sq_nonneg _
      have hφx : 0 ≤ φ x := by
        have hnum : 0 < Real.exp (-(x ^ 2) / 2) := Real.exp_pos _
        have hden : 0 < Real.sqrt (2 * Real.pi) := by
          have h2pi : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
          exact Real.sqrt_pos.2 h2pi
        exact le_of_lt (by simpa [φ] using div_pos hnum hden)
      exact mul_nonneg hsq hφx
    have hi0 : IntegrableOn (fun x : ℝ => φ x) (Set.Ici u) := by
      simpa [φ, TruncatedNormalMoments.φ] using
        (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 0) u)
    have hi1 : IntegrableOn (fun x : ℝ => (x - u) * φ x) (Set.Ici u) := by
      simpa [φ, TruncatedNormalMoments.φ, pow_one] using
        (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 1) u)
    have hi2 : IntegrableOn (fun x : ℝ => (x - u) ^ 2 * φ x) (Set.Ici u) := by
      simpa [φ, TruncatedNormalMoments.φ] using
        (TruncatedNormalMoments.integrable_pow_sub_mul_φ (k := 2) u)
    have hint :
        IntegrableOn (fun x : ℝ => ((x - u) - c) ^ 2 * φ x) (Set.Ici u) := by
      -- Expand `((x-u)-c)^2*φ` into a linear combination of `φ`, `(x-u)φ`, `(x-u)^2 φ`.
      have h12 :
          IntegrableOn
              (fun x : ℝ => (x - u) ^ 2 * φ x - (2 * c) * ((x - u) * φ x))
              (Set.Ici u) :=
        hi2.sub (hi1.const_mul (2 * c))
      have h3 :
          IntegrableOn (fun x : ℝ => (c ^ 2) * φ x) (Set.Ici u) :=
        hi0.const_mul (c ^ 2)
      have hsum :
          IntegrableOn
              (fun x : ℝ =>
                ((x - u) ^ 2 * φ x - (2 * c) * ((x - u) * φ x)) + (c ^ 2) * φ x)
              (Set.Ici u) :=
        h12.add h3
      have hfun :
          (fun x : ℝ => ((x - u) - c) ^ 2 * φ x) =
            fun x : ℝ =>
              ((x - u) ^ 2 * φ x - (2 * c) * ((x - u) * φ x)) + (c ^ 2) * φ x := by
        funext x
        ring_nf
      simpa [hfun] using hsum
    -- The support has positive measure: on `Ioc u (u+1)` the integrand vanishes at most on a singleton.
    have hsupp : 0 < μ (Function.support fun x : ℝ => ((x - u) - c) ^ 2 * φ x) := by
      have hsub :
          Set.Ioc u (u + 1) \ {u + c} ⊆
            Function.support (fun x : ℝ => ((x - u) - c) ^ 2 * φ x) := by
        intro x hx
        have hxne : x ≠ u + c := by
          -- membership in a set difference
          have hxnot : x ∉ ({u + c} : Set ℝ) := (Set.mem_diff (x := x)).1 hx |>.2
          simpa [Set.mem_singleton_iff] using hxnot
        have hx0 : (x - u) - c ≠ 0 := by
          intro h
          apply hxne
          linarith
        have hsq : ((x - u) - c) ^ 2 ≠ 0 := pow_ne_zero 2 hx0
        have hφx : φ x ≠ 0 := by
          have hnum : 0 < Real.exp (-(x ^ 2) / 2) := Real.exp_pos _
          have hden : 0 < Real.sqrt (2 * Real.pi) := by
            have h2pi : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
            exact Real.sqrt_pos.2 h2pi
          exact (div_pos hnum hden).ne'
        exact mul_ne_zero hsq hφx
      have hIoc_pos : 0 < μ (Set.Ioc u (u + 1)) := by
        have hsubset : Set.Ioc u (u + 1) ⊆ Set.Ici u := by
          intro x hx
          exact le_of_lt hx.1
        have hab : (0 : ℝ) < u + 1 - u := by linarith
        have hvol : 0 < (volume : Measure ℝ) (Set.Ioc u (u + 1)) := by
          simpa [Real.volume_Ioc] using (ENNReal.ofReal_pos.2 hab)
        simpa [μ, Measure.restrict_apply, measurableSet_Ioc, Set.inter_eq_left.2 hsubset] using hvol
      have hsingleton : μ ({u + c} : Set ℝ) = 0 := by
        have hvol : (volume : Measure ℝ) ({u + c} : Set ℝ) = 0 := by
          simpa using (Real.volume_singleton (u + c))
        have hsubset : ({u + c} ∩ Set.Ici u : Set ℝ) ⊆ ({u + c} : Set ℝ) := by
          intro x hx
          exact hx.1
        have : (volume : Measure ℝ) ({u + c} ∩ Set.Ici u : Set ℝ) = 0 :=
          MeasureTheory.measure_mono_null hsubset hvol
        simpa [μ, Measure.restrict_apply, measurableSet_singleton] using this
      have hdiff :
          μ (Set.Ioc u (u + 1) \ {u + c}) = μ (Set.Ioc u (u + 1)) := by
        simpa using
          (measure_diff_null (μ := μ) (s := Set.Ioc u (u + 1)) (t := ({u + c} : Set ℝ)) hsingleton)
      have : 0 < μ (Set.Ioc u (u + 1) \ {u + c}) := by
        simpa [hdiff] using hIoc_pos
      exact lt_of_lt_of_le this (MeasureTheory.measure_mono hsub)
    -- Therefore the variance integral is strictly positive.
    have hpos_int :
        0 < ∫ x in Set.Ici u, ((x - u) - c) ^ 2 * φ x := by
      have : 0 < ∫ x : ℝ, ((x - u) - c) ^ 2 * φ x ∂μ :=
        (MeasureTheory.integral_pos_iff_support_of_nonneg_ae (μ := μ)
              (f := fun x : ℝ => ((x - u) - c) ^ 2 * φ x) hnonneg hint).2 hsupp
      simpa [μ] using this
    have hIeq :
        (∫ x in Set.Ici u, ((x - u) - c) ^ 2 * φ x) = J₂ - 2 * c * J₁ + c ^ 2 * T := by
      -- Expand and use linearity of the integral.
      have h1 :
          IntegrableOn (fun x : ℝ => (2 * c) * ((x - u) * φ x)) (Set.Ici u) :=
        hi1.const_mul (2 * c)
      have h12 :
          IntegrableOn (fun x : ℝ => (x - u) ^ 2 * φ x - (2 * c) * ((x - u) * φ x)) (Set.Ici u) :=
        hi2.sub h1
      have h3 :
          IntegrableOn (fun x : ℝ => (c ^ 2) * φ x) (Set.Ici u) :=
        hi0.const_mul (c ^ 2)
      calc
        (∫ x in Set.Ici u, ((x - u) - c) ^ 2 * φ x) =
            ∫ x in Set.Ici u,
              ((x - u) ^ 2 * φ x - (2 * c) * ((x - u) * φ x)) + (c ^ 2) * φ x := by
                refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun x _hx => ?_)
                ring_nf
        _ =
            (∫ x in Set.Ici u, (x - u) ^ 2 * φ x - (2 * c) * ((x - u) * φ x)) +
              ∫ x in Set.Ici u, (c ^ 2) * φ x := by
                simpa using (MeasureTheory.integral_add h12 h3)
        _ =
            ((∫ x in Set.Ici u, (x - u) ^ 2 * φ x) -
                ∫ x in Set.Ici u, (2 * c) * ((x - u) * φ x)) +
              ∫ x in Set.Ici u, (c ^ 2) * φ x := by
                rw [MeasureTheory.integral_sub hi2 h1]
        _ = J₂ - 2 * c * J₁ + c ^ 2 * T := by
              simp [J₁, J₂, T, TruncatedNormalMoments.J, TruncatedNormalMoments.tail,
                TruncatedNormalMoments.φ, φ, MeasureTheory.integral_const_mul, sub_eq_add_neg,
                mul_assoc, add_assoc, add_comm, add_left_comm]
    -- Convert strict positivity of the variance integral into `μ₂ - μ₁^2 > 0`.
    have hvar : 0 < TruncatedNormalMoments.μ 2 u - (TruncatedNormalMoments.μ 1 u) ^ 2 := by
      have hpos :
          0 < (J₂ - 2 * c * J₁ + c ^ 2 * T) / T := by
        -- Use the strict positivity of the variance integral and substitute `hIeq`.
        have : 0 < (∫ x in Set.Ici u, ((x - u) - c) ^ 2 * φ x) / T :=
          div_pos (by simpa [hIeq] using hpos_int) hT
        simpa [hIeq] using this
      -- Rewrite the quotient as `μ₂ - μ₁^2` (with `c = J₁/T`).
      have hrewrite :
          (J₂ - 2 * c * J₁ + c ^ 2 * T) / T =
            TruncatedNormalMoments.μ 2 u - (TruncatedNormalMoments.μ 1 u) ^ 2 := by
        -- Here `μ 1 u = J₁/T = c` and `μ 2 u = J₂/T`.
        have ht : TruncatedNormalMoments.tail u ≠ 0 := by
          simpa [T] using hTne
        -- Unfold and clear denominators.
        simp [TruncatedNormalMoments.μ, c, J₁, J₂, T, pow_two, sub_eq_add_neg, div_eq_mul_inv]
        field_simp [ht]
        ring_nf
      simpa [hrewrite] using hpos
    have hμ₁ : TruncatedNormalMoments.μ 1 u = d u := by
      simpa [TruncatedNormalMoments.μ_one, tnm_d_eq_d (u := u)] using rfl
    have hμ₂ : TruncatedNormalMoments.μ 2 u = 1 - u * d u := by
      simpa [tnm_d_eq_d (u := u)] using (TruncatedNormalMoments.μ_two u)
    have : 0 < (1 - u * d u) - (d u) ^ 2 := by
      simpa [hμ₁, hμ₂] using hvar
    -- Rearrange into the desired inequality.
    have : u * d u + (d u) ^ 2 < 1 := by nlinarith
    simpa [x, y] using this

/-! ## Simple bound on `y(u) = d(u)^2` -/

lemma d_le_d0_of_nonneg {u : ℝ} (hu : 0 ≤ u) : d u ≤ d 0 := by
  -- We prove `d' < 0` on `[0,∞)` using `constraint_varY : x u + y u < 1`.
  have hderiv : ∀ t, 0 ≤ t → deriv d t < 0 := by
    intro t ht
    have hE : DifferentiableAt ℝ E t := by
      have hφ : DifferentiableAt ℝ φ t := (hasDerivAt_φ t).differentiableAt
      have hΦbar : DifferentiableAt ℝ Φbar t := (hasDerivAt_Φbar t).differentiableAt
      exact hφ.div hΦbar (Φbar_pos t).ne'
    have hdt : deriv d t = x t + y t - 1 := by
      have hsub :
          deriv d t = deriv E t - deriv (fun s : ℝ => s) t := by
        simpa [d] using
          (deriv_fun_sub (f := E) (g := fun s : ℝ => s) (x := t) hE
            differentiableAt_id)
      have hxy : x t + y t = (E t) ^ 2 - t * E t := by
        simp [x, y, d]
        ring
      calc
        deriv d t = (E t) ^ 2 - t * E t - 1 := by
          rw [hsub, deriv_E (u := t)]
          simp [sub_eq_add_neg]
        _ = x t + y t - 1 := by
          simp [hxy, sub_eq_add_neg]
    have hxylt : x t + y t < 1 := constraint_varY (u := t) ht
    have : x t + y t - 1 < 0 := by nlinarith [hxylt]
    simpa [hdt] using this
  have hcont : ContinuousOn d (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact
      (differentiableAt_of_deriv_ne_zero (hderiv t ht).ne).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn d (Set.Ici (0 : ℝ)) := by
    refine strictAntiOn_of_deriv_neg (D := Set.Ici (0 : ℝ)) (hD := convex_Ici (0 : ℝ)) hcont ?_
    intro t ht
    have ht' : 0 ≤ t := by
      have : 0 < t := by simpa [interior_Ici] using ht
      exact le_of_lt this
    exact hderiv t ht'
  have hu' : u ∈ Set.Ici (0 : ℝ) := hu
  have h0' : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
  by_cases h : u = 0
  · simpa [h]
  · have hlt : 0 < u := lt_of_le_of_ne hu (Ne.symm h)
    exact le_of_lt (hanti h0' hu' hlt)

lemma y_lt_two_thirds_of_nonneg {u : ℝ} (hu : 0 ≤ u) : y u < (2 : ℝ) / 3 := by
  -- From `y(u)=d(u)^2 ≤ d(0)^2 = 2/π < 2/3`.
  have hdle : d u ≤ d 0 := d_le_d0_of_nonneg (u := u) hu
  have habs : |d u| ≤ |d 0| := by
    simpa [abs_of_nonneg (le_of_lt (d_pos u)), abs_of_nonneg (le_of_lt (d_pos 0))] using hdle
  have hsq : (d u) ^ 2 ≤ (d 0) ^ 2 := (sq_le_sq).2 habs
  have hd0 : d 0 = Real.sqrt (2 / Real.pi) := d0_eq_sqrt_two_div_pi
  have hd0sq : (d 0) ^ 2 = 2 / Real.pi := by
    have hnonneg : 0 ≤ (2 / Real.pi : ℝ) := div_nonneg (by norm_num) (le_of_lt Real.pi_pos)
    calc
      (d 0) ^ 2 = (Real.sqrt (2 / Real.pi)) ^ 2 := by simpa [hd0]
      _ = 2 / Real.pi := by simpa using (Real.sq_sqrt hnonneg)
  have hy_le : y u ≤ 2 / Real.pi := by
    simpa [y, hd0sq] using hsq.trans_eq hd0sq
  have hpi : (2 : ℝ) / Real.pi < (2 : ℝ) / 3 := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    have h3 : (0 : ℝ) < 3 := by norm_num
    exact div_lt_div_of_pos_left h2 h3 Real.pi_gt_three
  exact lt_of_le_of_lt hy_le hpi

/-! ## Polynomial negativity lemma (placeholder) -/

lemma F_neg_of_constraints {x y : ℝ}
    (hx : 0 ≤ x) (hy0 : 0 < y) (hy : y < (2 : ℝ) / 3)
    (h₁ : 1 ≤ x + 2 * y) (h₂ : 0 ≤ q x y) (h₃ : x + y < 1) :
    F x y < 0 := by
  -- See `negative_F_bound/FnegLemma.lean` (`Numcheck.F_neg_of_constraints`).
  simpa [F, q, Numcheck.F, Numcheck.q] using
    (Numcheck.F_neg_of_constraints (x := x) (y := y) hx hy0 hy h₁ h₂ h₃)

lemma F_neg_of_nonneg {u : ℝ} (hu : 0 ≤ u) : F (x u) (y u) < 0 := by
  have hx : 0 ≤ x u := by
    have hd : 0 ≤ d u := le_of_lt (d_pos u)
    exact mul_nonneg hu hd
  have hy0 : 0 < y u := by
    -- y(u) = d(u)^2 and d(u) > 0.
    simpa [y] using (sq_pos_of_pos (d_pos u))
  have hy : y u < (2 : ℝ) / 3 := y_lt_two_thirds_of_nonneg (u := u) hu
  have h₁ : 1 ≤ x u + 2 * y u := constraint_detM1 (u := u) hu
  have h₂ : 0 ≤ q (x u) (y u) := constraint_detM2 (u := u) hu
  have h₃ : x u + y u < 1 := constraint_varY (u := u) hu
  simpa using (F_neg_of_constraints (x := x u) (y := y u) hx hy0 hy h₁ h₂ h₃)

/-! ## Derivative sign and strict monotonicity -/

lemma g_deriv_eq (u : ℝ) : deriv g u = 2 * (E u) ^ 2 * H u := by
  -- Differentiate g and simplify into the form `2 E(u)^2 H(u)`.
  have hE : DifferentiableAt ℝ E u := by
    have hφ : DifferentiableAt ℝ φ u := (hasDerivAt_φ u).differentiableAt
    have hΦbar : DifferentiableAt ℝ Φbar u := (hasDerivAt_Φbar u).differentiableAt
    exact hφ.div hΦbar (Φbar_pos u).ne'

  set A : ℝ → ℝ := fun t => (E t) ^ 2
  set B : ℝ → ℝ := fun t => 3 * (E t) ^ 2 - 4 * t * E t + t ^ 2 - 2
  have hA : DifferentiableAt ℝ A u := by
    simpa [A] using (hE.pow 2)
  have hB : DifferentiableAt ℝ B u := by
    -- `B` is built from `E` and polynomials by ring operations.
    fun_prop (disch := assumption)

  have hAderiv : deriv A u = 2 * E u * deriv E u := by
    simpa [A] using (deriv_fun_pow (f := E) (x := u) hE 2)

  have hmul_deriv : deriv (fun t : ℝ => t * E t) u = E u + u * deriv E u := by
    simpa using
      (deriv_fun_mul (c := fun t : ℝ => t) (d := E) (x := u) differentiableAt_id hE)

  have hBderiv : deriv B u = 6 * E u * deriv E u - 4 * (E u + u * deriv E u) + 2 * u := by
    -- Expand `B` as `((3*(E t)^2 - 4*t*E t) + t^2) - 2` and differentiate termwise.
    have h1 : DifferentiableAt ℝ (fun t => 3 * (E t) ^ 2) u := by
      -- constant multiple of `A`
      simpa [A] using (differentiableAt_const (c := (3 : ℝ))).mul (hE.pow 2)
    have h2 : DifferentiableAt ℝ (fun t => 4 * t * E t) u := by
      have : DifferentiableAt ℝ (fun t => (4 : ℝ) * (t * E t)) u :=
        (differentiableAt_const (c := (4 : ℝ))).mul (differentiableAt_id.mul hE)
      simpa [mul_assoc] using this
    have h12 : DifferentiableAt ℝ (fun t => 3 * (E t) ^ 2 - 4 * t * E t) u := h1.sub h2
    have h3 : DifferentiableAt ℝ (fun t : ℝ => t ^ 2) u := by
      simpa using (differentiableAt_id.pow 2)
    have h123 :
        DifferentiableAt ℝ (fun t => (3 * (E t) ^ 2 - 4 * t * E t) + t ^ 2) u := h12.add h3
    have hconst : DifferentiableAt ℝ (fun _ : ℝ => (2 : ℝ)) u := differentiableAt_const (c := (2 : ℝ))
    calc
      deriv B u =
          deriv (fun t => (3 * (E t) ^ 2 - 4 * t * E t + t ^ 2) - (fun _ : ℝ => (2 : ℝ)) t) u := by
            simp [B]
      _ =
          deriv (fun t => (3 * (E t) ^ 2 - 4 * t * E t + t ^ 2)) u -
            deriv (fun _ : ℝ => (2 : ℝ)) u := by
            simpa using
              (deriv_fun_sub (f := fun t => (3 * (E t) ^ 2 - 4 * t * E t + t ^ 2))
                (g := fun _ : ℝ => (2 : ℝ)) (x := u)
                (by
                  -- differentiability of the left term
                  simpa [sub_eq_add_neg, add_assoc] using h123)
                hconst)
      _ = deriv (fun t => (3 * (E t) ^ 2 - 4 * t * E t + t ^ 2)) u := by
            simp [deriv_const]
      _ = deriv (fun t => (3 * (E t) ^ 2 - 4 * t * E t) + t ^ 2) u := by
            simp [sub_eq_add_neg, add_assoc]
      _ =
          deriv (fun t => 3 * (E t) ^ 2 - 4 * t * E t) u +
            deriv (fun t : ℝ => t ^ 2) u := by
            simpa using (deriv_add h12 h3)
      _ =
          (deriv (fun t => 3 * (E t) ^ 2) u - deriv (fun t => 4 * t * E t) u) +
            deriv (fun t : ℝ => t ^ 2) u := by
            simpa using (deriv_fun_sub h1 h2)
      _ =
          (3 * (2 * E u * deriv E u) - 4 * (E u + u * deriv E u)) +
            (2 * u) := by
            -- compute each derivative and simplify
            have hder1 : deriv (fun t => 3 * (E t) ^ 2) u = 3 * (2 * E u * deriv E u) := by
              calc
                deriv (fun t => 3 * (E t) ^ 2) u = 3 * deriv A u := by
                  simpa [A] using (deriv_const_mul (c := (3 : ℝ)) (d := A) (x := u) hA)
                _ = 3 * (2 * E u * deriv E u) := by simp [hAderiv]
            have hder2 : deriv (fun t => 4 * t * E t) u = 4 * (E u + u * deriv E u) := by
              calc
                deriv (fun t => 4 * t * E t) u = (4 : ℝ) * deriv (fun t : ℝ => t * E t) u := by
                  have hmul : DifferentiableAt ℝ (fun t : ℝ => t * E t) u := differentiableAt_id.mul hE
                  simpa [mul_assoc] using
                    (deriv_const_mul (c := (4 : ℝ)) (d := fun t : ℝ => t * E t) (x := u) hmul)
                _ = 4 * (E u + u * deriv E u) := by simp [hmul_deriv]
            have hder3 : deriv (fun t : ℝ => t ^ 2) u = 2 * u := by
              simpa using (deriv_pow_field (𝕜 := ℝ) (x := u) (n := 2))
            simp [hder1, hder2, hder3, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      _ = 6 * E u * deriv E u - 4 * (E u + u * deriv E u) + 2 * u := by ring

  -- Put the pieces together and simplify using `deriv_E` and `d = E - u`.
  calc
    deriv g u =
        deriv A u * B u + A u * deriv B u := by
          simpa [g, A, B] using (deriv_fun_mul (c := A) (d := B) (x := u) hA hB)
    _ =
        (2 * E u * deriv E u) * (3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2) +
          (E u) ^ 2 * (6 * E u * deriv E u - 4 * (E u + u * deriv E u) + 2 * u) := by
          simp [A, B, hAderiv, hBderiv]
    _ = 2 * (E u) ^ 2 * H u := by
          -- eliminate `deriv E u` and close by ring normalization
          rw [deriv_E (u := u)]
          simp [H, d]
          ring_nf

lemma H_neg_of_nonneg {u : ℝ} (hu : 0 ≤ u) : H u < 0 := by
  have hF : F (x u) (y u) < 0 := F_neg_of_nonneg (u := u) hu
  exact H_neg_of_F_neg (u := u) (hd := d_pos u) hF

lemma deriv_g_neg_of_nonneg {u : ℝ} (hu : 0 ≤ u) : deriv g u < 0 := by
  have hH : H u < 0 := H_neg_of_nonneg (u := u) hu
  have hE : 0 < 2 * (E u) ^ 2 := by
    have : 0 < (E u) ^ 2 := sq_pos_of_pos (E_pos u)
    nlinarith
  -- `deriv g u = (2*(E u)^2) * H u` with positive left factor and negative H.
  simpa [g_deriv_eq (u := u), mul_assoc] using (mul_neg_of_pos_of_neg hE hH)

lemma strictAntiOn_Ici_of_deriv_neg
    (hderiv : ∀ u, 0 ≤ u → deriv g u < 0) :
    StrictAntiOn g (Set.Ici (0 : ℝ)) := by
  -- Standard calculus lemma: derivative strictly negative on an interval implies
  -- strict decrease on that interval.
  have hcont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    intro u hu
    exact
      (differentiableAt_of_deriv_ne_zero (hderiv u hu).ne).continuousAt.continuousWithinAt
  refine
    strictAntiOn_of_deriv_neg (D := Set.Ici (0 : ℝ)) (hD := convex_Ici (0 : ℝ)) hcont ?_
  intro u hu
  have hu' : 0 ≤ u := by
    have : 0 < u := by simpa [interior_Ici] using hu
    exact le_of_lt this
  exact hderiv u hu'

theorem g_strictAntiOn_Ici : StrictAntiOn g (Set.Ici (0 : ℝ)) := by
  exact strictAntiOn_Ici_of_deriv_neg (fun u hu => deriv_g_neg_of_nonneg (u := u) hu)

theorem g_le_g0_of_nonneg {u : ℝ} (hu : 0 ≤ u) : g u ≤ g 0 := by
  -- Monotone consequence of strict decrease on `[0,∞)`.
  have hanti := g_strictAntiOn_Ici
  have hu' : u ∈ Set.Ici (0 : ℝ) := hu
  have h0' : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
  by_cases h : u = 0
  · simpa [h]
  · have hlt : 0 < u := lt_of_le_of_ne hu (Ne.symm h)
    exact le_of_lt (hanti h0' hu' hlt)

/-! ## Value at 0 (placeholder) -/

lemma g0_eq : g 0 = 12 / Real.pi ^ 2 - 4 / Real.pi := by
  -- In `main.tex`: E(0)=√(2/π), hence g(0)=E(0)^2(3E(0)^2-2), then compute.
  have hE0 : E 0 = Real.sqrt (2 / Real.pi) := by
    simpa [d] using d0_eq_sqrt_two_div_pi
  have hE0sq : (E 0) ^ 2 = 2 / Real.pi := by
    have hnonneg : 0 ≤ (2 / Real.pi : ℝ) := div_nonneg (by norm_num) (le_of_lt Real.pi_pos)
    calc
      (E 0) ^ 2 = (Real.sqrt (2 / Real.pi)) ^ 2 := by simpa [hE0]
      _ = 2 / Real.pi := by simpa using (Real.sq_sqrt hnonneg)
  calc
    g 0 = (E 0) ^ 2 * (3 * (E 0) ^ 2 - 2) := by simp [g]
    _ = (2 / Real.pi) * (3 * (2 / Real.pi) - 2) := by simp [hE0sq]
    _ = 12 / Real.pi ^ 2 - 4 / Real.pi := by
          have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
          field_simp [hpi]
          ring

end
end DecreasingG
