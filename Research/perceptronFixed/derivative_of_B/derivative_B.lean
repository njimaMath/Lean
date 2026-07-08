import Mathlib

/-!
Blueprint scaffold: proof that `B'(t) = 𝔼[g(U_t)]`.

All intermediate lemmas are initially stated with placeholders.

Notes.
- The file is intentionally modular: you can replace the probability space and the
  definition of the standard normal law with whatever you use in your project.
- The analytic domination step needed for differentiating under the expectation is
  isolated in a single lemma.
- The Gaussian integration by parts is an explicit hypothesis.
-/

open scoped Real
open scoped MeasureTheory
open scoped ENNReal
open scoped NNReal
open MeasureTheory

namespace MillsBlueprint

noncomputable section

namespace Proof

/-! Settings -/

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/- A real-valued random variable, intended to be standard normal. -/
variable (Z : Ω → ℝ) (κ : ℝ)

/-- Expectation with respect to `P`.

We use the Bochner integral on `ℝ`.
-/
def 𝔼 (P : Measure Ω) (f : Ω → ℝ) : ℝ := (∫ ω, f ω ∂P)

/-! Definitions (matching main.tex) -/

/-- Standard normal density `φ(u) = (1/√(2π)) exp(-u^2/2)`. -/
def φ (u : ℝ) : ℝ := (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(u ^ 2) / 2)

/-- Standard normal CDF `Φ(u) = ∫_{-∞}^u φ(s) ds`.
-/
def Φ (u : ℝ) : ℝ := ∫ x in Set.Iic u, φ x

/-- Standard normal upper tail `Φ̄(u) = 1 - Φ(u)`. -/
def Φbar (u : ℝ) : ℝ := 1 - Φ u

/-- Inverse Mills ratio `E(u) = φ(u) / Φ̄(u)`. -/
def E (u : ℝ) : ℝ := φ u / Φbar u

/-- `h(u) = E(u)^2`. -/
def h (u : ℝ) : ℝ := (E u) ^ 2

/-- `g(u) = E(u)^2 (3E(u)^2 - 4uE(u) + u^2 - 2)`. -/
def g (u : ℝ) : ℝ := (E u) ^ 2 * (3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2)

/-- Random change of variables: `U_t = (κ - √t Z) / √(1 - t)`. -/
def U (t : ℝ) (ω : Ω) : ℝ := (κ - Real.sqrt t * Z ω) / Real.sqrt (1 - t)

/-- `B(t) = (1 - t) * 𝔼[ E(U_t)^2 ]`. -/
def B (t : ℝ) : ℝ := (1 - t) * 𝔼 (P := P) (fun ω => (E (U (κ := κ) (Z := Z) t ω)) ^ 2)

/-! Facts A: differentiation formulas for the inverse Mills ratio -/

/-!
To keep this blueprint file self-contained and modular, we prove the basic
calculus facts about `φ` and `Φbar` from the given definitions, and we treat the
non-vanishing of `Φbar` as a hypothesis (this is true for the standard normal).
-/

private lemma integrable_φ : Integrable φ := by
  have h : Integrable (fun x : ℝ => rexp (-((1 / 2 : ℝ) * x ^ 2))) := by
    simpa using (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num))
  have h' : Integrable (fun x : ℝ => rexp (-(x ^ 2) / 2)) := by
    have :
        (fun x : ℝ => rexp (-(x ^ 2) / 2)) =
          (fun x : ℝ => rexp (-((1 / 2 : ℝ) * x ^ 2))) := by
      funext x
      ring_nf
    simpa [this] using h
  change Integrable (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(x ^ 2) / 2))
  exact h'.const_mul (1 / Real.sqrt (2 * Real.pi))

private lemma continuous_φ : Continuous φ := by
  change Continuous (fun u : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(u ^ 2) / 2))
  have h_inner : Continuous (fun u : ℝ => -(u ^ 2) / (2 : ℝ)) := by
    have h_pow : Continuous (fun u : ℝ => u ^ 2) := by
      simpa using (continuous_pow 2 : Continuous fun u : ℝ => u ^ 2)
    simpa [div_eq_mul_inv, mul_assoc] using (h_pow.neg.div_const (2 : ℝ))
  have h_exp : Continuous (fun u : ℝ => rexp (-(u ^ 2) / (2 : ℝ))) := h_inner.rexp
  have h_const : Continuous (fun _u : ℝ => (1 / Real.sqrt (2 * Real.pi))) := continuous_const
  simpa [div_eq_mul_inv, mul_assoc] using h_const.mul h_exp

private lemma φ_pos (u : ℝ) : 0 < φ u := by
  unfold φ
  have hconst : 0 < (1 / Real.sqrt (2 * Real.pi) : ℝ) := by
    have hpi : (0 : ℝ) < Real.pi := by simpa using Real.pi_pos
    have h2pi : (0 : ℝ) < (2 * Real.pi : ℝ) := by nlinarith
    have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 h2pi
    simpa [one_div] using inv_pos.2 hsqrt
  have hexp : 0 < Real.exp (-(u ^ 2) / 2) := Real.exp_pos _
  have : 0 < (1 / Real.sqrt (2 * Real.pi) : ℝ) * Real.exp (-(u ^ 2) / 2) :=
    mul_pos hconst hexp
  simpa using this

private lemma φ_eq_gaussianPDFReal : φ = ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) := by
  funext x
  simp [φ, ProbabilityTheory.gaussianPDFReal]

private lemma integral_φ_eq_one : (∫ x : ℝ, φ x) = 1 := by
  have hv : (1 : ℝ≥0) ≠ 0 := by simp
  -- `integral_gaussianPDFReal_eq_one` is for the Lebesgue integral on `ℝ`.
  simpa [φ_eq_gaussianPDFReal] using
    (ProbabilityTheory.integral_gaussianPDFReal_eq_one (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)

lemma Φbar_ne_zero : ∀ u : ℝ, Φbar u ≠ 0 := by
  intro u
  have hab : u < u + 1 := by linarith
  have hfi : IntervalIntegrable φ volume u (u + 1) := by
    simpa using (integrable_φ.intervalIntegrable)
  have hpos_interval :
      0 < ∫ x : ℝ in u..(u + 1), φ x := by
    exact
      intervalIntegral.intervalIntegral_pos_of_pos
        (f := φ) (a := u) (b := u + 1) hfi (fun x => φ_pos x) hab
  have hIoc :
      (∫ x in Set.Ioc u (u + 1), φ x) = ∫ x : ℝ in u..(u + 1), φ x := by
    simpa using
      (intervalIntegral.integral_of_le (μ := volume) (f := φ) (a := u) (b := u + 1) hab.le).symm
  have hpos_Ioc : 0 < ∫ x in Set.Ioc u (u + 1), φ x := by
    simpa [hIoc] using hpos_interval
  have hset : (Set.Iic u ∪ Set.Ioi u : Set ℝ) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      have : x ≤ u ∨ u < x := le_or_gt x u
      simpa [Set.mem_Iic, Set.mem_Ioi] using this
  have hdis : Disjoint (Set.Iic u) (Set.Ioi u) := by
    refine Set.disjoint_left.2 ?_
    intro x hx1 hx2
    have hx2' : u < x := by simpa [Set.mem_Ioi] using hx2
    exact (not_lt_of_ge hx1) hx2'
  have hsplit :
      (∫ x : ℝ, φ x) = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
    have hunion :
        (∫ x in (Set.Iic u ∪ Set.Ioi u), φ x) =
          (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
      simpa using
        (setIntegral_union (μ := (volume : Measure ℝ)) (f := φ) hdis measurableSet_Ioi
          (integrable_φ.integrableOn) (integrable_φ.integrableOn))
    calc
      (∫ x : ℝ, φ x) = ∫ x in (Set.Iic u ∪ Set.Ioi u), φ x := by
        simp [hset]
      _ = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := hunion
  have htail : (∫ x in Set.Ioi u, φ x) = Φbar u := by
    dsimp [Φbar, Φ] at *
    linarith [hsplit, integral_φ_eq_one]
  have hmono : (∫ x in Set.Ioc u (u + 1), φ x) ≤ ∫ x in Set.Ioi u, φ x := by
    have hfi_on : IntegrableOn φ (Set.Ioi u) (volume : Measure ℝ) := integrable_φ.integrableOn
    have h_nonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi u)] φ := by
      refine ae_of_all _ (fun x => (φ_pos x).le)
    have hst : (Set.Ioc u (u + 1) : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Ioi u := by
      refine ae_of_all _ (fun x hx => hx.1)
    exact setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := φ)
      (s := Set.Ioc u (u + 1)) (t := Set.Ioi u) hfi_on h_nonneg hst
  have : 0 < ∫ x in Set.Ioi u, φ x := lt_of_lt_of_le hpos_Ioc hmono
  have hΦbar_pos : 0 < Φbar u := by simpa [htail] using this
  exact ne_of_gt hΦbar_pos

private lemma Φ_eq_const_add_intervalIntegral (u : ℝ) :
    Φ u = (∫ x in Set.Iic (0 : ℝ), φ x) + ∫ x in (0 : ℝ)..u, φ x := by
  classical
  by_cases hu : 0 ≤ u
  ·
    have hset : Set.Iic u = Set.Iic (0 : ℝ) ∪ Set.Ioc (0 : ℝ) u := by
      ext x
      constructor
      · intro hx
        have hx0 : x ≤ 0 ∨ 0 < x := le_or_lt x 0
        cases hx0 with
        | inl hx0 => exact Or.inl hx0
        | inr hx0 => exact Or.inr ⟨hx0, hx⟩
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
        (setIntegral_union (μ := volume) (f := φ) hdis measurableSet_Ioc
          (integrable_φ.integrableOn) (integrable_φ.integrableOn))
    have hint : (∫ x in Set.Ioc (0 : ℝ) u, φ x) = ∫ x in (0 : ℝ)..u, φ x := by
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
        (setIntegral_union (μ := volume) (f := φ) hdis measurableSet_Ioc
          (integrable_φ.integrableOn) (integrable_φ.integrableOn))
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
  -- `u ↦ ∫ x in 0..u, φ x` has derivative `φ u` at `u` when `φ` is continuous.
  have hInt : HasDerivAt (fun s : ℝ => ∫ x : ℝ in (0 : ℝ)..s, φ x) (φ u) u :=
    intervalIntegral.integral_hasDerivAt_right
      (hf := (continuous_φ.intervalIntegrable _ _))
      (hmeas := (continuous_φ.stronglyMeasurableAtFilter _ _))
      (hb := (continuous_φ.continuousAt))
  -- Add the constant.
  have hsum : HasDerivAt (fun s : ℝ => C + ∫ x : ℝ in (0 : ℝ)..s, φ x) (φ u) u := by
    simpa using hInt.const_add C
  simpa [hfun] using hsum

lemma deriv_φ (u : ℝ) : deriv φ u = -u * φ u := by
  -- Compute the derivative of `φ(u) = c * exp(-(u^2)/2)`.
  have h_inner : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-u) u := by
    have h_pow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
      simpa using (hasDerivAt_pow (n := 2) (x := u))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (h_pow.neg.div_const (2 : ℝ))
  have h_exp :
      HasDerivAt (fun x : ℝ => rexp (-(x ^ 2) / 2)) (-(u * rexp (-(u ^ 2) / 2))) u := by
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (x := (-(u ^ 2) / 2))).comp u h_inner
  have h_mul :
      HasDerivAt
        (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(x ^ 2) / 2))
        ((1 / Real.sqrt (2 * Real.pi)) * (-(u * rexp (-(u ^ 2) / 2)))) u :=
    h_exp.const_mul (1 / Real.sqrt (2 * Real.pi))
  -- Unfold `φ` in the goal (both occurrences) and finish by algebra.
  change
      deriv (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(x ^ 2) / 2)) u =
        -u * ((1 / Real.sqrt (2 * Real.pi)) * rexp (-(u ^ 2) / 2))
  have hderiv :
      deriv (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(x ^ 2) / 2)) u =
        (1 / Real.sqrt (2 * Real.pi)) * (-(u * rexp (-(u ^ 2) / 2))) :=
    h_mul.deriv
  rw [hderiv]
  ring_nf

lemma deriv_Φbar (u : ℝ) : deriv Φbar u = -φ u := by
  -- `Φbar = 1 - Φ`, and `Φ' = φ` by FTC.
  have hΦ : HasDerivAt Φ (φ u) u := hasDerivAt_Φ (u := u)
  have hΦbar : HasDerivAt Φbar (-φ u) u := by
    -- `1 - Φ` has derivative `-Φ'`.
    simpa [Φbar] using hΦ.const_sub (1 : ℝ)
  exact hΦbar.deriv

lemma deriv_E (u : ℝ) :
    deriv E u = (E u) ^ 2 - u * E u := by
  -- Differentiate `E = φ / Φbar` using the quotient rule.
  have hφ : DifferentiableAt ℝ φ u := by
    -- Unfold the definition and use `fun_prop`.
    change
      DifferentiableAt ℝ
        (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(x ^ 2) / 2)) u
    fun_prop
  have hΦbar : DifferentiableAt ℝ Φbar u := by
    -- From the existence of the derivative of `Φbar`.
    exact (hasDerivAt_Φ (u := u)).const_sub (1 : ℝ) |>.differentiableAt
  have h_div :
      deriv E u =
        (deriv φ u * Φbar u - φ u * deriv Φbar u) / (Φbar u) ^ 2 := by
    simpa [E] using (deriv_div hφ hΦbar (Φbar_ne_zero u))
  -- Substitute the known derivatives and simplify.
  rw [h_div, deriv_φ (u := u), deriv_Φbar (u := u)]
  field_simp [E, Φbar_ne_zero u]
  simp [E, div_eq_mul_inv, pow_two, Φbar_ne_zero u, mul_assoc, mul_left_comm, mul_comm]
  field_simp [Φbar_ne_zero u]
  ring

lemma differentiableAt_E (u : ℝ) :
    DifferentiableAt ℝ E u := by
  have hφ : DifferentiableAt ℝ φ u := by
    change
      DifferentiableAt ℝ
        (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(x ^ 2) / 2)) u
    fun_prop
  have hΦbar : DifferentiableAt ℝ Φbar u :=
    ((hasDerivAt_Φ (u := u)).const_sub (1 : ℝ)).differentiableAt
  simpa [E] using (hφ.div hΦbar (Φbar_ne_zero u))

lemma deriv2_E (u : ℝ) :
    deriv (fun x => deriv E x) u =
    2 * (E u) * (deriv E u) - (E u) - u * (deriv E u) := by
  -- Differentiate the identity `E' = E^2 - uE`.
  have hfun : (fun x => deriv E x) = fun x => (E x) ^ 2 - x * E x := by
    funext x
    simpa using (deriv_E (u := x))
  have hE : DifferentiableAt ℝ E u := by
    have hφ : DifferentiableAt ℝ φ u := by
      change
        DifferentiableAt ℝ
          (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(x ^ 2) / 2)) u
      fun_prop
    have hΦbar : DifferentiableAt ℝ Φbar u :=
      ((hasDerivAt_Φ (u := u)).const_sub (1 : ℝ)).differentiableAt
    simpa [E] using (hφ.div hΦbar (Φbar_ne_zero u))
  -- Rewrite the left-hand side using `hfun`, then compute the derivative of the RHS.
  simp [hfun, pow_two, deriv_sub, deriv_mul, hE, differentiableAt_id, mul_assoc, mul_left_comm,
      mul_comm]
  ring_nf

/-!
## Simple analytic lemmas for `Φbar` and `φ`

These are used later to prove a Mills-type growth bound for `E`, which in turn
discharges the bundled `IntegrabilityAssumptions`.
-/

lemma Φbar_eq_integral_Ioi (u : ℝ) : Φbar u = ∫ x in Set.Ioi u, φ x := by
  have hset : (Set.Iic u ∪ Set.Ioi u : Set ℝ) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      have : x ≤ u ∨ u < x := le_or_gt x u
      simpa [Set.mem_Iic, Set.mem_Ioi] using this
  have hdis : Disjoint (Set.Iic u) (Set.Ioi u) := by
    refine Set.disjoint_left.2 ?_
    intro x hx1 hx2
    exact (not_lt_of_ge hx1) (by simpa [Set.mem_Ioi] using hx2)
  have hsplit :
      (∫ x : ℝ, φ x) = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
    have hunion :
        (∫ x in (Set.Iic u ∪ Set.Ioi u), φ x) =
          (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
      simpa using
        (setIntegral_union (μ := (volume : Measure ℝ)) (f := φ) hdis measurableSet_Ioi
          (integrable_φ.integrableOn) (integrable_φ.integrableOn))
    calc
      (∫ x : ℝ, φ x) = ∫ x in (Set.Iic u ∪ Set.Ioi u), φ x := by
        simp [hset]
      _ = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := hunion
  -- Solve for the tail using `∫ φ = 1`.
  have htail : (∫ x in Set.Ioi u, φ x) = Φbar u := by
    dsimp [Φbar, Φ] at *
    linarith [hsplit, integral_φ_eq_one]
  simpa using htail.symm

lemma Φbar_pos (u : ℝ) : 0 < Φbar u := by
  have hab : u < u + 1 := by linarith
  have hfi : IntervalIntegrable φ volume u (u + 1) := by
    simpa using (integrable_φ.intervalIntegrable)
  have hpos_interval :
      0 < ∫ x : ℝ in u..(u + 1), φ x := by
    exact
      intervalIntegral.intervalIntegral_pos_of_pos
        (f := φ) (a := u) (b := u + 1) hfi (fun x => φ_pos x) hab
  have hIoc :
      (∫ x in Set.Ioc u (u + 1), φ x) = ∫ x : ℝ in u..(u + 1), φ x := by
    simpa using
      (intervalIntegral.integral_of_le (μ := volume) (f := φ) (a := u) (b := u + 1) hab.le).symm
  have hpos_Ioc : 0 < ∫ x in Set.Ioc u (u + 1), φ x := by
    simpa [hIoc] using hpos_interval
  have hmono :
      (∫ x in Set.Ioc u (u + 1), φ x) ≤ ∫ x in Set.Ioi u, φ x := by
    have hfi_on : IntegrableOn φ (Set.Ioi u) (volume : Measure ℝ) :=
      integrable_φ.integrableOn
    have h_nonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi u)] φ := by
      refine ae_of_all _ (fun x => (φ_pos x).le)
    have hst : (Set.Ioc u (u + 1) : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Ioi u := by
      refine ae_of_all _ (fun x hx => hx.1)
    exact setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := φ)
      (s := Set.Ioc u (u + 1)) (t := Set.Ioi u) hfi_on h_nonneg hst
  have : 0 < ∫ x in Set.Ioi u, φ x := lt_of_lt_of_le hpos_Ioc hmono
  simpa [Φbar_eq_integral_Ioi (u := u)] using this

lemma Φbar_antitone : Antitone Φbar := by
  intro u v huv
  -- Use the tail integral representation and set inclusion.
  rw [Φbar_eq_integral_Ioi (u := u), Φbar_eq_integral_Ioi (u := v)]
  have hfi_on : IntegrableOn φ (Set.Ioi u) (volume : Measure ℝ) :=
    integrable_φ.integrableOn
  have h_nonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi u)] φ := by
    refine ae_of_all _ (fun x => (φ_pos x).le)
  have hst : (Set.Ioi v : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Ioi u := by
    refine ae_of_all _ (fun x hx => ?_)
    have : v < x := by simpa [Set.mem_Ioi] using hx
    exact lt_of_le_of_lt huv this
  exact setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := φ)
    (s := Set.Ioi v) (t := Set.Ioi u) hfi_on h_nonneg hst

lemma φ_le_one (u : ℝ) : φ u ≤ 1 := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    simpa using (Real.one_le_sqrt.2 h2pi)
  have hconst : (1 / Real.sqrt (2 * Real.pi) : ℝ) ≤ 1 := by
    have : (1 : ℝ) / Real.sqrt (2 * Real.pi) ≤ (1 : ℝ) / (1 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hsqrt
    simpa using this
  have hexp : Real.exp (-(u ^ 2) / 2) ≤ 1 := by
    have : (-(u ^ 2) / 2 : ℝ) ≤ 0 := by
      have : 0 ≤ (u ^ 2 : ℝ) := by nlinarith
      nlinarith
    simpa [Real.exp_le_one_iff] using this
  unfold φ
  have hnonneg : 0 ≤ (Real.exp (-(u ^ 2) / 2) : ℝ) := Real.exp_nonneg _
  have hmul := mul_le_mul hconst hexp hnonneg (by linarith)
  simpa [one_mul] using hmul
lemma E_le_inv_Φbar_one_of_le_one {u : ℝ} (hu : u ≤ 1) :
    E u ≤ (Φbar 1)⁻¹ := by
  have hΦ : Φbar 1 ≤ Φbar u := Φbar_antitone hu
  have hΦpos1 : 0 < Φbar 1 := Φbar_pos (u := (1 : ℝ))
  have hinv : (Φbar u)⁻¹ ≤ (Φbar 1)⁻¹ := by
    have : (1 : ℝ) / Φbar u ≤ (1 : ℝ) / Φbar 1 :=
      one_div_le_one_div_of_le hΦpos1 hΦ
    simpa [one_div] using this
  have hΦposu : 0 < Φbar u := Φbar_pos (u := u)
  have hΦinv_nonneg : 0 ≤ (Φbar u)⁻¹ := inv_nonneg.2 hΦposu.le
  calc
    E u = φ u * (Φbar u)⁻¹ := by simp [E, div_eq_mul_inv]
    _ ≤ 1 * (Φbar u)⁻¹ := by
      exact mul_le_mul_of_nonneg_right (φ_le_one (u := u)) hΦinv_nonneg
    _ = (Φbar u)⁻¹ := by simp
    _ ≤ (Φbar 1)⁻¹ := hinv

lemma tendsto_neg_sq_div_two_atTop_atBot :
    Filter.Tendsto (fun x : ℝ => -(x ^ 2) / 2) Filter.atTop Filter.atBot := by
  refine (Filter.tendsto_atBot.2 ?_)
  intro a
  by_cases ha : a < 0
  · refine (Filter.eventually_atTop.2 ?_)
    have hnonneg : 0 ≤ -(2 * a) := by nlinarith [ha.le]
    refine ⟨Real.sqrt (-(2 * a)), ?_⟩
    intro x hx
    have hx0 : 0 ≤ x := le_trans (Real.sqrt_nonneg _) hx
    have hsq : -(2 * a) ≤ x ^ 2 := by
      have hxabs : |Real.sqrt (-(2 * a))| ≤ |x| := by
        simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hx0] using hx
      have : (Real.sqrt (-(2 * a))) ^ 2 ≤ x ^ 2 := (sq_le_sq).2 hxabs
      simpa [Real.sq_sqrt hnonneg] using this
    have hmul :
        (-(1 / 2 : ℝ)) * (x ^ 2) ≤ (-(1 / 2 : ℝ)) * (-(2 * a)) :=
      mul_le_mul_of_nonpos_left hsq (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
    nlinarith [hmul]
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hx2 : 0 ≤ (x ^ 2 : ℝ) := sq_nonneg x
    have : -(x ^ 2) / 2 ≤ 0 := by nlinarith [hx2]
    exact le_trans this ha0

lemma tendsto_φ_atTop_zero :
    Filter.Tendsto φ Filter.atTop (nhds (0 : ℝ)) := by
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2))
        Filter.atTop (nhds (0 : ℝ)) :=
    (Real.tendsto_exp_atBot.comp tendsto_neg_sq_div_two_atTop_atBot)
  have hconst :
      Filter.Tendsto (fun _x : ℝ => (1 / Real.sqrt (2 * Real.pi) : ℝ))
        Filter.atTop (nhds (1 / Real.sqrt (2 * Real.pi) : ℝ)) :=
    tendsto_const_nhds
  show Filter.Tendsto (fun x : ℝ => φ x) Filter.atTop (nhds (0 : ℝ))
  simpa [φ, mul_assoc] using hconst.mul hexp

lemma Φbar_eq_phi_div_sub_integral {u : ℝ} (hu : 0 < u) :
    Φbar u = φ u / u - ∫ x in Set.Ioi u, φ x / x ^ 2 := by
  have hφderiv : ∀ x, HasDerivAt φ (-x * φ x) x := by
    intro x
    have hdiff : DifferentiableAt ℝ φ x := by
      change
        DifferentiableAt ℝ
          (fun y : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(y ^ 2) / 2)) x
      fun_prop
    simpa [deriv_φ (u := x)] using hdiff.hasDerivAt
  have hu_deriv :
      ∀ x ∈ Set.Ioi u, HasDerivAt (fun y : ℝ => -φ y) (x * φ x) x := by
    intro x hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hφderiv x).neg
  have hv_deriv :
      ∀ x ∈ Set.Ioi u, HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := by
    intro x hx
    have hxpos : 0 < x := lt_trans hu (by simpa [Set.mem_Ioi] using hx)
    simpa using hasDerivAt_inv (ne_of_gt hxpos)

  have hφ_int : Integrable (fun x : ℝ => φ x) (volume.restrict (Set.Ioi u)) := by
    simpa [IntegrableOn] using (integrable_φ.integrableOn (s := Set.Ioi u))

  have hu'v_int : IntegrableOn (fun x : ℝ => (x * φ x) * x⁻¹) (Set.Ioi u) := by
    have hEq :
        (fun x : ℝ => (x * φ x) * x⁻¹) =ᵐ[volume.restrict (Set.Ioi u)]
          fun x => φ x := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 ?_
      refine ae_of_all _ (fun x hx => ?_)
      have hxpos : 0 < x := lt_trans hu (by simpa [Set.mem_Ioi] using hx)
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      simp [mul_assoc, mul_left_comm, mul_comm, hx0]
    exact hφ_int.congr hEq.symm

  have huv'_int : IntegrableOn (fun x : ℝ => (-φ x) * (-(x ^ 2)⁻¹)) (Set.Ioi u) := by
    have hdom :
        Integrable (fun x : ℝ => (1 / u ^ 2) * φ x) (volume.restrict (Set.Ioi u)) := by
      exact hφ_int.const_mul (1 / u ^ 2)
    have hmeas :
        AEStronglyMeasurable (fun x : ℝ => (-φ x) * (-(x ^ 2)⁻¹))
          (volume.restrict (Set.Ioi u)) := by
      have : Measurable (fun x : ℝ => (-φ x) * (-(x ^ 2)⁻¹)) := by
        have hφm : Measurable (fun x : ℝ => φ x) := continuous_φ.measurable
        have hx2 : Measurable (fun x : ℝ => x ^ 2) := (measurable_id.pow_const (2 : ℕ))
        exact hφm.neg.mul (hx2.inv.neg)
      exact this.aestronglyMeasurable
    have hbound :
        ∀ᵐ x ∂(volume.restrict (Set.Ioi u)),
          ‖(-φ x) * (-(x ^ 2)⁻¹)‖ ≤ ‖(1 / u ^ 2) * φ x‖ := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 ?_
      refine ae_of_all _ (fun x hx => ?_)
      have hxpos : 0 < x := lt_trans hu (by simpa [Set.mem_Ioi] using hx)
      have hu2pos : 0 < u ^ 2 := by nlinarith [hu]
      have hx2_ge : u ^ 2 ≤ x ^ 2 := by
        have hux : u ≤ x := le_of_lt (by simpa [Set.mem_Ioi] using hx)
        have habs : |u| ≤ |x| := by
          have hx0 : 0 ≤ x := le_of_lt hxpos
          simpa [abs_of_nonneg (le_of_lt hu), abs_of_nonneg hx0] using hux
        exact (sq_le_sq).2 habs
      have hinv' : (1 : ℝ) / (x ^ 2) ≤ (1 : ℝ) / (u ^ 2) :=
        one_div_le_one_div_of_le hu2pos hx2_ge
      have hinv : (x ^ 2)⁻¹ ≤ (u ^ 2)⁻¹ := by
        simpa [one_div] using hinv'
      have : |φ x| * (x ^ 2)⁻¹ ≤ (u ^ 2)⁻¹ * |φ x| := by
        calc
          |φ x| * (x ^ 2)⁻¹ ≤ |φ x| * (u ^ 2)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv (abs_nonneg (φ x))
          _ = (u ^ 2)⁻¹ * |φ x| := by
            simpa [mul_comm]
      simpa [Real.norm_eq_abs, abs_mul, one_div, mul_assoc, mul_left_comm, mul_comm] using this
    exact hdom.mono hmeas hbound

  have h_zero :
      Filter.Tendsto (fun x : ℝ => (-φ x) * x⁻¹)
        (nhdsWithin u (Set.Ioi u)) (nhds ((-φ u) * u⁻¹)) := by
    have hcont : ContinuousAt (fun x : ℝ => (-φ x) * x⁻¹) u := by
      have hφc : ContinuousAt (fun x : ℝ => -φ x) u := continuous_φ.continuousAt.neg
      have hinv : ContinuousAt (fun x : ℝ => x⁻¹) u :=
        ContinuousInv₀.continuousAt_inv₀ (ne_of_gt hu)
      simpa [mul_assoc] using hφc.mul hinv
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

  have h_infty :
      Filter.Tendsto (fun x : ℝ => (-φ x) * x⁻¹) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_φ_atTop_zero.neg.mul tendsto_inv_atTop_zero)

  have hibp :=
    MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := u)
      (u := fun x : ℝ => -φ x) (u' := fun x : ℝ => x * φ x)
      (v := fun x : ℝ => x⁻¹) (v' := fun x : ℝ => -(x ^ 2)⁻¹)
      (a' := (-φ u) * u⁻¹) (b' := (0 : ℝ))
      hu_deriv hv_deriv huv'_int hu'v_int h_zero h_infty

  have hu'v_simp :
      (∫ x in Set.Ioi u, (x * φ x) * x⁻¹) = ∫ x in Set.Ioi u, φ x := by
    have hEq :
        (fun x : ℝ => (x * φ x) * x⁻¹) =ᵐ[volume.restrict (Set.Ioi u)]
          fun x => φ x := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 ?_
      refine ae_of_all _ (fun x hx => ?_)
      have hxpos : 0 < x := lt_trans hu (by simpa [Set.mem_Ioi] using hx)
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      simp [mul_assoc, mul_left_comm, mul_comm, hx0]
    simpa using (MeasureTheory.integral_congr_ae hEq)

  have hibp' :
      (∫ x in Set.Ioi u, φ x / x ^ 2) = (φ u / u) - ∫ x in Set.Ioi u, φ x := by
    have hEq :
        (fun x : ℝ => (-φ x) * (-(x ^ 2)⁻¹)) = fun x => φ x / x ^ 2 := by
      funext x
      ring_nf
    calc
      (∫ x in Set.Ioi u, φ x / x ^ 2) =
          ∫ x in Set.Ioi u, (-φ x) * (-(x ^ 2)⁻¹) := by
            simpa [hEq, div_eq_mul_inv]
      _ = (0 : ℝ) - ((-φ u) * u⁻¹) - ∫ x in Set.Ioi u, (x * φ x) * x⁻¹ := by
            simpa using hibp
      _ = (φ u / u) - ∫ x in Set.Ioi u, φ x := by
            rw [hu'v_simp]
            simp [div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]

  have hΦ : Φbar u = ∫ x in Set.Ioi u, φ x := (Φbar_eq_integral_Ioi (u := u))

  have : Φbar u = φ u / u - ∫ x in Set.Ioi u, φ x / x ^ 2 := by
    have : (∫ x in Set.Ioi u, φ x) = φ u / u - ∫ x in Set.Ioi u, φ x / x ^ 2 := by
      linarith [hibp']
    simpa [hΦ] using this
  simpa using this

lemma E_le_add_inv {u : ℝ} (hu : 0 < u) : E u ≤ u + 1 / u := by
  have hΦ := Φbar_eq_phi_div_sub_integral (u := u) hu
  have hI :
      (∫ x in Set.Ioi u, φ x / x ^ 2) ≤ (1 / u ^ 2) * Φbar u := by
    have hφ_int : Integrable (fun x : ℝ => φ x) (volume.restrict (Set.Ioi u)) := by
      simpa [IntegrableOn] using (integrable_φ.integrableOn (s := Set.Ioi u))
    have hF_int :
        Integrable (fun x : ℝ => φ x / x ^ 2) (volume.restrict (Set.Ioi u)) := by
      have hdom : Integrable (fun x : ℝ => (1 / u ^ 2) * φ x) (volume.restrict (Set.Ioi u)) := by
        exact hφ_int.const_mul (1 / u ^ 2)
      have hmeas :
          AEStronglyMeasurable (fun x : ℝ => φ x / x ^ 2) (volume.restrict (Set.Ioi u)) := by
        have : Measurable (fun x : ℝ => φ x / x ^ 2) := by
          have hφm : Measurable (fun x : ℝ => φ x) := continuous_φ.measurable
          have hx2 : Measurable (fun x : ℝ => x ^ 2) := (measurable_id.pow_const (2 : ℕ))
          simpa [div_eq_mul_inv] using hφm.mul hx2.inv
        exact this.aestronglyMeasurable
      have hbound :
          ∀ᵐ x ∂(volume.restrict (Set.Ioi u)), ‖φ x / x ^ 2‖ ≤ ‖(1 / u ^ 2) * φ x‖ := by
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 ?_
        refine ae_of_all _ (fun x hx => ?_)
        have hxpos : 0 < x := lt_trans hu (by simpa [Set.mem_Ioi] using hx)
        have hu2pos : 0 < u ^ 2 := by nlinarith [hu]
        have hx2_ge : u ^ 2 ≤ x ^ 2 := by
          have hux : u ≤ x := le_of_lt (by simpa [Set.mem_Ioi] using hx)
          have habs : |u| ≤ |x| := by
            have hx0 : 0 ≤ x := le_of_lt hxpos
            simpa [abs_of_nonneg (le_of_lt hu), abs_of_nonneg hx0] using hux
          exact (sq_le_sq).2 habs
        have hinv' : (1 : ℝ) / (x ^ 2) ≤ (1 : ℝ) / (u ^ 2) :=
          one_div_le_one_div_of_le hu2pos hx2_ge
        have hinv : (x ^ 2)⁻¹ ≤ (u ^ 2)⁻¹ := by
          simpa [one_div] using hinv'
        have : |φ x| * (x ^ 2)⁻¹ ≤ (u ^ 2)⁻¹ * |φ x| := by
          calc
            |φ x| * (x ^ 2)⁻¹ ≤ |φ x| * (u ^ 2)⁻¹ := by
              exact mul_le_mul_of_nonneg_left hinv (abs_nonneg (φ x))
            _ = (u ^ 2)⁻¹ * |φ x| := by
              simpa [mul_comm]
        simpa [Real.norm_eq_abs, abs_mul, one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      exact hdom.mono hmeas hbound
    have hG_int :
        Integrable (fun x : ℝ => (1 / u ^ 2) * φ x) (volume.restrict (Set.Ioi u)) := by
      exact hφ_int.const_mul (1 / u ^ 2)
    have hmono :
        (∫ x in Set.Ioi u, φ x / x ^ 2) ≤ ∫ x in Set.Ioi u, (1 / u ^ 2) * φ x := by
      refine MeasureTheory.integral_mono_ae (μ := volume.restrict (Set.Ioi u)) hF_int hG_int ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 ?_
      refine ae_of_all _ (fun x hx => ?_)
      have hxpos : 0 < x := lt_trans hu (by simpa [Set.mem_Ioi] using hx)
      have hu2pos : 0 < u ^ 2 := by nlinarith [hu]
      have hx2_ge : u ^ 2 ≤ x ^ 2 := by
        have hux : u ≤ x := le_of_lt (by simpa [Set.mem_Ioi] using hx)
        have habs : |u| ≤ |x| := by
          have hx0 : 0 ≤ x := le_of_lt hxpos
          simpa [abs_of_nonneg (le_of_lt hu), abs_of_nonneg hx0] using hux
        exact (sq_le_sq).2 habs
      have hinv : (1 : ℝ) / (x ^ 2) ≤ (1 : ℝ) / (u ^ 2) :=
        one_div_le_one_div_of_le hu2pos hx2_ge
      have hφnonneg : 0 ≤ φ x := (φ_pos (u := x)).le
      have hmul : φ x * ((1 : ℝ) / (x ^ 2)) ≤ φ x * ((1 : ℝ) / (u ^ 2)) :=
        mul_le_mul_of_nonneg_left hinv hφnonneg
      simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      (∫ x in Set.Ioi u, φ x / x ^ 2) ≤ ∫ x in Set.Ioi u, (1 / u ^ 2) * φ x := hmono
      _ = (1 / u ^ 2) * ∫ x in Set.Ioi u, φ x := by
            simp [MeasureTheory.integral_const_mul]
      _ = (1 / u ^ 2) * Φbar u := by
            simp [Φbar_eq_integral_Ioi (u := u)]

  have hφu : φ u / u = Φbar u + ∫ x in Set.Ioi u, φ x / x ^ 2 := by
    linarith [hΦ]

  have hφu_le : φ u / u ≤ (1 + 1 / u ^ 2) * Φbar u := by
    rw [hφu]
    have hI' :
        Φbar u + ∫ x in Set.Ioi u, φ x / x ^ 2 ≤ Φbar u + (1 / u ^ 2) * Φbar u :=
      add_le_add_right hI (Φbar u)
    have : Φbar u + (1 / u ^ 2) * Φbar u = (1 + 1 / u ^ 2) * Φbar u := by ring
    calc
      Φbar u + ∫ x in Set.Ioi u, φ x / x ^ 2 ≤ Φbar u + (1 / u ^ 2) * Φbar u := hI'
      _ = (1 + 1 / u ^ 2) * Φbar u := this

  have hΦpos : 0 < Φbar u := Φbar_pos (u := u)
  have hu0 : 0 ≤ u := le_of_lt hu
  have hmul : u * (φ u / u) ≤ u * ((1 + 1 / u ^ 2) * Φbar u) :=
    mul_le_mul_of_nonneg_left hφu_le hu0

  have hmain : φ u ≤ (u + 1 / u) * Φbar u := by
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have hleft : u * (φ u / u) = φ u := by
      field_simp [hu_ne]
    have hright : u * ((1 + (u ^ 2)⁻¹) * Φbar u) = (u + 1 / u) * Φbar u := by
      have : u * ((1 + 1 / u ^ 2) * Φbar u) = (u + 1 / u) * Φbar u := by
        field_simp [hu_ne]
      simpa [one_div] using this
    simpa [hleft, hright, one_div] using hmul

  have hΦinv_nonneg : 0 ≤ (Φbar u)⁻¹ := inv_nonneg.2 hΦpos.le
  have hmul' : φ u * (Φbar u)⁻¹ ≤ (u + 1 / u) := by
    have := mul_le_mul_of_nonneg_right hmain hΦinv_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm, hΦpos.ne'] using this

  simpa [E, div_eq_mul_inv] using hmul'

noncomputable def C_mills : ℝ := max ((Φbar 1)⁻¹) 1

lemma E_le_abs_add_C (u : ℝ) : E u ≤ |u| + C_mills := by
  classical
  by_cases hu1 : u ≤ 1
  · have hE : E u ≤ (Φbar 1)⁻¹ := E_le_inv_Φbar_one_of_le_one (u := u) hu1
    have hC : (Φbar 1)⁻¹ ≤ C_mills := le_max_left _ _
    exact le_trans (le_trans hE hC) (by nlinarith [abs_nonneg u])
  · have hu1' : 1 < u := lt_of_not_ge hu1
    have hu0 : 0 < u := lt_trans (by linarith) hu1'
    have hE : E u ≤ u + 1 / u := E_le_add_inv (u := u) hu0
    have h1u : 1 / u ≤ 1 := by
      have : (1 : ℝ) / u ≤ (1 : ℝ) / (1 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (le_of_lt hu1')
      simpa using this
    have hC1 : (1 : ℝ) ≤ C_mills := le_max_right _ _
    have hE' : E u ≤ u + C_mills := by
      calc
        E u ≤ u + 1 / u := hE
        _ ≤ u + 1 := by nlinarith [h1u]
        _ ≤ u + C_mills := by nlinarith [hC1]
    simpa [abs_of_pos hu0, add_assoc, add_left_comm, add_comm] using hE'
/-! Goal -/

variable {t : ℝ}

/-! Step 1 -/

lemma B_eq :
    B (P := P) (κ := κ) (Z := Z) t =
      (1 - t) * 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) t ω)) := by
  simp [B, h]

/-! Step 2 -/

  /-- Justify differentiation under the expectation.

  This is a thin wrapper around
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (differentiation under the integral sign),
  specialized to the integrand `ω ↦ h (U_s ω)`.

  The assumptions are exactly the usual ones: measurability near `t`, integrability at `t`,
  and a domination hypothesis for the pointwise derivative on a uniform ball around `t`. -/
  lemma h_deriv_under_expect
      (ε : ℝ) (ε_pos : 0 < ε)
      (h_meas :
        ∀ᶠ s in nhds t, AEStronglyMeasurable (fun ω => h (U (κ := κ) (Z := Z) s ω)) P)
      (h_int : Integrable (fun ω => h (U (κ := κ) (Z := Z) t ω)) P)
      (hF'_meas :
        AEStronglyMeasurable
          (fun ω =>
            (deriv h (U (κ := κ) (Z := Z) t ω))
              * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)) P)
      (bound : Ω → ℝ)
      (h_bound :
        ∀ᵐ ω ∂P, ∀ s ∈ Metric.ball t ε,
          ‖(deriv h (U (κ := κ) (Z := Z) s ω))
              * (deriv (fun r => U (κ := κ) (Z := Z) r ω) s)‖ ≤ bound ω)
      (bound_int : Integrable bound P)
      (h_diff :
        ∀ᵐ ω ∂P, ∀ s ∈ Metric.ball t ε,
          HasDerivAt
            (fun r => h (U (κ := κ) (Z := Z) r ω))
            ((deriv h (U (κ := κ) (Z := Z) s ω))
              * (deriv (fun r => U (κ := κ) (Z := Z) r ω) s))
            s) :
      HasDerivAt
        (fun s => 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
        (𝔼 (P := P) (fun ω =>
          (deriv h (U (κ := κ) (Z := Z) t ω))
            * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
        t := by
    have hmain :=
        (hasDerivAt_integral_of_dominated_loc_of_deriv_le
          (μ := P)
          (F := fun s ω => h (U (κ := κ) (Z := Z) s ω))
          (x₀ := t)
          (ε := ε)
          (bound := bound)
          (F' := fun s ω =>
            (deriv h (U (κ := κ) (Z := Z) s ω))
              * (deriv (fun r => U (κ := κ) (Z := Z) r ω) s))
          ε_pos h_meas h_int hF'_meas h_bound bound_int h_diff).2
    simpa [𝔼] using hmain

  /-- Analytic domination step: justify differentiation under the expectation.

  Fill this using your growth bounds and integrability arguments.
  -/
  lemma diff_under_expect_justification
      (h_deriv_under_expect :
        HasDerivAt
          (fun s =>
            𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
          (𝔼 (P := P) (fun ω =>
            (deriv h (U (κ := κ) (Z := Z) t ω))
              * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
          t) :
      DifferentiableAt ℝ (fun s => B (P := P) (κ := κ) (Z := Z) s) t := by
    have h1 : DifferentiableAt ℝ (fun s : ℝ => 1 - s) t := by
      fun_prop
    have h2 :
        DifferentiableAt ℝ (fun s => 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω))) t :=
      h_deriv_under_expect.differentiableAt
    simpa [B, h] using h1.mul h2

  lemma deriv_B_step2
      (h_deriv_under_expect :
        HasDerivAt
          (fun s =>
            𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
          (𝔼 (P := P) (fun ω =>
            (deriv h (U (κ := κ) (Z := Z) t ω))
              * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
          t) :
      deriv (fun s => B (P := P) (κ := κ) (Z := Z) s) t =
        - 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) t ω))
        + (1 - t) * 𝔼 (P := P) (fun ω =>
            (deriv h (U (κ := κ) (Z := Z) t ω)) * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)) := by
    have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hprod :
        HasDerivAt
          (fun s =>
            (1 - s) * 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
          ((-1) * 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) t ω))
            + (1 - t)
              * 𝔼 (P := P) (fun ω =>
                (deriv h (U (κ := κ) (Z := Z) t ω))
                  * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
          t := by
      simpa using h1.mul h_deriv_under_expect
    -- Rewrite `B` using `h` and apply the product rule.
    simpa [B, h, mul_add, add_mul, add_assoc, add_left_comm, add_comm] using hprod.deriv

/-! Step 3 -/

  lemma deriv_U (ht : t ∈ Set.Ioo (0 : ℝ) 1) (ω : Ω) :
      deriv (fun s => U (κ := κ) (Z := Z) s ω) t =
        (U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))
        - (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t)) := by
    have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht.1
    have ht1 : (1 - t : ℝ) ≠ 0 := by
      have : (0 : ℝ) < 1 - t := sub_pos.mpr ht.2
      exact ne_of_gt this
    have hdenom : Real.sqrt (1 - t) ≠ 0 := by
      have : (0 : ℝ) < 1 - t := sub_pos.mpr ht.2
      exact ne_of_gt (Real.sqrt_pos.2 this)

    -- Differentiate `U(s,ω) = (κ - √s * Z ω) / √(1 - s)` via the quotient rule.
    have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt s) (1 / (2 * Real.sqrt t)) t := by
      simpa using Real.hasDerivAt_sqrt (x := t) ht0
    have hmul :
        HasDerivAt (fun s : ℝ => Real.sqrt s * Z ω) ((1 / (2 * Real.sqrt t)) * Z ω) t := by
      simpa using hsqrt.mul_const (Z ω)
    have hnum :
        HasDerivAt (fun s : ℝ => κ - Real.sqrt s * Z ω) (-(Z ω) / (2 * Real.sqrt t)) t := by
      have := hmul.const_sub κ
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hden :
        HasDerivAt (fun s : ℝ => Real.sqrt (1 - s)) (-(1 / (2 * Real.sqrt (1 - t)))) t := by
      have h_inside : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
      have hsqrt_at :
          HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * Real.sqrt (1 - t))) (1 - t) := by
        simpa using Real.hasDerivAt_sqrt (x := 1 - t) ht1
      have hcomp :
          HasDerivAt (fun s : ℝ => Real.sqrt (1 - s)) ((1 / (2 * Real.sqrt (1 - t))) * (-1)) t :=
        hsqrt_at.comp t h_inside
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcomp

    have hU' :
        HasDerivAt
          (fun s : ℝ => (κ - Real.sqrt s * Z ω) / Real.sqrt (1 - s))
          (((-(Z ω) / (2 * Real.sqrt t)) * Real.sqrt (1 - t)
              - (κ - Real.sqrt t * Z ω) * (-(1 / (2 * Real.sqrt (1 - t)))))
            / (Real.sqrt (1 - t)) ^ 2)
          t := by
      simpa using (hnum.div hden hdenom)
    have hsqrt_t : Real.sqrt t ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 ht.1)
    have h1mt : (1 - t) ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr ht.2)
    have ht0' : 0 ≤ t := le_of_lt ht.1
    have ht1' : 0 ≤ 1 - t := le_of_lt (sub_pos.mpr ht.2)

    -- Unfold `U` and simplify the quotient-rule expression.
    simp [U]
    have hder :
        deriv (fun s : ℝ => (κ - Real.sqrt s * Z ω) / Real.sqrt (1 - s)) t =
          (((-(Z ω) / (2 * Real.sqrt t)) * Real.sqrt (1 - t)
              - (κ - Real.sqrt t * Z ω) * (-(1 / (2 * Real.sqrt (1 - t)))))
            / (Real.sqrt (1 - t)) ^ 2) := by
      simpa using hU'.deriv
    rw [hder]
    field_simp [hsqrt_t, hdenom, h1mt]
    have ht1'' : 0 ≤ -t + 1 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using ht1'
    simp [Real.sq_sqrt ht1'', sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

  lemma deriv_B_step3
      (ht : t ∈ Set.Ioo (0 : ℝ) 1)
      (h_deriv_under_expect :
        HasDerivAt
          (fun s =>
            𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
          (𝔼 (P := P) (fun ω =>
            (deriv h (U (κ := κ) (Z := Z) t ω))
              * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
          t)
      (integrable_h : Integrable (fun ω => h (U (κ := κ) (Z := Z) t ω)) P)
      (integrable_Uh :
        Integrable
          (fun ω => (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P)
      (integrable_Zh :
        Integrable
          (fun ω => (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P) :
      deriv (fun s => B (P := P) (κ := κ) (Z := Z) s) t =
        𝔼 (P := P) (fun ω =>
          -h (U (κ := κ) (Z := Z) t ω)
            + (1 / 2) * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω)))
        - (Real.sqrt (1 - t) / (2 * Real.sqrt t))
          * 𝔼 (P := P) (fun ω => (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) := by
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have hsqrt_t : Real.sqrt t ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 ht0)
    have hdenom : Real.sqrt (1 - t) ≠ 0 := by
      have : (0 : ℝ) < 1 - t := sub_pos.mpr ht1
      exact ne_of_gt (Real.sqrt_pos.2 this)
    have h1mt : (1 - t) ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr ht1)

    -- Start from Step 2 and substitute `∂ₜ U_t`.
    have hstep2 := deriv_B_step2 (t := t) (h_deriv_under_expect := h_deriv_under_expect)
    -- Rewrite the `U`-derivative inside the expectation.
    have hU_rw :
        𝔼 (P := P) (fun ω =>
            (deriv h (U (κ := κ) (Z := Z) t ω))
              * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)) =
          𝔼 (P := P) (fun ω =>
            (deriv h (U (κ := κ) (Z := Z) t ω))
              * ((U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))
                  - (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t)))) := by
      -- Use `deriv_U` pointwise under the integral.
      have hpoint :
          (fun ω =>
              (deriv h (U (κ := κ) (Z := Z) t ω))
                * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)) =
            fun ω =>
              (deriv h (U (κ := κ) (Z := Z) t ω))
                * ((U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))
                    - (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t))) := by
        funext ω
        rw [deriv_U (t := t) (ht := ht) (ω := ω)]
      simp [𝔼, hpoint]

    -- Replace the expectation term and move the prefactor `(1 - t)` inside.
    rw [hstep2]
    rw [hU_rw]

    -- Put constants inside expectations to simplify pointwise.
    have hmul_const :
        (1 - t)
            * 𝔼 (P := P) (fun ω =>
              (deriv h (U (κ := κ) (Z := Z) t ω))
                * ((U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))
                    - (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t)))) =
          𝔼 (P := P) (fun ω =>
            (1 - t)
              * ((deriv h (U (κ := κ) (Z := Z) t ω))
                  * ((U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))
                      - (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t))))) := by
      simp [𝔼, MeasureTheory.integral_const_mul]
    rw [hmul_const]

    -- Expand the integrand and separate the Bochner integrals (requires integrability).
    have integrable_B :
        Integrable
          (fun ω =>
            (2 : ℝ)⁻¹ * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P := by
      -- `(1/2)` is a constant scalar.
      simpa [mul_assoc, mul_left_comm, mul_comm] using (integrable_Uh.const_mul ((2 : ℝ)⁻¹))
    have integrable_cC :
        Integrable
          (fun ω =>
            (Real.sqrt (1 - t) / (2 * Real.sqrt t))
              * ((Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω)))) P := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (integrable_Zh.const_mul (Real.sqrt (1 - t) / (2 * Real.sqrt t)))

    -- Rewrite the whole derivative expression into the desired form.
    -- First, simplify the prefactor `(1 - t)` against `1 - t` in the denominator.
    -- Then, combine the first two expectation terms into a single expectation.
    -- The remaining `Z`-term is already in the right shape.
    have hmain :
        -𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) t ω))
          + 𝔼 (P := P) (fun ω =>
              (1 - t)
                * ((deriv h (U (κ := κ) (Z := Z) t ω))
                    * ((U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))
                        - (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t))))) =
          𝔼 (P := P) (fun ω =>
              -h (U (κ := κ) (Z := Z) t ω)
                + (1 / 2) * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω)))
            - (Real.sqrt (1 - t) / (2 * Real.sqrt t))
              * 𝔼 (P := P) (fun ω => (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) := by
      have integrable_neg_h :
          Integrable (fun ω => -h (U (κ := κ) (Z := Z) t ω)) P :=
        integrable_h.neg
      have hpoint_simpl :
          (fun ω =>
              (1 - t)
                * ((deriv h (U (κ := κ) (Z := Z) t ω))
                    * ((U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))
                        - (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t))))) =
            fun ω =>
              (1 / 2) * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))
                - (Real.sqrt (1 - t) / (2 * Real.sqrt t))
                  * ((Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) := by
        funext ω
        field_simp [hsqrt_t, hdenom, h1mt]
        ring_nf
        have ht1_nonneg : 0 ≤ 1 - t := le_of_lt (sub_pos.mpr ht1)
        -- `ring_nf` leaves a residual `√(1 - t)^2`; eliminate it and finish.
        simp [Real.sq_sqrt ht1_nonneg]
        ring

      -- Unfold expectations and rewrite the integrand.
      simp [𝔼, hpoint_simpl]
      -- Split the integral of the difference on the LHS.
      rw [MeasureTheory.integral_sub integrable_B integrable_cC]
      -- Split the integral of the sum on the RHS.
      rw [MeasureTheory.integral_add integrable_neg_h integrable_B]
      -- Rewrite `-∫ h` as `∫ (-h)`.
      have hneg :
          -(∫ ω : Ω, h (U (κ := κ) (Z := Z) t ω) ∂P) =
            ∫ ω : Ω, -h (U (κ := κ) (Z := Z) t ω) ∂P := by
        simpa using (MeasureTheory.integral_neg (μ := P) (f := fun ω => h (U (κ := κ) (Z := Z) t ω))).symm
      -- Pull out the constant on the `Z`-term and finish by ring normalization.
      simp [MeasureTheory.integral_const_mul, hneg]
      ring_nf

    -- Finish by rewriting into the target statement.
    simpa [hmain, add_assoc, add_left_comm, add_comm]

/-! Step 4 -/

/-- The auxiliary function `ψ(z) = h'( (κ - √t z)/√(1-t) )`. -/
def ψ (z : ℝ) : ℝ := deriv h ((κ - Real.sqrt t * z) / Real.sqrt (1 - t))

lemma deriv_ψ (ht : t ∈ Set.Ioo (0 : ℝ) 1) (z : ℝ) :
    deriv (ψ (κ := κ) (t := t)) z =
      -(Real.sqrt (t / (1 - t))) * (deriv (fun u => deriv h u) ((κ - Real.sqrt t * z) / Real.sqrt (1 - t))) := by
  let ufun : ℝ → ℝ := fun z => (κ - Real.sqrt t * z) / Real.sqrt (1 - t)
  have hu : DifferentiableAt ℝ ufun z := by
    fun_prop

  have hderiv_h_fun :
      (fun u : ℝ => deriv h u) = fun u : ℝ => 2 * (E u) * ((E u) ^ 2 - u * E u) := by
    funext u
    have hE : DifferentiableAt ℝ E u :=
      differentiableAt_E (u := u)
    have hderiv_h :
        deriv h u = (2 : ℝ) * (E u) * (deriv E u) := by
      have hEq : h = E * E := by
        funext x
        simp [h, pow_two]
      have hpow : deriv (E * E) u = (2 : ℝ) * (E u) * (deriv E u) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
          (deriv_pow (f := E) (x := u) hE 2)
      simpa [hEq] using hpow
    rw [hderiv_h, deriv_E (u := u)]

  have hE0 : DifferentiableAt ℝ E (ufun z) :=
    differentiableAt_E (u := ufun z)
  have houter_poly :
      DifferentiableAt ℝ (fun u : ℝ => 2 * (E u) * ((E u) ^ 2 - u * E u)) (ufun z) := by
    fun_prop
  have houter : DifferentiableAt ℝ (fun u : ℝ => deriv h u) (ufun z) := by
    simpa [hderiv_h_fun] using houter_poly

  have hcomp :
      deriv ((fun u : ℝ => deriv h u) ∘ ufun) z =
        deriv (fun u : ℝ => deriv h u) (ufun z) * deriv ufun z := by
    simpa using (deriv_comp z houter hu)
  have hcomp' :
      deriv (ψ (κ := κ) (t := t)) z =
        deriv (fun u : ℝ => deriv h u) (ufun z) * deriv ufun z := by
    simpa [ψ, ufun, Function.comp] using hcomp

  have hdu : deriv ufun z = -(Real.sqrt (t / (1 - t))) := by
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hdu' : deriv ufun z = -(Real.sqrt t / Real.sqrt (1 - t)) := by
      simp [ufun, deriv_div_const, deriv_sub, differentiableAt_const, differentiableAt_id, deriv_const,
        deriv_const_mul, deriv_id, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hsqrt :
        Real.sqrt t / Real.sqrt (1 - t) = Real.sqrt (t / (1 - t)) := by
      simpa using (Real.sqrt_div ht0 (1 - t)).symm
    simpa [hdu', hsqrt]

  -- Insert the derivative of `ufun` and commute constants.
  calc
    deriv (ψ (κ := κ) (t := t)) z =
        deriv (fun u : ℝ => deriv h u) (ufun z) * deriv ufun z := hcomp'
    _ = deriv (fun u : ℝ => deriv h u) (ufun z) * (-(Real.sqrt (t / (1 - t)))) := by
        simp [hdu]
    _ = -(Real.sqrt (t / (1 - t))) * deriv (fun u : ℝ => deriv h u) (ufun z) := by
        simp [mul_assoc, mul_left_comm, mul_comm]
    _ = -(Real.sqrt (t / (1 - t)))
        * deriv (fun u => deriv h u) ((κ - Real.sqrt t * z) / Real.sqrt (1 - t)) := by
        simp [ufun]

private lemma gaussianIBP_gaussianReal
    (ψ : ℝ → ℝ)
    (hψ : Differentiable ℝ ψ)
    (hψ_int : Integrable ψ (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))))
    (hψ'_int :
      Integrable (fun x => deriv ψ x) (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))))
    (hxψ_int :
      Integrable (fun x => x * ψ x) (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))) :
    (∫ x, x * ψ x ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))) =
      (∫ x, deriv ψ x ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))) := by
  set μ : Measure ℝ := ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  have hv : (1 : ℝ≥0) ≠ 0 := by simp
  have hf : Measurable (ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0)) :=
    ProbabilityTheory.measurable_gaussianPDF _ _
  have hflt :
      (∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0) x < ∞) := by
    exact ae_of_all _ (fun _ => ProbabilityTheory.gaussianPDF_lt_top)

  have hψ_int' :
      Integrable ψ (volume.withDensity (ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0))) := by
    simpa [μ, ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv] using
      hψ_int
  have hψ'_int' :
      Integrable (fun x => deriv ψ x)
        (volume.withDensity (ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0))) := by
    simpa [μ, ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv] using
      hψ'_int
  have hxψ_int' :
      Integrable (fun x => x * ψ x)
        (volume.withDensity (ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0))) := by
    simpa [μ, ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv] using
      hxψ_int

  have hψφ : Integrable (fun x : ℝ => ψ x * φ x) (volume : Measure ℝ) := by
    have h :=
      (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
            (f := ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0)) hf hflt (g := ψ)).1 hψ_int'
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, φ_eq_gaussianPDFReal] using h
  have hψ'φ : Integrable (fun x : ℝ => deriv ψ x * φ x) (volume : Measure ℝ) := by
    have h :=
      (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
            (f := ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0)) hf hflt (g := fun x => deriv ψ x)).1
        hψ'_int'
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, φ_eq_gaussianPDFReal] using h
  have hxψφ : Integrable (fun x : ℝ => (x * ψ x) * φ x) (volume : Measure ℝ) := by
    have h :=
      (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
            (f := ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0)) hf hflt (g := fun x => x * ψ x)).1
        hxψ_int'
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, φ_eq_gaussianPDFReal] using h

  have hu : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x => (hψ x).hasDerivAt
  have hvφ : ∀ x, HasDerivAt φ (-x * φ x) x := by
    intro x
    have hdiff : DifferentiableAt ℝ φ x := by
      change
        DifferentiableAt ℝ
          (fun u : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(u ^ 2) / 2)) x
      fun_prop
    simpa [deriv_φ (u := x)] using hdiff.hasDerivAt

  have huv' : Integrable (fun x : ℝ => ψ x * (-x * φ x)) (volume : Measure ℝ) := by
    have hneg : Integrable (fun x : ℝ => -(x * (ψ x * φ x))) (volume : Measure ℝ) := by
      simpa [mul_assoc] using (hxψφ.const_mul (-1 : ℝ))
    have hpoint :
        (fun x : ℝ => ψ x * (-x * φ x)) = fun x => -(x * (ψ x * φ x)) := by
      funext x
      ring_nf
    rw [hpoint]
    exact hneg

  have hu'v : Integrable (fun x : ℝ => deriv ψ x * φ x) (volume : Measure ℝ) := hψ'φ

  have huv : Integrable (fun x : ℝ => ψ x * φ x) (volume : Measure ℝ) := hψφ

  have hibp_vol :
      (∫ x : ℝ, ψ x * (-x * φ x)) = -∫ x : ℝ, (deriv ψ x) * φ x := by
    simpa using
      (MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
        (u := ψ) (v := φ) (u' := fun x => deriv ψ x) (v' := fun x => -x * φ x)
        hu hvφ huv' hu'v huv)

  have hibp_vol' :
      (∫ x : ℝ, (x * ψ x) * φ x) = ∫ x : ℝ, (deriv ψ x) * φ x := by
    have hneg :
        (∫ x : ℝ, (x * ψ x) * φ x) = -∫ x : ℝ, ψ x * (-x * φ x) := by
      -- Expand and use linearity.
      have :
          (fun x : ℝ => (x * ψ x) * φ x) = fun x => -(ψ x * (-x * φ x)) := by
        funext x
        ring_nf
      simp [this, MeasureTheory.integral_neg]
    have hneg' :
        -∫ x : ℝ, ψ x * (-x * φ x) = ∫ x : ℝ, (deriv ψ x) * φ x := by
      simpa using congrArg Neg.neg hibp_vol
    simpa [hneg] using hneg'

  -- Go back to the Gaussian measure using `integral_gaussianReal_eq_integral_smul`.
  have hL :
      (∫ x, x * ψ x ∂μ) = ∫ x : ℝ, (x * ψ x) * φ x := by
    have hμ :
        (∫ x, x * ψ x ∂μ) =
          ∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x * (x * ψ x) := by
      simpa [μ, ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv,
        smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    simpa [μ, φ_eq_gaussianPDFReal, mul_assoc, mul_left_comm, mul_comm] using hμ
  have hR :
      (∫ x, deriv ψ x ∂μ) = ∫ x : ℝ, (deriv ψ x) * φ x := by
    have hμ :
        (∫ x, deriv ψ x ∂μ) =
          ∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x * (deriv ψ x) := by
      simpa [μ, ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv,
        smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    simpa [μ, φ_eq_gaussianPDFReal, mul_assoc, mul_left_comm, mul_comm] using hμ

  -- Finish.
  calc
    (∫ x, x * ψ x ∂μ) = ∫ x : ℝ, (x * ψ x) * φ x := hL
    _ = ∫ x : ℝ, (deriv ψ x) * φ x := hibp_vol'
    _ = (∫ x, deriv ψ x ∂μ) := by
      simpa [hR]

/-- If `Z` has the standard Gaussian law, then `Z` is a.e. measurable. -/
lemma aemeasurable_Z_of_gaussian
    (hZ_gaussian :
      Measure.map Z P =
        ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))) :
    AEMeasurable Z P := by
  refine AEMeasurable.of_map_ne_zero ?_
  have hgauss_ne :
      (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))) ≠ 0 := by
    simpa using
      (MeasureTheory.IsProbabilityMeasure.ne_zero
        (μ :=
          ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))))
  simpa [hZ_gaussian] using hgauss_ne

/-- Evaluate the `Z`-term using Gaussian integration by parts for a standard normal `Z`. -/
lemma Z_term_eq
    (hZ_gaussian :
      Measure.map Z P =
        ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (integrable_Zh :
      Integrable (fun ω => (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P)
    (integrable_ψZ : Integrable (fun ω => ψ (κ := κ) (t := t) (Z ω)) P)
    (integrable_deriv_ψZ :
      Integrable (fun ω => deriv (ψ (κ := κ) (t := t)) (Z ω)) P) :
    𝔼 (P := P) (fun ω => (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) =
      -(Real.sqrt (t / (1 - t)))
        * 𝔼 (P := P) (fun ω => deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) := by
  have hZ_meas : AEMeasurable Z P :=
    aemeasurable_Z_of_gaussian (P := P) (Z := Z) (hZ_gaussian := hZ_gaussian)
  -- Unfold expectations to integrals.
  simp [𝔼]
  set μ : Measure ℝ :=
    ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  have hmap : Measure.map Z P = μ := by
    simpa [μ] using hZ_gaussian

  have hψdiff : Differentiable ℝ (ψ (κ := κ) (t := t)) := by
    intro z
    let ufun : ℝ → ℝ := fun z => (κ - Real.sqrt t * z) / Real.sqrt (1 - t)
    have hu : DifferentiableAt ℝ ufun z := by
      fun_prop
    have hderiv_h_fun :
        (fun u : ℝ => deriv h u) = fun u : ℝ => 2 * (E u) * ((E u) ^ 2 - u * E u) := by
      funext u
      have hE : DifferentiableAt ℝ E u := differentiableAt_E (u := u)
      have hderiv_h :
          deriv h u = (2 : ℝ) * (E u) * (deriv E u) := by
        have hEq : h = E * E := by
          funext x
          simp [h, pow_two]
        have hpow : deriv (E * E) u = (2 : ℝ) * (E u) * (deriv E u) := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            (deriv_pow (f := E) (x := u) hE 2)
        simpa [hEq] using hpow
      rw [hderiv_h, deriv_E (u := u)]
    have hE0 : DifferentiableAt ℝ E (ufun z) := differentiableAt_E (u := ufun z)
    have houter_poly :
        DifferentiableAt ℝ (fun u : ℝ => 2 * (E u) * ((E u) ^ 2 - u * E u)) (ufun z) := by
      fun_prop
    have houter : DifferentiableAt ℝ (fun u : ℝ => deriv h u) (ufun z) := by
      simpa [hderiv_h_fun] using houter_poly
    simpa [ψ, ufun, Function.comp] using houter.comp z hu

  have hψ_aesm : AEStronglyMeasurable (ψ (κ := κ) (t := t)) (Measure.map Z P) := by
    exact hψdiff.continuous.measurable.aestronglyMeasurable
  have hψ'_aesm :
      AEStronglyMeasurable (fun x : ℝ => deriv (ψ (κ := κ) (t := t)) x) (Measure.map Z P) := by
    simpa using aestronglyMeasurable_deriv (ψ (κ := κ) (t := t)) (Measure.map Z P)
  have hxψ_aesm :
      AEStronglyMeasurable (fun x : ℝ => x * (ψ (κ := κ) (t := t) x)) (Measure.map Z P) := by
    have hmeas : Measurable (fun x : ℝ => x * (ψ (κ := κ) (t := t) x)) := by
      simpa using measurable_id.mul (hψdiff.continuous.measurable)
    exact hmeas.aestronglyMeasurable

  have hψ_int_gauss : Integrable (ψ (κ := κ) (t := t)) μ := by
    have hψ_int_map : Integrable (ψ (κ := κ) (t := t)) (Measure.map Z P) := by
      exact (integrable_map_measure hψ_aesm hZ_meas).2 integrable_ψZ
    simpa [hmap] using hψ_int_map
  have hψ'_int_gauss : Integrable (fun x => deriv (ψ (κ := κ) (t := t)) x) μ := by
    have hψ'_int_map :
        Integrable (fun x => deriv (ψ (κ := κ) (t := t)) x) (Measure.map Z P) := by
      exact (integrable_map_measure hψ'_aesm hZ_meas).2 integrable_deriv_ψZ
    simpa [hmap] using hψ'_int_map
  have hxψ_int_gauss : Integrable (fun x => x * (ψ (κ := κ) (t := t) x)) μ := by
    have hxψ_int_map :
        Integrable (fun x => x * (ψ (κ := κ) (t := t) x)) (Measure.map Z P) := by
      have : Integrable (fun ω => (Z ω) * (ψ (κ := κ) (t := t) (Z ω))) P := by
        simpa [ψ, U] using integrable_Zh
      exact (integrable_map_measure hxψ_aesm hZ_meas).2 this
    simpa [hmap] using hxψ_int_map

  have hibp_gauss :
      (∫ x, x * (ψ (κ := κ) (t := t) x) ∂μ) =
        (∫ x, deriv (ψ (κ := κ) (t := t)) x ∂μ) := by
    simpa [μ] using
      gaussianIBP_gaussianReal (ψ := ψ (κ := κ) (t := t)) hψdiff hψ_int_gauss hψ'_int_gauss
        hxψ_int_gauss

  have hibp :
      (∫ ω, (Z ω) * (ψ (κ := κ) (t := t) (Z ω)) ∂P) =
        (∫ ω, deriv (ψ (κ := κ) (t := t)) (Z ω) ∂P) := by
    have hL :
        (∫ ω, (Z ω) * (ψ (κ := κ) (t := t) (Z ω)) ∂P) =
          ∫ x, x * (ψ (κ := κ) (t := t) x) ∂μ := by
      have hmap_int :
          (∫ x, x * (ψ (κ := κ) (t := t) x) ∂Measure.map Z P) =
            ∫ ω, (Z ω) * (ψ (κ := κ) (t := t) (Z ω)) ∂P := by
        simpa [mul_assoc, Function.comp] using
          (MeasureTheory.integral_map (μ := P) (φ := Z) hZ_meas
            (f := fun x : ℝ => x * (ψ (κ := κ) (t := t) x)) hxψ_aesm)
      calc
        (∫ ω, (Z ω) * (ψ (κ := κ) (t := t) (Z ω)) ∂P) =
            (∫ x, x * (ψ (κ := κ) (t := t) x) ∂Measure.map Z P) := by
              simpa using hmap_int.symm
        _ = ∫ x, x * (ψ (κ := κ) (t := t) x) ∂μ := by
              simpa [hmap]
    have hR :
        (∫ ω, deriv (ψ (κ := κ) (t := t)) (Z ω) ∂P) =
          ∫ x, deriv (ψ (κ := κ) (t := t)) x ∂μ := by
      have hmap_int :
          (∫ x, deriv (ψ (κ := κ) (t := t)) x ∂Measure.map Z P) =
            ∫ ω, deriv (ψ (κ := κ) (t := t)) (Z ω) ∂P := by
        simpa [Function.comp] using
          (MeasureTheory.integral_map (μ := P) (φ := Z) hZ_meas
            (f := fun x : ℝ => deriv (ψ (κ := κ) (t := t)) x) hψ'_aesm)
      calc
        (∫ ω, deriv (ψ (κ := κ) (t := t)) (Z ω) ∂P) =
            (∫ x, deriv (ψ (κ := κ) (t := t)) x ∂Measure.map Z P) := by
              simpa using hmap_int.symm
        _ = ∫ x, deriv (ψ (κ := κ) (t := t)) x ∂μ := by
              simpa [hmap]
    calc
      (∫ ω, (Z ω) * (ψ (κ := κ) (t := t) (Z ω)) ∂P) =
          ∫ x, x * (ψ (κ := κ) (t := t) x) ∂μ := hL
      _ = ∫ x, deriv (ψ (κ := κ) (t := t)) x ∂μ := hibp_gauss
      _ = (∫ ω, deriv (ψ (κ := κ) (t := t)) (Z ω) ∂P) := hR.symm
  have hibp' :
      (∫ ω, (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω)) ∂P) =
        (∫ ω, (deriv (ψ (κ := κ) (t := t)) (Z ω)) ∂P) := by
    simpa [ψ, U] using hibp
  rw [hibp']
  have hderiv_point :
      (fun ω => deriv (ψ (κ := κ) (t := t)) (Z ω)) =
        fun ω =>
          -(Real.sqrt (t / (1 - t)))
            * deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω) := by
    funext ω
    simpa [ψ, U] using
      (deriv_ψ (κ := κ) (t := t) (ht := ht) (z := Z ω))
  -- Pull out the constant scalar.
  calc
    (∫ ω : Ω, deriv (ψ (κ := κ) (t := t)) (Z ω) ∂P) =
        ∫ ω : Ω,
          -(Real.sqrt (t / (1 - t))
            * deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) ∂P := by
          simp [hderiv_point, mul_assoc]
    _ =
        -(∫ ω : Ω,
            (Real.sqrt (t / (1 - t)))
              * deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω) ∂P) := by
          simpa using
            (MeasureTheory.integral_neg (μ := P)
              (f := fun ω : Ω =>
                (Real.sqrt (t / (1 - t)))
                  * deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)))
    _ =
        -((Real.sqrt (t / (1 - t)))
          * ∫ ω : Ω, deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω) ∂P) := by
          simp [MeasureTheory.integral_const_mul]

lemma deriv_B_step4
    (hZ_gaussian :
      Measure.map Z P =
        ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (h_deriv_under_expect :
      HasDerivAt
        (fun s => 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
        (𝔼 (P := P) (fun ω =>
          (deriv h (U (κ := κ) (Z := Z) t ω))
            * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
        t)
    (integrable_h : Integrable (fun ω => h (U (κ := κ) (Z := Z) t ω)) P)
    (integrable_Uh :
      Integrable (fun ω =>
        (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P)
    (integrable_Zh :
      Integrable (fun ω =>
        (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P)
    (integrable_ψZ : Integrable (fun ω => ψ (κ := κ) (t := t) (Z ω)) P)
    (integrable_deriv_ψZ :
      Integrable (fun ω => deriv (ψ (κ := κ) (t := t)) (Z ω)) P)
    (integrable_hdd :
      Integrable (fun ω => deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) P) :
    deriv (fun s => B (P := P) (κ := κ) (Z := Z) s) t =
      𝔼 (P := P) (fun ω =>
        -h (U (κ := κ) (Z := Z) t ω)
          + (1 / 2) * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))
          + (1 / 2) * (deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω))) := by
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2

  have h3 :=
    deriv_B_step3 (P := P) (Z := Z) (κ := κ) (t := t) (ht := ht)
      (h_deriv_under_expect := h_deriv_under_expect)
      (integrable_h := integrable_h) (integrable_Uh := integrable_Uh) (integrable_Zh := integrable_Zh)
  have hZ :=
    Z_term_eq (P := P) (Z := Z) (κ := κ) (t := t)
      (hZ_gaussian := hZ_gaussian) (ht := ht) (integrable_Zh := integrable_Zh)
      (integrable_ψZ := integrable_ψZ) (integrable_deriv_ψZ := integrable_deriv_ψZ)

  -- Substitute the evaluated `Z`-term into Step 3.
  rw [h3]
  rw [hZ]
  -- Simplify the signs.
  ring_nf

  -- Simplify the product of constants to `1/2`.
  have hsqrt_t : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht0)
  have hsqrt_1mt : Real.sqrt (1 - t) ≠ 0 := by
    have : (0 : ℝ) < 1 - t := sub_pos.mpr ht1
    exact ne_of_gt (Real.sqrt_pos.2 this)
  have ht0le : 0 ≤ t := le_of_lt ht0
  have hsqrt_div : Real.sqrt (t / (1 - t)) = Real.sqrt t / Real.sqrt (1 - t) := by
    simpa using (Real.sqrt_div ht0le (1 - t))
  have hcoeff :
      (Real.sqrt (1 - t) / (2 * Real.sqrt t)) * Real.sqrt (t / (1 - t)) = (1 / 2 : ℝ) := by
    rw [hsqrt_div]
    field_simp [hsqrt_t, hsqrt_1mt]

  -- Combine the two expectations into a single expectation.
  have integrable_neg_h : Integrable (fun ω => -h (U (κ := κ) (Z := Z) t ω)) P :=
    integrable_h.neg
  have integrable_half_Uh :
      Integrable (fun ω =>
        (1 / 2) * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integrable_Uh.const_mul (1 / 2 : ℝ))
  have integrable_A :
      Integrable (fun ω =>
        -h (U (κ := κ) (Z := Z) t ω)
          + (1 / 2) * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P :=
    integrable_neg_h.add integrable_half_Uh
  have integrable_half_hdd :
      Integrable (fun ω =>
        (1 / 2) * deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) P :=
    integrable_hdd.const_mul (1 / 2 : ℝ)

  -- Unfold expectations to integrals and use linearity.
  simp [𝔼]
  have hcoeff_one :
      Real.sqrt (1 - t) * (Real.sqrt t)⁻¹ * Real.sqrt (t * (1 - t)⁻¹) = (1 : ℝ) := by
    have hs : Real.sqrt (t * (1 - t)⁻¹) = Real.sqrt t / Real.sqrt (1 - t) := by
      simpa [div_eq_mul_inv] using hsqrt_div
    rw [hs]
    field_simp [hsqrt_t, hsqrt_1mt]
  have hcoeff_one' :
      (Real.sqrt t)⁻¹ * Real.sqrt (1 - t) * Real.sqrt (t * (1 - t)⁻¹) = (1 : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcoeff_one
  have integrable_Uh2inv :
      Integrable (fun ω =>
        (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω)) * (2⁻¹ : ℝ)) P := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integrable_Uh.const_mul (2⁻¹ : ℝ))
  have integrable_A2inv :
      Integrable (fun ω =>
        -h (U (κ := κ) (Z := Z) t ω)
          + (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω)) * (2⁻¹ : ℝ)) P := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integrable_neg_h.add integrable_Uh2inv)
  have integrable_hdd2inv :
      Integrable (fun ω =>
        deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω) * (2⁻¹ : ℝ)) P := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (integrable_hdd.const_mul (2⁻¹ : ℝ))
  rw [MeasureTheory.integral_add integrable_A2inv integrable_hdd2inv]
  simp [MeasureTheory.integral_const_mul, hcoeff_one', mul_assoc, mul_left_comm, mul_comm]

/-! Step 5 -/

/-- Bundle of the integrability hypotheses used in Steps 3–6. -/
structure IntegrabilityAssumptions (t : ℝ) : Prop where
  integrable_h : Integrable (fun ω => h (U (κ := κ) (Z := Z) t ω)) P
  integrable_Uh :
    Integrable (fun ω =>
      (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P
  integrable_Zh :
    Integrable (fun ω =>
      (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P
  integrable_ψZ : Integrable (fun ω => ψ (κ := κ) (t := t) (Z ω)) P
  integrable_deriv_ψZ :
    Integrable (fun ω => deriv (ψ (κ := κ) (t := t)) (Z ω)) P
  integrable_hdd :
    Integrable (fun ω =>
      deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) P

lemma deriv_h (u : ℝ) :
    deriv h u = 2 * (E u) * (deriv E u) := by
  have hEq : h = E * E := by
    funext x
    simp [h, pow_two]
  have hE : DifferentiableAt ℝ E u :=
    differentiableAt_E (u := u)
  have hpow : deriv (E * E) u = 2 * (E u) * (deriv E u) := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (deriv_pow (f := E) (x := u) hE 2)
  simpa [hEq] using hpow

lemma deriv2_h (u : ℝ) :
    deriv (fun x => deriv h x) u =
      2 * (deriv E u) ^ 2 + 2 * (E u) * (deriv (fun x => deriv E x) u) := by
  have hfun : (fun x => deriv h x) = fun x => 2 * (E x) * (deriv E x) := by
    funext x
    simpa using (deriv_h (u := x))
  have hE : DifferentiableAt ℝ E u :=
    differentiableAt_E (u := u)
  have hfunE : (fun x => deriv E x) = fun x => (E x) ^ 2 - x * E x := by
    funext x
    simpa using (deriv_E (u := x))
  have hderivE : DifferentiableAt ℝ (fun x => deriv E x) u := by
    have hPow : DifferentiableAt ℝ (fun x => (E x) ^ 2) u := by
      simpa using hE.pow 2
    have hMul : DifferentiableAt ℝ (fun x => x * E x) u := by
      simpa using (differentiableAt_id.mul hE)
    have hRHS : DifferentiableAt ℝ (fun x => (E x) ^ 2 - x * E x) u := by
      simpa using hPow.sub hMul
    simpa [hfunE] using hRHS
  simp [hfun, pow_two, deriv_mul, deriv_const_mul, hE, hderivE, mul_assoc, mul_left_comm, mul_comm]
  ring_nf



  /-- Under the standard Gaussian law for Z, the integrability hypotheses used in Steps 3–6
  follow automatically from the Mills bound and finite Gaussian moments. -/
  lemma integrabilityAssumptions_of_gaussian
      (hZ_gaussian :
        Measure.map Z P =
          ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      IntegrabilityAssumptions (P := P) (Z := Z) (κ := κ) t := by
    have hZ_meas : AEMeasurable Z P :=
      aemeasurable_Z_of_gaussian (P := P) (Z := Z) (hZ_gaussian := hZ_gaussian)
    have hC1 : (1 : ℝ) ≤ C_mills := le_max_right _ _
    have hC0 : 0 ≤ C_mills := by nlinarith [hC1]

    let b : ℝ → ℝ := fun u => |u| + C_mills

    have hb_nonneg : ∀ u : ℝ, 0 ≤ b u := by
      intro u
      dsimp [b]
      exact add_nonneg (abs_nonneg u) hC0

    have hb_ge_one : ∀ u : ℝ, (1 : ℝ) ≤ b u := by
      intro u
      dsimp [b]
      nlinarith [abs_nonneg u, hC1]

    have habs_le_b : ∀ u : ℝ, |u| ≤ b u := by
      intro u
      dsimp [b]
      nlinarith [hC0]

    have hb_pow3_le_pow4 : ∀ u : ℝ, (b u) ^ 3 ≤ (b u) ^ 4 := by
      intro u
      have hb1 : (1 : ℝ) ≤ b u := hb_ge_one u
      have hb3 : 0 ≤ (b u) ^ 3 := by positivity
      have hmul : (b u) ^ 3 * 1 ≤ (b u) ^ 3 * b u :=
        mul_le_mul_of_nonneg_left hb1 hb3
      simpa [pow_succ, mul_assoc] using hmul

    have hb_pow2_le_pow4 : ∀ u : ℝ, (b u) ^ 2 ≤ (b u) ^ 4 := by
      intro u
      have hb1 : (1 : ℝ) ≤ b u := hb_ge_one u
      have hb0 : 0 ≤ b u := hb_nonneg u
      have hb2_ge_one : (1 : ℝ) ≤ (b u) ^ 2 := by
        have : (1 : ℝ) * 1 ≤ b u * b u := mul_le_mul hb1 hb1 (by norm_num) hb0
        simpa [pow_two] using this
      have hb2 : 0 ≤ (b u) ^ 2 := by positivity
      have hmul : (b u) ^ 2 * 1 ≤ (b u) ^ 2 * (b u) ^ 2 :=
        mul_le_mul_of_nonneg_left hb2_ge_one hb2
      -- rewrite (b u)^2 * (b u)^2 as (b u)^4
      simpa [mul_assoc, (pow_add (b u) 2 2).symm] using hmul

    have E_nonneg : ∀ u : ℝ, 0 ≤ E u := by
      intro u
      unfold E
      have hφ : 0 ≤ φ u := (φ_pos (u := u)).le
      have hΦ : 0 ≤ Φbar u := (Φbar_pos (u := u)).le
      exact div_nonneg hφ hΦ

    have abs_E_le : ∀ u : ℝ, |E u| ≤ b u := by
      intro u
      have hE : E u ≤ b u := by
        simpa [b] using (E_le_abs_add_C (u := u))
      simpa [abs_of_nonneg (E_nonneg u)] using hE

    have abs_deriv_E_le : ∀ u : ℝ, |deriv E u| ≤ 2 * (b u) ^ 2 := by
      intro u
      calc
        |deriv E u| = |(E u) ^ 2 - u * E u| := by simp [deriv_E (u := u)]
        _ = |(E u) ^ 2 + (-(u * E u))| := by simp [sub_eq_add_neg]
        _ ≤ |(E u) ^ 2| + |-(u * E u)| := abs_add_le _ _
        _ = |E u| ^ 2 + |u| * |E u| := by
          simp [abs_pow, abs_mul]
        _ ≤ (b u) ^ 2 + (b u) ^ 2 := by
          have hE2 : |E u| ^ 2 ≤ (b u) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg (E u)) (abs_E_le u) 2
          have huE : |u| * |E u| ≤ (b u) ^ 2 := by
            have hb0 : 0 ≤ b u := hb_nonneg u
            have hmul : |u| * |E u| ≤ b u * b u :=
              mul_le_mul (habs_le_b u) (abs_E_le u) (abs_nonneg (E u)) hb0
            simpa [pow_two] using hmul
          nlinarith [hE2, huE]
        _ = 2 * (b u) ^ 2 := by ring

    have abs_deriv_h_le : ∀ u : ℝ, |deriv h u| ≤ 4 * (b u) ^ 3 := by
      intro u
      have hdh : deriv h u = 2 * (E u) * (deriv E u) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using (deriv_h (u := u))
      calc
        |deriv h u| = |2 * (E u) * (deriv E u)| := by simp [hdh]
        _ = 2 * |E u| * |deriv E u| := by
          simp [abs_mul, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ 2 * (b u) * (2 * (b u) ^ 2) := by
          gcongr
          · exact abs_E_le u
          · exact abs_deriv_E_le u
        _ = 4 * (b u) ^ 3 := by ring_nf

    have abs_u_mul_deriv_h_le : ∀ u : ℝ, |u * deriv h u| ≤ 4 * (b u) ^ 4 := by
      intro u
      have hb0 : 0 ≤ b u := hb_nonneg u
      have hu : |u| ≤ b u := habs_le_b u
      calc
        |u * deriv h u| = |u| * |deriv h u| := by simp [abs_mul]
        _ ≤ |u| * (4 * (b u) ^ 3) := by
          gcongr
          exact abs_deriv_h_le u
        _ ≤ (b u) * (4 * (b u) ^ 3) := by
          gcongr
        _ = 4 * (b u) ^ 4 := by ring_nf

    have abs_deriv2_E_le : ∀ u : ℝ, |deriv (fun x => deriv E x) u| ≤ 7 * (b u) ^ 3 := by
      intro u
      have h2 :
          deriv (fun x => deriv E x) u =
            2 * (E u) * (deriv E u) - (E u) - u * (deriv E u) := by
        simpa using (deriv2_E (u := u))
      -- Triangle inequality: peel off the last term, then the middle one.
      have htri1 :
          |2 * (E u) * (deriv E u) - (E u) - u * (deriv E u)| ≤
            |2 * (E u) * (deriv E u) - (E u)| + |u * (deriv E u)| := by
        simpa [sub_eq_add_neg, add_assoc] using
          (abs_add_le (2 * (E u) * (deriv E u) - (E u)) (-(u * deriv E u)))
      have htri2 :
          |2 * (E u) * (deriv E u) - (E u)| ≤ |2 * (E u) * (deriv E u)| + |E u| := by
        simpa [sub_eq_add_neg] using
          (abs_add_le (2 * (E u) * (deriv E u)) (-(E u)))
      have hterm1 : |2 * (E u) * (deriv E u)| ≤ 4 * (b u) ^ 3 := by
        calc
          |2 * (E u) * (deriv E u)| = 2 * |E u| * |deriv E u| := by
            simp [abs_mul, mul_assoc, mul_left_comm, mul_comm]
          _ ≤ 2 * (b u) * (2 * (b u) ^ 2) := by
            gcongr
            · exact abs_E_le u
            · exact abs_deriv_E_le u
          _ = 4 * (b u) ^ 3 := by ring_nf
      have hterm3 : |u * deriv E u| ≤ 2 * (b u) ^ 3 := by
        have hb0 : 0 ≤ b u := hb_nonneg u
        calc
          |u * deriv E u| = |u| * |deriv E u| := by simp [abs_mul]
          _ ≤ b u * (2 * (b u) ^ 2) := by
            gcongr
            · exact habs_le_b u
            · exact abs_deriv_E_le u
          _ = 2 * (b u) ^ 3 := by ring_nf
      have hterm2 : |E u| ≤ (b u) ^ 3 := by
        exact le_trans (abs_E_le u) (by
          --  u ≤ (b u)^3 since  u ≥ 1.
          have hb1 : (1 : ℝ) ≤ b u := hb_ge_one u
          have hb0 : 0 ≤ b u := hb_nonneg u
          have hb_sq : b u ≤ (b u) ^ 2 := by
            have hmul : b u * 1 ≤ b u * b u := mul_le_mul_of_nonneg_left hb1 hb0
            simpa [pow_two] using hmul
          have hb_cu : (b u) ^ 2 ≤ (b u) ^ 3 := by
            have hb2 : 0 ≤ (b u) ^ 2 := by positivity
            have hmul : (b u) ^ 2 * 1 ≤ (b u) ^ 2 * b u := mul_le_mul_of_nonneg_left hb1 hb2
            simpa [pow_succ, mul_assoc] using hmul
          exact le_trans hb_sq hb_cu)
      have : |2 * (E u) * (deriv E u) - (E u) - u * (deriv E u)| ≤ 7 * (b u) ^ 3 := by
        calc
          |2 * (E u) * (deriv E u) - (E u) - u * (deriv E u)|
              ≤ |2 * (E u) * (deriv E u) - (E u)| + |u * (deriv E u)| := htri1
          _ ≤ (|2 * (E u) * (deriv E u)| + |E u|) + |u * (deriv E u)| := by
            exact add_le_add_left htri2 _
          _ ≤ (4 * (b u) ^ 3 + (b u) ^ 3) + 2 * (b u) ^ 3 := by
            have h12 :
                |2 * (E u) * (deriv E u)| + |E u| ≤ 4 * (b u) ^ 3 + (b u) ^ 3 :=
              add_le_add hterm1 hterm2
            exact add_le_add h12 hterm3
          _ = 7 * (b u) ^ 3 := by ring
      simpa [h2] using this

    have abs_deriv2_h_le : ∀ u : ℝ, |deriv (fun x => deriv h x) u| ≤ 22 * (b u) ^ 4 := by
      intro u
      have h2h :
          deriv (fun x => deriv h x) u =
            2 * (deriv E u) ^ 2 + 2 * (E u) * (deriv (fun x => deriv E x) u) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using (deriv2_h (u := u))
      have hterm1 : |2 * (deriv E u) ^ 2| ≤ 8 * (b u) ^ 4 := by
        have hdu : |deriv E u| ≤ 2 * (b u) ^ 2 := abs_deriv_E_le u
        have hsq : |deriv E u| ^ 2 ≤ (2 * (b u) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg (deriv E u)) hdu 2
        calc
          |2 * (deriv E u) ^ 2| = 2 * |(deriv E u) ^ 2| := by simp [abs_mul]
          _ = 2 * (|deriv E u| ^ 2) := by simp [abs_pow]
          _ ≤ 2 * ((2 * (b u) ^ 2) ^ 2) := by gcongr
          _ = 8 * (b u) ^ 4 := by ring_nf
      have hterm2 : |2 * (E u) * (deriv (fun x => deriv E x) u)| ≤ 14 * (b u) ^ 4 := by
        calc
          |2 * (E u) * (deriv (fun x => deriv E x) u)| =
              2 * |E u| * |deriv (fun x => deriv E x) u| := by
                simp [abs_mul, mul_assoc, mul_left_comm, mul_comm]
          _ ≤ 2 * (b u) * (7 * (b u) ^ 3) := by
                gcongr
                · exact abs_E_le u
                · exact abs_deriv2_E_le u
          _ = 14 * (b u) ^ 4 := by ring_nf
      have : |deriv (fun x => deriv h x) u| ≤ 22 * (b u) ^ 4 := by
        calc
          |deriv (fun x => deriv h x) u| =
              |2 * (deriv E u) ^ 2 + 2 * (E u) * (deriv (fun x => deriv E x) u)| := by
                simp [h2h]
          _ ≤ |2 * (deriv E u) ^ 2| + |2 * (E u) * (deriv (fun x => deriv E x) u)| :=
                abs_add_le _ _
          _ ≤ 8 * (b u) ^ 4 + 14 * (b u) ^ 4 := by
                gcongr
          _ = 22 * (b u) ^ 4 := by ring
      exact this

    -- Finite 4th moment for Z, hence for the affine transform U_t.
    have hZ4 : MemLp Z (4 : ℝ≥0∞) P := by
      have hid : MemLp (id : ℝ → ℝ) (4 : ℝ≥0∞)
          (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))) := by
        simpa using
          (ProbabilityTheory.memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (4 : ℝ≥0∞)) (by simp))
      have hid_map : MemLp (id : ℝ → ℝ) (4 : ℝ≥0∞) (Measure.map Z P) := by
        simpa [hZ_gaussian] using hid
      have hcomp : MemLp ((id : ℝ → ℝ) ∘ Z) (4 : ℝ≥0∞) P :=
        (memLp_map_measure_iff (μ := P) (f := Z) (g := (id : ℝ → ℝ)) (p := (4 : ℝ≥0∞))
              (hg := measurable_id.aestronglyMeasurable) (hf := hZ_meas)).1 hid_map
      simpa [Function.comp] using hcomp

    have hU4 : MemLp (fun ω => U (κ := κ) (Z := Z) t ω) (4 : ℝ≥0∞) P := by
      have hκ : MemLp (fun _ : Ω => κ) (4 : ℝ≥0∞) P := by
        simpa using (memLp_const (μ := P) (c := κ) (p := (4 : ℝ≥0∞)))
      have hZscaled : MemLp (fun ω => Real.sqrt t * Z ω) (4 : ℝ≥0∞) P :=
        hZ4.const_mul (Real.sqrt t)
      have hnum : MemLp (fun ω => κ - Real.sqrt t * Z ω) (4 : ℝ≥0∞) P := by
        simpa using hκ.sub hZscaled
      simpa [U, div_eq_mul_inv] using hnum.mul_const ((Real.sqrt (1 - t))⁻¹)

    have hb4_int : Integrable (fun ω => (b (U (κ := κ) (Z := Z) t ω)) ^ 4) P := by
      have habsU : MemLp (fun ω => |U (κ := κ) (Z := Z) t ω|) (4 : ℝ≥0∞) P := by
        simpa [Real.norm_eq_abs] using hU4.norm
      have hC : MemLp (fun _ : Ω => C_mills) (4 : ℝ≥0∞) P := by
        simpa using (memLp_const (μ := P) (c := C_mills) (p := (4 : ℝ≥0∞)))
      have hb_memLp : MemLp (fun ω => b (U (κ := κ) (Z := Z) t ω)) (4 : ℝ≥0∞) P := by
        simpa [b] using (habsU.add hC)
      have hb_int_norm : Integrable (fun ω => ‖b (U (κ := κ) (Z := Z) t ω)‖ ^ 4) P :=
        hb_memLp.integrable_norm_pow (p := 4) (by decide)
      have hb_int_abs : Integrable (fun ω => |b (U (κ := κ) (Z := Z) t ω)| ^ 4) P := by
        simpa [Real.norm_eq_abs] using hb_int_norm
      have hb_eq :
          (fun ω => |b (U (κ := κ) (Z := Z) t ω)| ^ 4) =
            (fun ω => (b (U (κ := κ) (Z := Z) t ω)) ^ 4) := by
        funext ω
        have hb0 : 0 ≤ b (U (κ := κ) (Z := Z) t ω) := hb_nonneg _
        simp [abs_of_nonneg hb0]
      simpa [hb_eq] using hb_int_abs

    have hU_meas : AEMeasurable (fun ω => U (κ := κ) (Z := Z) t ω) P := by
      have hZmul : AEMeasurable (fun ω => Real.sqrt t * Z ω) P :=
        hZ_meas.const_mul (Real.sqrt t)
      have hnum : AEMeasurable (fun ω => κ - Real.sqrt t * Z ω) P := by
        simpa using (aemeasurable_const.sub hZmul)
      simpa [U] using hnum.div_const (Real.sqrt (1 - t))

    -- Measurability of the deterministic functions.
    have hcont_E : Continuous E := by
      refine continuous_iff_continuousAt.2 ?_
      intro u
      exact (differentiableAt_E (u := u)).continuousAt
    have hmeas_E : Measurable E := hcont_E.measurable
    have hmeas_h : Measurable h := by
      simpa [h] using hmeas_E.pow_const (2 : ℕ)
    have hmeas_deriv_h : Measurable (fun u : ℝ => deriv h u) := by
      simpa using (measurable_deriv h)
    have hmeas_hdd : Measurable (fun u : ℝ => deriv (fun x => deriv h x) u) := by
      simpa using (measurable_deriv (fun x => deriv h x))

    have integrable_h : Integrable (fun ω => h (U (κ := κ) (Z := Z) t ω)) P := by
      have hf_meas : AEStronglyMeasurable (fun ω => h (U (κ := κ) (Z := Z) t ω)) P :=
        (hmeas_h.comp_aemeasurable hU_meas).aestronglyMeasurable
      have hle : ∀ᵐ ω ∂P, ‖h (U (κ := κ) (Z := Z) t ω)‖ ≤ (b (U (κ := κ) (Z := Z) t ω)) ^ 4 := by
        refine ae_of_all _ (fun ω => ?_)
        set u : ℝ := U (κ := κ) (Z := Z) t ω
        have hb0 : 0 ≤ b u := hb_nonneg u
        have hE0 : 0 ≤ E u := E_nonneg u
        have hE_le : E u ≤ b u := by
          simpa [b] using (E_le_abs_add_C (u := u))
        have hE_sq : (E u) ^ 2 ≤ (b u) ^ 2 := by
          have : E u * E u ≤ b u * b u := mul_le_mul hE_le hE_le hE0 hb0
          simpa [pow_two] using this
        have hb2_le : (b u) ^ 2 ≤ (b u) ^ 4 := hb_pow2_le_pow4 u
        have hhu : h u ≤ (b u) ^ 4 := by
          have : h u ≤ (b u) ^ 2 := by simpa [h] using hE_sq
          exact le_trans this hb2_le
        have hhnonneg : 0 ≤ h u := by
          have : 0 ≤ (E u) ^ 2 := pow_nonneg hE0 2
          simpa [h] using this
        have : ‖h u‖ ≤ (b u) ^ 4 := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hhnonneg, u] using hhu
        simpa [u] using this
      exact Integrable.mono' hb4_int hf_meas hle

    have integrable_deriv_hU : Integrable (fun ω => deriv h (U (κ := κ) (Z := Z) t ω)) P := by
      have hf_meas : AEStronglyMeasurable (fun ω => deriv h (U (κ := κ) (Z := Z) t ω)) P :=
        (hmeas_deriv_h.comp_aemeasurable hU_meas).aestronglyMeasurable
      have hg : Integrable (fun ω => 4 * (b (U (κ := κ) (Z := Z) t ω)) ^ 4) P :=
        hb4_int.const_mul 4
      have hle : ∀ᵐ ω ∂P, ‖deriv h (U (κ := κ) (Z := Z) t ω)‖ ≤ 4 * (b (U (κ := κ) (Z := Z) t ω)) ^ 4 := by
        refine ae_of_all _ (fun ω => ?_)
        set u : ℝ := U (κ := κ) (Z := Z) t ω
        have h_abs : |deriv h u| ≤ 4 * (b u) ^ 3 := abs_deriv_h_le u
        have hb34 : (b u) ^ 3 ≤ (b u) ^ 4 := hb_pow3_le_pow4 u
        have h_abs' : |deriv h u| ≤ 4 * (b u) ^ 4 := by
          have : 4 * (b u) ^ 3 ≤ 4 * (b u) ^ 4 := by
            have : 0 ≤ (4 : ℝ) := by norm_num
            exact mul_le_mul_of_nonneg_left hb34 this
          exact le_trans h_abs this
        simpa [Real.norm_eq_abs, u] using h_abs'
      exact Integrable.mono' hg hf_meas hle

    have integrable_Uh :
        Integrable (fun ω => (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P := by
      have hf_meas : AEStronglyMeasurable (fun ω =>
          (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P := by
        have hdh_meas : AEMeasurable (fun ω => deriv h (U (κ := κ) (Z := Z) t ω)) P :=
          hmeas_deriv_h.comp_aemeasurable hU_meas
        exact (hU_meas.mul hdh_meas).aestronglyMeasurable
      have hg : Integrable (fun ω => 4 * (b (U (κ := κ) (Z := Z) t ω)) ^ 4) P :=
        hb4_int.const_mul 4
      have hle : ∀ᵐ ω ∂P,
          ‖(U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))‖ ≤
            4 * (b (U (κ := κ) (Z := Z) t ω)) ^ 4 := by
        refine ae_of_all _ (fun ω => ?_)
        set u : ℝ := U (κ := κ) (Z := Z) t ω
        have : |u * deriv h u| ≤ 4 * (b u) ^ 4 := abs_u_mul_deriv_h_le u
        simpa [Real.norm_eq_abs, u] using this
      exact Integrable.mono' hg hf_meas hle

    have integrable_hdd :
        Integrable (fun ω => deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) P := by
      have hf_meas : AEStronglyMeasurable
          (fun ω => deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) P :=
        (hmeas_hdd.comp_aemeasurable hU_meas).aestronglyMeasurable
      have hg : Integrable (fun ω => 22 * (b (U (κ := κ) (Z := Z) t ω)) ^ 4) P :=
        hb4_int.const_mul 22
      have hle : ∀ᵐ ω ∂P,
          ‖deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)‖ ≤
            22 * (b (U (κ := κ) (Z := Z) t ω)) ^ 4 := by
        refine ae_of_all _ (fun ω => ?_)
        set u : ℝ := U (κ := κ) (Z := Z) t ω
        have : |deriv (fun x => deriv h x) u| ≤ 22 * (b u) ^ 4 := abs_deriv2_h_le u
        simpa [Real.norm_eq_abs, u] using this
      exact Integrable.mono' hg hf_meas hle

    have integrable_ψZ : Integrable (fun ω => ψ (κ := κ) (t := t) (Z ω)) P := by
      simpa [ψ, U] using integrable_deriv_hU

    have integrable_deriv_ψZ :
        Integrable (fun ω => deriv (ψ (κ := κ) (t := t)) (Z ω)) P := by
      -- Use the chain rule lemma deriv_ψ.
      have hEq : (fun ω => deriv (ψ (κ := κ) (t := t)) (Z ω)) =
          fun ω =>
            -(Real.sqrt (t / (1 - t))) *
              deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω) := by
        funext ω
        simpa [ψ, U] using (deriv_ψ (κ := κ) (t := t) (ht := ht) (z := Z ω))
      have : Integrable (fun ω =>
          -(Real.sqrt (t / (1 - t))) *
            deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) P :=
        integrable_hdd.const_mul (-(Real.sqrt (t / (1 - t))))
      simpa [hEq] using this

    have integrable_Zh :
        Integrable (fun ω => (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P := by
      have ht0 : 0 < t := ht.1
      have hsqrt_t_ne : Real.sqrt t ≠ 0 := by
        exact ne_of_gt (Real.sqrt_pos.2 ht0)
      have hZ_eq : ∀ ω, Z ω = (κ - Real.sqrt (1 - t) * U (κ := κ) (Z := Z) t ω) / Real.sqrt t := by
        intro ω
        have h1mt : 0 < 1 - t := sub_pos.mpr ht.2
        have hsqrt_1mt_ne : Real.sqrt (1 - t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1mt)
        have hU_mul : Real.sqrt (1 - t) * U (κ := κ) (Z := Z) t ω = κ - Real.sqrt t * Z ω := by
          unfold U
          calc
            Real.sqrt (1 - t) * ((κ - Real.sqrt t * Z ω) / Real.sqrt (1 - t))
                = Real.sqrt (1 - t) * (κ - Real.sqrt t * Z ω) / Real.sqrt (1 - t) := by
                    simpa using
                      (mul_div_assoc (Real.sqrt (1 - t)) (κ - Real.sqrt t * Z ω) (Real.sqrt (1 - t))).symm
            _ = κ - Real.sqrt t * Z ω := by
                    simpa using
                      (mul_div_cancel_left₀ (b := (κ - Real.sqrt t * Z ω)) (a := Real.sqrt (1 - t)) hsqrt_1mt_ne)
        have hz : Real.sqrt t * Z ω = κ - Real.sqrt (1 - t) * U (κ := κ) (Z := Z) t ω := by
          linarith
        have hz' : Z ω * Real.sqrt t = κ - Real.sqrt (1 - t) * U (κ := κ) (Z := Z) t ω := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hz
        field_simp [hsqrt_t_ne]
        simpa using hz'
      have hrewrite : (fun ω => (Z ω) * deriv h (U (κ := κ) (Z := Z) t ω)) =
          fun ω => (κ / Real.sqrt t) * deriv h (U (κ := κ) (Z := Z) t ω)
                - (Real.sqrt (1 - t) / Real.sqrt t) *
                    ((U (κ := κ) (Z := Z) t ω) * deriv h (U (κ := κ) (Z := Z) t ω)) := by
        funext ω
        have hz := hZ_eq ω
        rw [hz]
        field_simp [hsqrt_t_ne]
      have int1 : Integrable (fun ω => (κ / Real.sqrt t) * deriv h (U (κ := κ) (Z := Z) t ω)) P :=
        integrable_deriv_hU.const_mul (κ / Real.sqrt t)
      have int2 : Integrable (fun ω => (Real.sqrt (1 - t) / Real.sqrt t) *
            ((U (κ := κ) (Z := Z) t ω) * deriv h (U (κ := κ) (Z := Z) t ω))) P :=
        integrable_Uh.const_mul (Real.sqrt (1 - t) / Real.sqrt t)
      simpa [hrewrite] using int1.sub int2

    exact
      { integrable_h := integrable_h
        integrable_Uh := integrable_Uh
        integrable_Zh := integrable_Zh
        integrable_ψZ := integrable_ψZ
        integrable_deriv_ψZ := integrable_deriv_ψZ
        integrable_hdd := integrable_hdd }

/- Under the Gaussian law for Z and 	 ∈ (0,1), the differentiation-under-expectation hypothesis
for the integrand ω ↦ h (U_s ω) holds automatically. -/
set_option maxHeartbeats 2000000 in
lemma h_deriv_under_expect_of_gaussian
    (hZ_gaussian :
      Measure.map Z P =
        ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
      (𝔼 (P := P) (fun ω =>
        (deriv h (U (κ := κ) (Z := Z) t ω))
          * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
      t := by
  have hZ_meas : AEMeasurable Z P :=
    aemeasurable_Z_of_gaussian (P := P) (Z := Z) (hZ_gaussian := hZ_gaussian)
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2

  -- Choose a small ball around 	 contained in (0,1).
  let ε : ℝ := min (t / 2) ((1 - t) / 2)
  have ε_pos : 0 < ε := by
    have h1 : 0 < t / 2 := by nlinarith
    have h2 : 0 < (1 - t) / 2 := by
      have : 0 < 1 - t := sub_pos.mpr ht1
      nlinarith
    exact lt_min h1 h2

  have hs_mem_Ioo : ∀ {s : ℝ}, s ∈ Metric.ball t ε → s ∈ Set.Ioo (0 : ℝ) 1 := by
    intro s hs
    have hs' : dist s t < ε := (Metric.mem_ball.mp hs)
    have hsabs : |s - t| < ε := by simpa [Real.dist_eq] using hs'
    have hst : s - t < ε ∧ t - s < ε := (abs_sub_lt_iff).1 hsabs
    have hs_lt : s < t + ε := by linarith [hst.1]
    have hs_gt : t - ε < s := by linarith [hst.2]
    have hε_le_t : ε ≤ t / 2 := min_le_left _ _
    have hε_le_1t : ε ≤ (1 - t) / 2 := min_le_right _ _
    have hs_pos : 0 < s := by
      have ht_half : 0 < t / 2 := by nlinarith
      have ht2_le : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
      have : t / 2 < s := lt_of_le_of_lt ht2_le hs_gt
      exact lt_trans ht_half this
    have hs_one : s < 1 := by
      have : t + ε ≤ (1 + t) / 2 := by nlinarith [hε_le_1t]
      have : t + ε < 1 := lt_of_le_of_lt this (by nlinarith [ht1])
      exact lt_of_lt_of_le hs_lt (le_of_lt this)
    exact ⟨hs_pos, hs_one⟩

  -- Deterministic measurability facts for h and deriv h.
  have hcont_E : Continuous E := by
    refine continuous_iff_continuousAt.2 ?_
    intro u
    exact (differentiableAt_E (u := u)).continuousAt
  have hmeas_E : Measurable E := hcont_E.measurable
  have hmeas_h : Measurable h := by
    simpa [h] using hmeas_E.pow_const (2 : ℕ)
  have hmeas_deriv_h : Measurable (fun u : ℝ => deriv h u) := by
    simpa using (measurable_deriv h)

  have h_meas :
      ∀ᶠ s in nhds t, AEStronglyMeasurable (fun ω => h (U (κ := κ) (Z := Z) s ω)) P := by
    have hall : ∀ s : ℝ, AEStronglyMeasurable (fun ω => h (U (κ := κ) (Z := Z) s ω)) P := by
      intro s
      have hZmul : AEMeasurable (fun ω => Real.sqrt s * Z ω) P :=
        hZ_meas.const_mul (Real.sqrt s)
      have hnum : AEMeasurable (fun ω => κ - Real.sqrt s * Z ω) P := by
        simpa using (aemeasurable_const.sub hZmul)
      have hU_meas : AEMeasurable (fun ω => U (κ := κ) (Z := Z) s ω) P := by
        simpa [U] using hnum.div_const (Real.sqrt (1 - s))
      exact (hmeas_h.comp_aemeasurable hU_meas).aestronglyMeasurable
    refine (Filter.eventually_iff).2 ?_
    have hset :
        {s : ℝ | AEStronglyMeasurable (fun ω => h (U (κ := κ) (Z := Z) s ω)) P} = Set.univ := by
      ext s
      constructor
      · intro _; trivial
      · intro _; exact hall s
    simpa [hset] using (Filter.univ_mem : (Set.univ : Set ℝ) ∈ nhds t)

  have h_int :
      Integrable (fun ω => h (U (κ := κ) (Z := Z) t ω)) P :=
    (integrabilityAssumptions_of_gaussian (P := P) (Z := Z) (κ := κ) (t := t)
      (hZ_gaussian := hZ_gaussian) (ht := ht)).integrable_h

  have hF'_meas :
      AEStronglyMeasurable
        (fun ω =>
          (deriv h (U (κ := κ) (Z := Z) t ω))
            * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)) P := by
    have hZmul : AEMeasurable (fun ω => Real.sqrt t * Z ω) P :=
      hZ_meas.const_mul (Real.sqrt t)
    have hnum : AEMeasurable (fun ω => κ - Real.sqrt t * Z ω) P := by
      simpa using (aemeasurable_const.sub hZmul)
    have hU_meas : AEMeasurable (fun ω => U (κ := κ) (Z := Z) t ω) P := by
      simpa [U] using hnum.div_const (Real.sqrt (1 - t))
    have hdh_meas : AEMeasurable (fun ω => deriv h (U (κ := κ) (Z := Z) t ω)) P :=
      hmeas_deriv_h.comp_aemeasurable hU_meas
    have hUder_meas :
        AEMeasurable (fun ω => deriv (fun s => U (κ := κ) (Z := Z) s ω) t) P := by
      have hpoint :
          (fun ω => deriv (fun s => U (κ := κ) (Z := Z) s ω) t) =
            fun ω =>
              (U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))
                - (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t)) := by
        funext ω
        simpa using (deriv_U (Z := Z) (κ := κ) (t := t) (ht := ht) (ω := ω))
      have hUterm :
          AEMeasurable (fun ω => (U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))) P := by
        simpa using (hU_meas.div_const (2 * (1 - t)))
      have hZterm :
          AEMeasurable (fun ω => (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t))) P := by
        simpa using (hZ_meas.div_const (2 * Real.sqrt t * Real.sqrt (1 - t)))
      have hRHS :
          AEMeasurable
            (fun ω =>
              (U (κ := κ) (Z := Z) t ω) / (2 * (1 - t))
                - (Z ω) / (2 * Real.sqrt t * Real.sqrt (1 - t))) P := by
        simpa [sub_eq_add_neg] using (hUterm.add hZterm.neg)
      simpa [hpoint] using hRHS
    exact (hdh_meas.mul hUder_meas).aestronglyMeasurable

  have hC1 : (1 : ℝ) ≤ C_mills := le_max_right _ _
  have hC0 : 0 ≤ C_mills := by nlinarith [hC1]
  let b : ℝ → ℝ := fun u => |u| + C_mills

  have habs_u_le_b : ∀ u : ℝ, |u| ≤ b u := by
    intro u
    dsimp [b]
    nlinarith [abs_nonneg u, hC0]

  have abs_E_le_b : ∀ u : ℝ, |E u| ≤ b u := by
    intro u
    have hEu : E u ≤ b u := by
      simpa [b] using (E_le_abs_add_C (u := u))
    have hEnonneg : 0 ≤ E u := by
      have hφ : 0 ≤ φ u := (φ_pos (u := u)).le
      have hΦ : 0 ≤ Φbar u := (Φbar_pos (u := u)).le
      have : 0 ≤ φ u / Φbar u := div_nonneg hφ hΦ
      simpa [E] using this
    simpa [abs_of_nonneg hEnonneg] using hEu

  have abs_deriv_h_le : ∀ u : ℝ, |deriv h u| ≤ 4 * (b u) ^ 3 := by
    intro u
    have hdh : deriv h u = 2 * (E u) * (deriv E u) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (deriv_h (u := u))
    have habsDerE : |deriv E u| ≤ 2 * (b u) ^ 2 := by
      have hde : deriv E u = (E u) ^ 2 - u * E u := by
        simpa using (deriv_E (u := u))
      have hterm1 : |(E u) ^ 2| ≤ (b u) ^ 2 := by
        have : |E u| ^ 2 ≤ (b u) ^ 2 := pow_le_pow_left₀ (abs_nonneg (E u)) (abs_E_le_b u) 2
        simpa [abs_pow] using this
      have hterm2 : |u * E u| ≤ (b u) ^ 2 := by
        have hmul : |u| * |E u| ≤ b u * b u :=
          mul_le_mul (habs_u_le_b u) (abs_E_le_b u) (abs_nonneg (E u)) (by
            dsimp [b]; exact add_nonneg (abs_nonneg u) hC0)
        simpa [abs_mul, pow_two] using hmul
      have htri : |(E u) ^ 2 - u * E u| ≤ (b u) ^ 2 + (b u) ^ 2 := by
        have hmain : |(E u) ^ 2 - u * E u| ≤ (E u) ^ 2 + |u| * |E u| := by
          have habs_sq : |(E u) ^ 2| = (E u) ^ 2 := by
            simp [abs_of_nonneg (sq_nonneg (E u))]
          have habs_neg : |-(u * E u)| = |u| * |E u| := by
            simp [abs_mul]
          have h := abs_add_le ((E u) ^ 2) (-(u * E u))
          have hR : |(E u) ^ 2| + |-(u * E u)| ≤ (E u) ^ 2 + |u| * |E u| := by
            simpa [habs_sq, habs_neg]
          have h2 : |(E u) ^ 2 + -(u * E u)| ≤ (E u) ^ 2 + |u| * |E u| :=
            le_trans h hR
          simpa [sub_eq_add_neg] using h2
        have hterm1' : (E u) ^ 2 ≤ (b u) ^ 2 := by
          have habs_sq : |(E u) ^ 2| = (E u) ^ 2 := by
            simp [abs_of_nonneg (sq_nonneg (E u))]
          simpa [habs_sq] using hterm1
        have hterm2' : |u| * |E u| ≤ (b u) ^ 2 := by
          simpa [abs_mul] using hterm2
        exact le_trans hmain (add_le_add hterm1' hterm2')
      have : |(E u) ^ 2 - u * E u| ≤ 2 * (b u) ^ 2 := by
        have : (b u) ^ 2 + (b u) ^ 2 = 2 * (b u) ^ 2 := by ring
        simpa [this] using htri
      simpa [hde] using this
    calc
      |deriv h u| = |2 * (E u) * (deriv E u)| := by simp [hdh]
      _ = 2 * |E u| * |deriv E u| := by simp [abs_mul, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ 2 * (b u) * (2 * (b u) ^ 2) := by
        have hb0 : 0 ≤ b u := by
          dsimp [b]
          exact add_nonneg (abs_nonneg u) hC0
        have hmul :
            |E u| * |deriv E u| ≤ b u * (2 * (b u) ^ 2) :=
          mul_le_mul (abs_E_le_b u) habsDerE (abs_nonneg _) hb0
        have htwo :
            2 * (|E u| * |deriv E u|) ≤ 2 * (b u * (2 * (b u) ^ 2)) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        simpa [mul_assoc, mul_left_comm, mul_comm] using htwo
      _ = 4 * (b u) ^ 3 := by ring_nf

  -- Constants and dominating function.
  let A : ℝ := 1 / Real.sqrt ((1 - t) / 2)
  let B : ℝ := A * |κ| + C_mills
  let C1 : ℝ := 1 / (1 - t)
  let C2 : ℝ := 1 / (2 * Real.sqrt (t / 2) * Real.sqrt ((1 - t) / 2))
  let D : ℝ := (C1 * A + C2) + (C1 * A * |κ|)
  let K : ℝ := 4 * (A + B) ^ 3 * D
  let bound : Ω → ℝ := fun ω => K * (|Z ω| + 1) ^ 4

  have bound_int : Integrable bound P := by
    have hZ4 : MemLp Z (4 : ℝ≥0∞) P := by
      have hid : MemLp (id : ℝ → ℝ) (4 : ℝ≥0∞)
          (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))) := by
        simpa using
          (ProbabilityTheory.memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
            (p := (4 : ℝ≥0∞)) (by simp))
      have hid_map : MemLp (id : ℝ → ℝ) (4 : ℝ≥0∞) (Measure.map Z P) := by
        simpa [hZ_gaussian] using hid
      have hcomp : MemLp ((id : ℝ → ℝ) ∘ Z) (4 : ℝ≥0∞) P :=
        (memLp_map_measure_iff (μ := P) (f := Z) (g := (id : ℝ → ℝ)) (p := (4 : ℝ≥0∞))
              (hg := measurable_id.aestronglyMeasurable) (hf := hZ_meas)).1 hid_map
      simpa [Function.comp] using hcomp
    have habsZ4 : MemLp (fun ω => |Z ω|) (4 : ℝ≥0∞) P := by
      simpa [Real.norm_eq_abs] using hZ4.norm
    have hone : MemLp (fun _ : Ω => (1 : ℝ)) (4 : ℝ≥0∞) P := by
      simpa using (memLp_const (μ := P) (c := (1 : ℝ)) (p := (4 : ℝ≥0∞)))
    have hsum : MemLp (fun ω => |Z ω| + 1) (4 : ℝ≥0∞) P := by
      simpa using habsZ4.add hone
    have hint : Integrable (fun ω => ‖|Z ω| + 1‖ ^ 4) P :=
      hsum.integrable_norm_pow (p := 4) (by decide)
    have hint' : Integrable (fun ω => (|Z ω| + 1) ^ 4) P := by
      have hEq :
          (fun ω => ‖|Z ω| + 1‖ ^ 4) =ᵐ[P] fun ω => (|Z ω| + 1) ^ 4 := by
        refine ae_of_all P (fun ω => ?_)
        have h0 : 0 ≤ |Z ω| + 1 := by nlinarith [abs_nonneg (Z ω)]
        simp [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hint.congr hEq
    simpa [bound] using hint'.const_mul K

  have h_bound :
      ∀ᵐ ω ∂P, ∀ s ∈ Metric.ball t ε,
        ‖(deriv h (U (κ := κ) (Z := Z) s ω))
            * (deriv (fun r => U (κ := κ) (Z := Z) r ω) s)‖ ≤ bound ω := by
    refine ae_of_all _ (fun ω => ?_)
    intro s hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := hs_mem_Ioo hs
    have hs' : dist s t < ε := (Metric.mem_ball.mp hs)
    have hsabs : |s - t| < ε := by simpa [Real.dist_eq] using hs'
    have hst : s - t < ε ∧ t - s < ε := (abs_sub_lt_iff).1 hsabs
    have hs_lt : s < t + ε := by linarith [hst.1]
    have hs_gt : t - ε < s := by linarith [hst.2]
    have hε_le_t : ε ≤ t / 2 := min_le_left _ _
    have hε_le_1t : ε ≤ (1 - t) / 2 := min_le_right _ _
    have hs_lower : t / 2 ≤ s := by
      have : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
      exact le_trans this (le_of_lt hs_gt)
    have h1s_lower : (1 - t) / 2 ≤ 1 - s := by
      have : s < t + (1 - t) / 2 := lt_of_lt_of_le hs_lt (by nlinarith [hε_le_1t])
      have : (1 - t) / 2 < 1 - s := by nlinarith
      exact le_of_lt this

    have hs_sqrt_le_one : Real.sqrt s ≤ 1 := by
      have : s ≤ 1 := le_of_lt hsIoo.2
      simpa using (Real.sqrt_le_sqrt this)

    have hden_inv : 1 / Real.sqrt (1 - s) ≤ A := by
      have ha_pos : 0 < Real.sqrt ((1 - t) / 2) := by
        have : 0 < (1 - t) / 2 := by
          have : 0 < 1 - t := sub_pos.mpr ht1
          nlinarith
        exact Real.sqrt_pos.2 this
      have hab : Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - s) :=
        Real.sqrt_le_sqrt h1s_lower
      have := one_div_le_one_div_of_le ha_pos hab
      simpa [A, one_div] using this

    have hU_abs :
        |U (κ := κ) (Z := Z) s ω| ≤ A * |Z ω| + A * |κ| := by
      have hnum : |κ - Real.sqrt s * Z ω| ≤ |κ| + |Z ω| := by
        calc
          |κ - Real.sqrt s * Z ω| ≤ |κ| + |Real.sqrt s * Z ω| := by
            simpa [sub_eq_add_neg] using (abs_add_le κ (-(Real.sqrt s * Z ω)))
          _ = |κ| + Real.sqrt s * |Z ω| := by
            simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg s)]
          _ ≤ |κ| + 1 * |Z ω| := by
            have hz0 : 0 ≤ |Z ω| := abs_nonneg (Z ω)
            exact add_le_add_right (mul_le_mul_of_nonneg_right hs_sqrt_le_one hz0) |κ|
          _ = |κ| + |Z ω| := by ring
      calc
        |U (κ := κ) (Z := Z) s ω|
            = |κ - Real.sqrt s * Z ω| / Real.sqrt (1 - s) := by
              simp [U, abs_div, abs_of_nonneg (Real.sqrt_nonneg (1 - s))]
        _ ≤ (|κ| + |Z ω|) / Real.sqrt (1 - s) := by
              gcongr
        _ = (|κ| + |Z ω|) * (1 / Real.sqrt (1 - s)) := by
              simp [div_eq_mul_inv, one_div]
        _ ≤ (|κ| + |Z ω|) * A := by
              have h0 : 0 ≤ |κ| + |Z ω| := by nlinarith [abs_nonneg κ, abs_nonneg (Z ω)]
              exact mul_le_mul_of_nonneg_left hden_inv h0
        _ = A * |Z ω| + A * |κ| := by ring_nf

    have hbU : b (U (κ := κ) (Z := Z) s ω) ≤ (A + B) * (|Z ω| + 1) := by
      have h1 : b (U (κ := κ) (Z := Z) s ω) ≤ A * |Z ω| + B := by
        have : |U (κ := κ) (Z := Z) s ω| + C_mills ≤ (A * |Z ω| + A * |κ|) + C_mills :=
          add_le_add_left hU_abs C_mills
        simpa [b, B, add_assoc, add_left_comm, add_comm] using this
      have hA0 : 0 ≤ A := by
        have : 0 < Real.sqrt ((1 - t) / 2) := by
          have : 0 < (1 - t) / 2 := by
            have : 0 < 1 - t := sub_pos.mpr ht1
            nlinarith
          exact Real.sqrt_pos.2 this
        have : 0 < 1 / Real.sqrt ((1 - t) / 2) := by
          simpa [one_div] using (inv_pos.2 this)
        exact this.le
      have hB0 : 0 ≤ B := by
        dsimp [B]
        exact add_nonneg (mul_nonneg hA0 (abs_nonneg κ)) hC0
      have h2 : A * |Z ω| + B ≤ (A + B) * (|Z ω| + 1) := by
        have hz0 : 0 ≤ |Z ω| := abs_nonneg (Z ω)
        nlinarith [hz0, hA0, hB0]
      exact le_trans h1 h2

    have hderivU :
        |deriv (fun r => U (κ := κ) (Z := Z) r ω) s| ≤ D * (|Z ω| + 1) := by
      have hderivU_eq :
          deriv (fun r => U (κ := κ) (Z := Z) r ω) s =
            (U (κ := κ) (Z := Z) s ω) / (2 * (1 - s))
              - (Z ω) / (2 * Real.sqrt s * Real.sqrt (1 - s)) := by
        simpa using (deriv_U (Z := Z) (κ := κ) (t := s) (ht := hsIoo) (ω := ω))
      have htri :
          |deriv (fun r => U (κ := κ) (Z := Z) r ω) s| ≤
            |(U (κ := κ) (Z := Z) s ω) / (2 * (1 - s))|
              + |(Z ω) / (2 * Real.sqrt s * Real.sqrt (1 - s))| := by
        simpa [hderivU_eq, sub_eq_add_neg, abs_neg] using
          (abs_add_le ((U (κ := κ) (Z := Z) s ω) / (2 * (1 - s)))
            (-( (Z ω) / (2 * Real.sqrt s * Real.sqrt (1 - s)))))

      have hcoeff1 : 1 / (2 * (1 - s)) ≤ C1 := by
        have ha_pos : 0 < 1 - t := sub_pos.mpr ht1
        have hab : 1 - t ≤ 2 * (1 - s) := by
          nlinarith [h1s_lower]
        simpa [C1, one_div, mul_assoc, mul_left_comm, mul_comm] using
          (one_div_le_one_div_of_le ha_pos hab)

      have hcoeff2 : 1 / (2 * Real.sqrt s * Real.sqrt (1 - s)) ≤ C2 := by
        have ht2 : 0 < t / 2 := by
          exact div_pos ht0 (by norm_num)
        have h1t2 : 0 < (1 - t) / 2 := by
          have : 0 < 1 - t := sub_pos.mpr ht1
          exact div_pos this (by norm_num)
        have ha_pos : 0 < 2 * Real.sqrt (t / 2) * Real.sqrt ((1 - t) / 2) := by
          have hs1 : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.2 ht2
          have hs2 : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 h1t2
          have : 0 < (2 : ℝ) * Real.sqrt (t / 2) := mul_pos (by norm_num) hs1
          exact mul_pos this hs2
        have hab :
            2 * Real.sqrt (t / 2) * Real.sqrt ((1 - t) / 2) ≤
              2 * Real.sqrt s * Real.sqrt (1 - s) := by
          have hst : Real.sqrt (t / 2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs_lower
          have hst' : Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - s) :=
            Real.sqrt_le_sqrt h1s_lower
          have hmul :
              Real.sqrt (t / 2) * Real.sqrt ((1 - t) / 2) ≤
                Real.sqrt s * Real.sqrt (1 - s) :=
            mul_le_mul hst hst' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          have h2mul :
              (2 : ℝ) * (Real.sqrt (t / 2) * Real.sqrt ((1 - t) / 2)) ≤
                (2 : ℝ) * (Real.sqrt s * Real.sqrt (1 - s)) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
          simpa [mul_assoc] using h2mul
        simpa [C2] using (one_div_le_one_div_of_le ha_pos hab)

      have hterm1 :
          |(U (κ := κ) (Z := Z) s ω) / (2 * (1 - s))| ≤ C1 * (A * |Z ω| + A * |κ|) := by
        have hden0 : 0 ≤ 2 * (1 - s) := by
          have h2 : 0 ≤ (2 : ℝ) := by norm_num
          have h : 0 ≤ 1 - s := (sub_pos.mpr hsIoo.2).le
          exact mul_nonneg h2 h
        have habs : |(U (κ := κ) (Z := Z) s ω) / (2 * (1 - s))| =
            |U (κ := κ) (Z := Z) s ω| * (1 / (2 * (1 - s))) := by
          calc
            |(U (κ := κ) (Z := Z) s ω) / (2 * (1 - s))|
                = |U (κ := κ) (Z := Z) s ω| / |2 * (1 - s)| := by
                  simpa [abs_div]
            _ = |U (κ := κ) (Z := Z) s ω| / (2 * (1 - s)) := by
                  simp [abs_of_nonneg hden0]
            _ = |U (κ := κ) (Z := Z) s ω| * (1 / (2 * (1 - s))) := by
                  simp [div_eq_mul_inv, one_div]
        calc
          |(U (κ := κ) (Z := Z) s ω) / (2 * (1 - s))|
              = |U (κ := κ) (Z := Z) s ω| * (1 / (2 * (1 - s))) := habs
          _ ≤ |U (κ := κ) (Z := Z) s ω| * C1 := by
            have h0 : 0 ≤ |U (κ := κ) (Z := Z) s ω| := abs_nonneg _
            exact mul_le_mul_of_nonneg_left hcoeff1 h0
          _ ≤ (A * |Z ω| + A * |κ|) * C1 := by
            have h0 : 0 ≤ C1 := by
              have : 0 < 1 - t := sub_pos.mpr ht1
              exact (one_div_pos.2 this).le
            exact mul_le_mul_of_nonneg_right hU_abs h0
          _ = C1 * (A * |Z ω| + A * |κ|) := by ring

      have hterm2 :
          |(Z ω) / (2 * Real.sqrt s * Real.sqrt (1 - s))| ≤ C2 * |Z ω| := by
        have hden0 : 0 ≤ 2 * Real.sqrt s * Real.sqrt (1 - s) := by
          have h2 : 0 ≤ (2 : ℝ) := by norm_num
          exact
            mul_nonneg (mul_nonneg h2 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        have habs : |(Z ω) / (2 * Real.sqrt s * Real.sqrt (1 - s))| =
            |Z ω| * (1 / (2 * Real.sqrt s * Real.sqrt (1 - s))) := by
          calc
            |(Z ω) / (2 * Real.sqrt s * Real.sqrt (1 - s))|
                = |Z ω| / |2 * Real.sqrt s * Real.sqrt (1 - s)| := by
                  simpa [abs_div]
            _ = |Z ω| / (2 * Real.sqrt s * Real.sqrt (1 - s)) := by
                  simp [abs_of_nonneg hden0]
            _ = |Z ω| * (1 / (2 * Real.sqrt s * Real.sqrt (1 - s))) := by
                  simp [div_eq_mul_inv, one_div]
        calc
          |(Z ω) / (2 * Real.sqrt s * Real.sqrt (1 - s))|
              = |Z ω| * (1 / (2 * Real.sqrt s * Real.sqrt (1 - s))) := habs
          _ ≤ |Z ω| * C2 := by
            have h0 : 0 ≤ |Z ω| := abs_nonneg _
            exact mul_le_mul_of_nonneg_left hcoeff2 h0
          _ = C2 * |Z ω| := by ring

      have :
          |deriv (fun r => U (κ := κ) (Z := Z) r ω) s| ≤
            C1 * (A * |Z ω| + A * |κ|) + C2 * |Z ω| := by
        exact le_trans htri (add_le_add hterm1 hterm2)

      -- Linear bound in |Z| dominated by D * (|Z| + 1).
      have hz0 : 0 ≤ |Z ω| := abs_nonneg _
      have hC10 : 0 ≤ C1 := by
        have : 0 < 1 - t := sub_pos.mpr ht1
        exact (one_div_pos.2 this).le
      have hA0 : 0 ≤ A := by
        have : 0 < Real.sqrt ((1 - t) / 2) := by
          have : 0 < (1 - t) / 2 := by
            have : 0 < 1 - t := sub_pos.mpr ht1
            nlinarith
          exact Real.sqrt_pos.2 this
        have : 0 < 1 / Real.sqrt ((1 - t) / 2) := by
          simpa [one_div] using (inv_pos.2 this)
        exact this.le
      have hC20 : 0 ≤ C2 := by
        have : 0 < 2 * Real.sqrt (t / 2) * Real.sqrt ((1 - t) / 2) := by
          have ht2 : 0 < t / 2 := by nlinarith
          have h1t2 : 0 < (1 - t) / 2 := by
            have : 0 < 1 - t := sub_pos.mpr ht1
            nlinarith
          have hs1 : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.2 ht2
          have hs2 : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 h1t2
          have : 0 < (2 : ℝ) * Real.sqrt (t / 2) := mul_pos (by norm_num) hs1
          exact mul_pos this hs2
        exact (one_div_pos.2 this).le
      have ha0 : 0 ≤ C1 * A + C2 := by
        nlinarith [mul_nonneg hC10 hA0, hC20]
      have hb0 : 0 ≤ C1 * A * |κ| := by
        exact mul_nonneg (mul_nonneg hC10 hA0) (abs_nonneg κ)
      have hlin :
          C1 * (A * |Z ω| + A * |κ|) + C2 * |Z ω| ≤ D * (|Z ω| + 1) := by
        -- Expand the left-hand side and use `a*x + b ≤ (a+b)*(x+1)` for `x = |Z| ≥ 0`.
        have hrewrite :
            C1 * (A * |Z ω| + A * |κ|) + C2 * |Z ω| =
              (C1 * A + C2) * |Z ω| + (C1 * A * |κ|) := by ring_nf
        have haux :
            (C1 * A + C2) * |Z ω| + (C1 * A * |κ|) ≤
              ((C1 * A + C2) + (C1 * A * |κ|)) * (|Z ω| + 1) := by
          have hpos : 0 ≤ (C1 * A * |κ|) * |Z ω| + (C1 * A + C2) :=
            add_nonneg (mul_nonneg hb0 hz0) ha0
          have hle :
              (C1 * A + C2) * |Z ω| + (C1 * A * |κ|) ≤
                ((C1 * A + C2) * |Z ω| + (C1 * A * |κ|)) + ((C1 * A * |κ|) * |Z ω| + (C1 * A + C2)) :=
            le_add_of_nonneg_right hpos
          have hrw :
              ((C1 * A + C2) * |Z ω| + (C1 * A * |κ|)) + ((C1 * A * |κ|) * |Z ω| + (C1 * A + C2)) =
                ((C1 * A + C2) + (C1 * A * |κ|)) * (|Z ω| + 1) := by ring
          exact le_trans hle (le_of_eq hrw)
        have hD :
            ((C1 * A + C2) + (C1 * A * |κ|)) * (|Z ω| + 1) = D * (|Z ω| + 1) := by
          simp [D, add_assoc, add_left_comm, add_comm]
        simpa [hrewrite, hD] using haux
      exact le_trans this hlin

    have habs_deriv_h :
        |deriv h (U (κ := κ) (Z := Z) s ω)| ≤ 4 * ((A + B) * (|Z ω| + 1)) ^ 3 := by
      have h1 : |deriv h (U (κ := κ) (Z := Z) s ω)| ≤ 4 * (b (U (κ := κ) (Z := Z) s ω)) ^ 3 :=
        abs_deriv_h_le _
      have hpow : (b (U (κ := κ) (Z := Z) s ω)) ^ 3 ≤ ((A + B) * (|Z ω| + 1)) ^ 3 :=
        pow_le_pow_left₀ (by
          dsimp [b]
          exact add_nonneg (abs_nonneg _) hC0) hbU 3
      have : 4 * (b (U (κ := κ) (Z := Z) s ω)) ^ 3 ≤ 4 * ((A + B) * (|Z ω| + 1)) ^ 3 := by
        have : 0 ≤ (4 : ℝ) := by norm_num
        exact mul_le_mul_of_nonneg_left hpow this
      exact le_trans h1 this

    have habs_prod :
        |(deriv h (U (κ := κ) (Z := Z) s ω))
            * (deriv (fun r => U (κ := κ) (Z := Z) r ω) s)| ≤ bound ω := by
      have hmul :
          |(deriv h (U (κ := κ) (Z := Z) s ω))
              * (deriv (fun r => U (κ := κ) (Z := Z) r ω) s)| =
            |deriv h (U (κ := κ) (Z := Z) s ω)|
              * |deriv (fun r => U (κ := κ) (Z := Z) r ω) s| := by
        simp [abs_mul]
      have :
          |deriv h (U (κ := κ) (Z := Z) s ω)|
              * |deriv (fun r => U (κ := κ) (Z := Z) r ω) s| ≤
            (4 * ((A + B) * (|Z ω| + 1)) ^ 3) * (D * (|Z ω| + 1)) := by
        have h0 : 0 ≤ |deriv (fun r => U (κ := κ) (Z := Z) r ω) s| := abs_nonneg _
        exact mul_le_mul habs_deriv_h hderivU h0 (by positivity)
      have hrewrite :
          (4 * ((A + B) * (|Z ω| + 1)) ^ 3) * (D * (|Z ω| + 1)) =
            bound ω := by
        dsimp [bound, K]
        ring_nf
      simpa [hmul, hrewrite] using le_trans this (le_of_eq hrewrite)

    simpa [Real.norm_eq_abs, bound] using habs_prod

  have h_diff :
      ∀ᵐ ω ∂P, ∀ s ∈ Metric.ball t ε,
        HasDerivAt
          (fun r => h (U (κ := κ) (Z := Z) r ω))
          ((deriv h (U (κ := κ) (Z := Z) s ω))
            * (deriv (fun r => U (κ := κ) (Z := Z) r ω) s))
          s := by
    refine ae_of_all _ (fun ω => ?_)
    intro s hs
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := hs_mem_Ioo hs
    have hs0 : (s : ℝ) ≠ 0 := ne_of_gt hsIoo.1
    have hs1 : (1 - s : ℝ) ≠ 0 := by
      have : 0 < 1 - s := sub_pos.mpr hsIoo.2
      exact ne_of_gt this
    have hinside : DifferentiableAt ℝ (fun r : ℝ => 1 - r) s := by
      fun_prop
    have hsqrt1 : DifferentiableAt ℝ (fun x : ℝ => Real.sqrt x) (1 - s) :=
      (Real.hasDerivAt_sqrt (x := 1 - s) hs1).differentiableAt
    have hsqrt0 : DifferentiableAt ℝ (fun x : ℝ => Real.sqrt x) s :=
      (Real.hasDerivAt_sqrt (x := s) hs0).differentiableAt
    have hnum_diff :
        DifferentiableAt ℝ (fun r : ℝ => κ - Real.sqrt r * Z ω) s := by
      have hmul : DifferentiableAt ℝ (fun r : ℝ => Real.sqrt r * Z ω) s :=
        hsqrt0.mul_const (Z ω)
      simpa [sub_eq_add_neg] using (hmul.const_sub κ)
    have hden_diff :
        DifferentiableAt ℝ (fun r : ℝ => Real.sqrt (1 - r)) s :=
      hsqrt1.comp s hinside
    have hden0 : Real.sqrt (1 - s) ≠ 0 := by
      have : 0 < 1 - s := sub_pos.mpr hsIoo.2
      exact ne_of_gt (Real.sqrt_pos.2 this)
    have hU_diff :
        DifferentiableAt ℝ (fun r : ℝ => U (κ := κ) (Z := Z) r ω) s := by
      simpa [U] using (hnum_diff.div hden_diff hden0)
    have hU_has :
        HasDerivAt (fun r : ℝ => U (κ := κ) (Z := Z) r ω)
          (deriv (fun r : ℝ => U (κ := κ) (Z := Z) r ω) s) s :=
      hU_diff.hasDerivAt
    have hh_diff : DifferentiableAt ℝ h (U (κ := κ) (Z := Z) s ω) := by
      have hE : DifferentiableAt ℝ E (U (κ := κ) (Z := Z) s ω) :=
        differentiableAt_E (u := U (κ := κ) (Z := Z) s ω)
      simpa [h] using hE.pow 2
    have hh_has : HasDerivAt h (deriv h (U (κ := κ) (Z := Z) s ω)) (U (κ := κ) (Z := Z) s ω) :=
      hh_diff.hasDerivAt
    simpa [Function.comp] using (hh_has.comp s hU_has)

  exact
    h_deriv_under_expect (P := P) (Z := Z) (κ := κ) (t := t)
      (ε := ε) ε_pos h_meas h_int hF'_meas bound h_bound bound_int h_diff

lemma deriv_B_step5
    (hZ_gaussian :
      Measure.map Z P =
        ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (h_deriv_under_expect :
      HasDerivAt
        (fun s => 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
        (𝔼 (P := P) (fun ω =>
          (deriv h (U (κ := κ) (Z := Z) t ω))
            * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
        t)
    (integrable_h : Integrable (fun ω => h (U (κ := κ) (Z := Z) t ω)) P)
    (integrable_Uh :
      Integrable (fun ω =>
        (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P)
    (integrable_Zh :
      Integrable (fun ω =>
        (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P)
    (integrable_ψZ : Integrable (fun ω => ψ (κ := κ) (t := t) (Z ω)) P)
    (integrable_deriv_ψZ :
      Integrable (fun ω => deriv (ψ (κ := κ) (t := t)) (Z ω)) P)
    (integrable_hdd :
      Integrable (fun ω => deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) P) :
    deriv (fun s => B (P := P) (κ := κ) (Z := Z) s) t =
      𝔼 (P := P) (fun ω =>
        -(E (U (κ := κ) (Z := Z) t ω)) ^ 2
        + (U (κ := κ) (Z := Z) t ω) * (E (U (κ := κ) (Z := Z) t ω)) * (deriv E (U (κ := κ) (Z := Z) t ω))
        + (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
        + (E (U (κ := κ) (Z := Z) t ω)) * (deriv (fun x => deriv E x) (U (κ := κ) (Z := Z) t ω))) := by
  have h4 :=
    deriv_B_step4 (P := P) (Z := Z) (κ := κ) (t := t)
      (hZ_gaussian := hZ_gaussian) (ht := ht)
      (h_deriv_under_expect := h_deriv_under_expect)
      (integrable_h := integrable_h) (integrable_Uh := integrable_Uh)
      (integrable_Zh := integrable_Zh) (integrable_ψZ := integrable_ψZ)
      (integrable_deriv_ψZ := integrable_deriv_ψZ) (integrable_hdd := integrable_hdd)
  -- Rewrite Step 4's integrand into the Step 5 form.
  have hpoint :
      (fun ω =>
          -h (U (κ := κ) (Z := Z) t ω)
            + (1 / 2) * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))
            + (1 / 2) * deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) =
        fun ω =>
          -(E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (U (κ := κ) (Z := Z) t ω) * (E (U (κ := κ) (Z := Z) t ω)) * (deriv E (U (κ := κ) (Z := Z) t ω))
            + (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (E (U (κ := κ) (Z := Z) t ω)) * (deriv (fun x => deriv E x) (U (κ := κ) (Z := Z) t ω)) := by
    funext ω
    simp [h, pow_two, mul_assoc, mul_left_comm, mul_comm]
    rw [deriv_h (u := U (κ := κ) (Z := Z) t ω)]
    rw [deriv2_h (u := U (κ := κ) (Z := Z) t ω)]
    ring_nf
  -- Rewrite Step 4's `𝔼`-integrand using `hpoint`.
  have h4' : 𝔼 (P := P) (fun ω =>
        -h (U (κ := κ) (Z := Z) t ω)
          + (1 / 2) * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))
          + (1 / 2) * deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) =
      𝔼 (P := P) (fun ω =>
        -(E (U (κ := κ) (Z := Z) t ω)) ^ 2
          + (U (κ := κ) (Z := Z) t ω) * (E (U (κ := κ) (Z := Z) t ω)) * (deriv E (U (κ := κ) (Z := Z) t ω))
          + (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
          + (E (U (κ := κ) (Z := Z) t ω)) * (deriv (fun x => deriv E x) (U (κ := κ) (Z := Z) t ω))) := by
    simpa using congrArg (fun f : Ω → ℝ => 𝔼 (P := P) f) hpoint
  -- Combine Step 4 with the rewritten expectation.
  calc
    deriv (fun s => B (P := P) (κ := κ) (Z := Z) s) t =
        𝔼 (P := P) (fun ω =>
          -h (U (κ := κ) (Z := Z) t ω)
            + (1 / 2) * (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))
            + (1 / 2) * deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) := h4
    _ = 𝔼 (P := P) (fun ω =>
          -(E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (U (κ := κ) (Z := Z) t ω) * (E (U (κ := κ) (Z := Z) t ω)) * (deriv E (U (κ := κ) (Z := Z) t ω))
            + (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (E (U (κ := κ) (Z := Z) t ω)) * (deriv (fun x => deriv E x) (U (κ := κ) (Z := Z) t ω))) := h4'

/-! Step 6 -/

lemma simplify_combo (u : ℝ) :
    u * (E u) * (deriv E u)
      + (E u) * (deriv (fun x => deriv E x) u)
      - (E u) ^ 2
    = 2 * (E u) ^ 2 * ((deriv E u) - 1) := by
  rw [deriv2_E (u := u)]
  ring_nf

lemma deriv_B_step6
    (hZ_gaussian :
      Measure.map Z P =
        ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (h_deriv_under_expect :
      HasDerivAt
        (fun s => 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
        (𝔼 (P := P) (fun ω =>
          (deriv h (U (κ := κ) (Z := Z) t ω))
            * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
        t)
    (integrable_h : Integrable (fun ω => h (U (κ := κ) (Z := Z) t ω)) P)
    (integrable_Uh :
      Integrable (fun ω =>
        (U (κ := κ) (Z := Z) t ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P)
    (integrable_Zh :
      Integrable (fun ω =>
        (Z ω) * (deriv h (U (κ := κ) (Z := Z) t ω))) P)
    (integrable_ψZ : Integrable (fun ω => ψ (κ := κ) (t := t) (Z ω)) P)
    (integrable_deriv_ψZ :
      Integrable (fun ω => deriv (ψ (κ := κ) (t := t)) (Z ω)) P)
    (integrable_hdd :
      Integrable (fun ω => deriv (fun u => deriv h u) (U (κ := κ) (Z := Z) t ω)) P) :
    deriv (fun s => B (P := P) (κ := κ) (Z := Z) s) t =
      𝔼 (P := P) (fun ω =>
        (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
          + 2 * (E (U (κ := κ) (Z := Z) t ω)) ^ 2 * ((deriv E (U (κ := κ) (Z := Z) t ω)) - 1)) := by
  have h5 :=
    deriv_B_step5 (P := P) (Z := Z) (κ := κ) (t := t)
      (hZ_gaussian := hZ_gaussian) (ht := ht)
      (h_deriv_under_expect := h_deriv_under_expect)
      (integrable_h := integrable_h) (integrable_Uh := integrable_Uh)
      (integrable_Zh := integrable_Zh) (integrable_ψZ := integrable_ψZ)
      (integrable_deriv_ψZ := integrable_deriv_ψZ) (integrable_hdd := integrable_hdd)
  have hpoint :
      (fun ω =>
          -(E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (U (κ := κ) (Z := Z) t ω) * (E (U (κ := κ) (Z := Z) t ω)) * (deriv E (U (κ := κ) (Z := Z) t ω))
            + (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (E (U (κ := κ) (Z := Z) t ω)) * (deriv (fun x => deriv E x) (U (κ := κ) (Z := Z) t ω))) =
        fun ω =>
          (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + 2 * (E (U (κ := κ) (Z := Z) t ω)) ^ 2 * ((deriv E (U (κ := κ) (Z := Z) t ω)) - 1) := by
    funext ω
    -- Use `simplify_combo` at `u = U_t(ω)` and then rearrange.
    have hs :=
      simplify_combo (u := U (κ := κ) (Z := Z) t ω)
    have hs' :=
      congrArg (fun x =>
        (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2 + x) hs
    -- Rearrange the Step 5 integrand to expose the combination simplified by `hs`.
    calc
      -(E (U (κ := κ) (Z := Z) t ω)) ^ 2
          + (U (κ := κ) (Z := Z) t ω) * (E (U (κ := κ) (Z := Z) t ω)) * (deriv E (U (κ := κ) (Z := Z) t ω))
          + (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
          + (E (U (κ := κ) (Z := Z) t ω)) * (deriv (fun x => deriv E x) (U (κ := κ) (Z := Z) t ω)) =
          (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + ((U (κ := κ) (Z := Z) t ω) * (E (U (κ := κ) (Z := Z) t ω)) * (deriv E (U (κ := κ) (Z := Z) t ω))
                + (E (U (κ := κ) (Z := Z) t ω)) * (deriv (fun x => deriv E x) (U (κ := κ) (Z := Z) t ω))
                - (E (U (κ := κ) (Z := Z) t ω)) ^ 2) := by
          ring_nf
      _ = (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + 2 * (E (U (κ := κ) (Z := Z) t ω)) ^ 2 * ((deriv E (U (κ := κ) (Z := Z) t ω)) - 1) := by
          simpa using hs'
  have hEqE :
      𝔼 (P := P) (fun ω =>
          -(E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (U (κ := κ) (Z := Z) t ω) * (E (U (κ := κ) (Z := Z) t ω)) * (deriv E (U (κ := κ) (Z := Z) t ω))
            + (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (E (U (κ := κ) (Z := Z) t ω)) * (deriv (fun x => deriv E x) (U (κ := κ) (Z := Z) t ω))) =
        𝔼 (P := P) (fun ω =>
          (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + 2 * (E (U (κ := κ) (Z := Z) t ω)) ^ 2 * ((deriv E (U (κ := κ) (Z := Z) t ω)) - 1)) := by
    simpa using congrArg (fun f : Ω → ℝ => 𝔼 (P := P) f) hpoint
  calc
    deriv (fun s => B (P := P) (κ := κ) (Z := Z) s) t =
        𝔼 (P := P) (fun ω =>
          -(E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (U (κ := κ) (Z := Z) t ω) * (E (U (κ := κ) (Z := Z) t ω)) * (deriv E (U (κ := κ) (Z := Z) t ω))
            + (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + (E (U (κ := κ) (Z := Z) t ω)) * (deriv (fun x => deriv E x) (U (κ := κ) (Z := Z) t ω))) := h5
    _ = 𝔼 (P := P) (fun ω =>
          (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + 2 * (E (U (κ := κ) (Z := Z) t ω)) ^ 2 * ((deriv E (U (κ := κ) (Z := Z) t ω)) - 1)) := hEqE

/-! Step 7 -/

lemma g_eq (u : ℝ) :
    g u = (deriv E u) ^ 2 + 2 * (E u) ^ 2 * ((deriv E u) - 1) := by
  rw [deriv_E (u := u)]
  simp [g, pow_two, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
  ring_nf

theorem deriv_B_eq_expect_g
    (hZ_gaussian :
      Measure.map Z P =
        ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    : deriv (fun s => B (P := P) (κ := κ) (Z := Z) s) t =
      𝔼 (P := P) (fun ω => g (U (κ := κ) (Z := Z) t ω)) := by
  have h_integrable :
      IntegrabilityAssumptions (P := P) (Z := Z) (κ := κ) t :=
    integrabilityAssumptions_of_gaussian (P := P) (Z := Z) (κ := κ) (t := t)
      (hZ_gaussian := hZ_gaussian) (ht := ht)
  have h_deriv_under_expect :
      HasDerivAt
        (fun s => 𝔼 (P := P) (fun ω => h (U (κ := κ) (Z := Z) s ω)))
        (𝔼 (P := P) (fun ω =>
          (deriv h (U (κ := κ) (Z := Z) t ω))
            * (deriv (fun s => U (κ := κ) (Z := Z) s ω) t)))
        t :=
    h_deriv_under_expect_of_gaussian (P := P) (Z := Z) (κ := κ) (t := t)
      (hZ_gaussian := hZ_gaussian) (ht := ht)
  have h6 :=
    deriv_B_step6 (P := P) (Z := Z) (κ := κ) (t := t)
      (hZ_gaussian := hZ_gaussian) (ht := ht)
      (h_deriv_under_expect := h_deriv_under_expect)
      (integrable_h := h_integrable.integrable_h)
      (integrable_Uh := h_integrable.integrable_Uh)
      (integrable_Zh := h_integrable.integrable_Zh)
      (integrable_ψZ := h_integrable.integrable_ψZ)
      (integrable_deriv_ψZ := h_integrable.integrable_deriv_ψZ)
      (integrable_hdd := h_integrable.integrable_hdd)

  have hpoint :
      (fun ω => g (U (κ := κ) (Z := Z) t ω)) =
        fun ω =>
          (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + 2 * (E (U (κ := κ) (Z := Z) t ω)) ^ 2 * ((deriv E (U (κ := κ) (Z := Z) t ω)) - 1) := by
    funext ω
    simpa using (g_eq (u := U (κ := κ) (Z := Z) t ω))
  have hEqE :
      𝔼 (P := P) (fun ω =>
          (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + 2 * (E (U (κ := κ) (Z := Z) t ω)) ^ 2 * ((deriv E (U (κ := κ) (Z := Z) t ω)) - 1)) =
        𝔼 (P := P) (fun ω => g (U (κ := κ) (Z := Z) t ω)) := by
    simpa using congrArg (fun f : Ω → ℝ => 𝔼 (P := P) f) hpoint.symm
  calc
    deriv (fun s => B (P := P) (κ := κ) (Z := Z) s) t =
        𝔼 (P := P) (fun ω =>
          (deriv E (U (κ := κ) (Z := Z) t ω)) ^ 2
            + 2 * (E (U (κ := κ) (Z := Z) t ω)) ^ 2 * ((deriv E (U (κ := κ) (Z := Z) t ω)) - 1)) := h6
    _ = 𝔼 (P := P) (fun ω => g (U (κ := κ) (Z := Z) t ω)) := hEqE

end Proof

end

end MillsBlueprint
