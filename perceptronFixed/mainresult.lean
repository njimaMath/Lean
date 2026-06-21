import Mathlib

import perceptronFixed.Theorem1.Theorem


open scoped Topology
open MeasureTheory Filter

namespace MainResult

noncomputable section

def γ : Measure ℝ :=
  ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))

def Expect (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂γ

def φ (u : ℝ) : ℝ :=
  Real.exp (-(u ^ 2) / 2) / Real.sqrt (2 * Real.pi)

def Φbar (u : ℝ) : ℝ :=
  ∫ x in Set.Ici u, φ x

def Φ (u : ℝ) : ℝ :=
  1 - Φbar u

def E (u : ℝ) : ℝ :=
  φ u / Φbar u

def U (κ q z : ℝ) : ℝ :=
  (κ - Real.sqrt q * z) / Real.sqrt (1 - q)

def F (κ q x : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - q)) * E ((κ - x) / Real.sqrt (1 - q))

def P (r : ℝ) : ℝ :=
  Expect (fun z => (Real.tanh (Real.sqrt r * z)) ^ 2)

def B (κ q : ℝ) : ℝ :=
  (1 - q) * Expect (fun z => (E (U κ q z)) ^ 2)

def R (κ q α : ℝ) : ℝ :=
  α * Expect (fun z => (F κ q (Real.sqrt q * z)) ^ 2)

def Cκ (κ : ℝ) : ℝ :=
  Expect (fun z => (max (κ - z) 0) ^ 2)

def αc (κ : ℝ) : ℝ :=
  2 / (Real.pi * Cκ κ)

def IsSolution (κ α q r : ℝ) : Prop :=
  0 ≤ q ∧ q < 1 ∧ 0 ≤ r ∧ q = P r ∧ r = R κ q α

lemma Expect_eq (f : ℝ → ℝ) : Expect f = Theorem1.Expect f := by
  simp [Expect, Theorem1.Expect, γ, Theorem1.γ]

lemma φ_eq (u : ℝ) : φ u = Theorem1.φ u := by
  simp [φ, Theorem1.φ, DecreasingG.φ]

lemma Φbar_eq (u : ℝ) : Φbar u = Theorem1.Φbar u := by
  simp [Φbar, Theorem1.Φbar, DecreasingG.Φbar, φ, DecreasingG.φ]

lemma E_eq (u : ℝ) : E u = Theorem1.E u := by
  simp [E, Theorem1.E, DecreasingG.E, φ_eq, Φbar_eq]

lemma U_eq (κ q z : ℝ) : U κ q z = Theorem1.U κ q z := by
  simp [U, Theorem1.U]

lemma F_eq (κ q x : ℝ) : F κ q x = Theorem1.F κ q x := by
  simp [F, Theorem1.F, E_eq]

lemma P_eq (r : ℝ) : P r = Theorem1.P r := by
  simp [P, Theorem1.P, Expect, Theorem1.Expect, γ, Theorem1.γ]

lemma B_eq (κ q : ℝ) : B κ q = Theorem1.B κ q := by
  simp [B, Theorem1.B, Expect, Theorem1.Expect, γ, Theorem1.γ, U_eq, E_eq]

lemma R_eq (κ q α : ℝ) : R κ q α = Theorem1.R κ q α := by
  simp [R, Theorem1.R, Expect, Theorem1.Expect, γ, Theorem1.γ, F_eq]

lemma Cκ_eq (κ : ℝ) : Cκ κ = Theorem1.Cκ κ := by
  simp [Cκ, Theorem1.Cκ, Expect, Theorem1.Expect, γ, Theorem1.γ]

lemma αc_eq (κ : ℝ) : αc κ = Theorem1.αc κ := by
  simp [αc, Theorem1.αc, Cκ_eq]

lemma αc_pos (κ : ℝ) : 0 < αc κ := by
  simpa [αc_eq κ] using Theorem1.αc_pos κ

private lemma φ_eq_gaussianPDFReal :
    φ = ProbabilityTheory.gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : NNReal)) := by
  funext x
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp [φ, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

private lemma integral_φ_eq_one : (∫ x : ℝ, φ x) = 1 := by
  have hv : (1 : NNReal) ≠ 0 := by simp
  simpa [φ_eq_gaussianPDFReal] using
    (ProbabilityTheory.integral_gaussianPDFReal_eq_one (μ := (0 : ℝ)) (v := (1 : NNReal)) hv)

private lemma integrable_φ : Integrable φ := by
  change Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi))
  have h :
      Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
    have h' :
        (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) =
          fun x : ℝ => Real.exp (-((1 / 2 : ℝ) * x ^ 2)) := by
      funext x
      ring_nf
    simpa [h'] using (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num))
  exact h.div_const (Real.sqrt (2 * Real.pi))

private lemma φ_even (u : ℝ) : φ (-u) = φ u := by
  simp [φ]

private lemma Φ_eq_integral_Iic (u : ℝ) : Φ u = ∫ x in Set.Iic u, φ x := by
  have hIoi : Φbar u = ∫ x in Set.Ioi u, φ x := by
    simpa [Φbar] using
      (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := (volume : Measure ℝ)) (f := φ) (x := u))
  have hdis : Disjoint (Set.Iic u) (Set.Ioi u) := Set.Iic_disjoint_Ioi (a := u) (b := u) le_rfl
  have hunion :
      (∫ x in (Set.Iic u ∪ Set.Ioi u : Set ℝ), φ x) =
        (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
    simpa using
      (MeasureTheory.setIntegral_union (μ := (volume : Measure ℝ)) (f := φ)
        (s := Set.Iic u) (t := Set.Ioi u) hdis measurableSet_Ioi
        (integrable_φ.integrableOn) (integrable_φ.integrableOn))
  have hset : (Set.Iic u ∪ Set.Ioi u : Set ℝ) = Set.univ := by
    simpa using (Set.Iic_union_Ioi (a := u))
  have hsplit :
      (∫ x : ℝ, φ x) = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := by
    calc
      (∫ x : ℝ, φ x) = ∫ x in (Set.Iic u ∪ Set.Ioi u : Set ℝ), φ x := by
        simp [hset]
      _ = (∫ x in Set.Iic u, φ x) + ∫ x in Set.Ioi u, φ x := hunion
  have hIic : ∫ x in Set.Iic u, φ x = 1 - Φbar u := by
    have : (∫ x in Set.Iic u, φ x) = (∫ x : ℝ, φ x) - ∫ x in Set.Ioi u, φ x := by
      linarith [hsplit]
    simpa [hIoi, integral_φ_eq_one] using this
  simpa [Φ] using hIic.symm

private lemma Φbar_neg_eq_Φ (u : ℝ) : Φbar (-u) = Φ u := by
  have hIoi : Φbar (-u) = ∫ x in Set.Ioi (-u), φ x := by
    simpa [Φbar] using
      (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := (volume : Measure ℝ)) (f := φ)
        (x := (-u)))
  have hsymm : (∫ x in Set.Iic u, φ x) = ∫ x in Set.Ioi (-u), φ x := by
    simpa [φ_even] using (integral_comp_neg_Iic (c := u) (f := φ))
  calc
    Φbar (-u) = ∫ x in Set.Ioi (-u), φ x := hIoi
    _ = ∫ x in Set.Iic u, φ x := hsymm.symm
    _ = Φ u := (Φ_eq_integral_Iic u).symm

private lemma tendsto_φ_atTop : Tendsto φ atTop (𝓝 0) := by
  change Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)) atTop (𝓝 0)
  have hpow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
    simpa using (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hneg : Tendsto (fun x : ℝ => -(x ^ 2)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hpow
  have hneg_div : Tendsto (fun x : ℝ => -(x ^ 2) / (2 : ℝ)) atTop atBot :=
    hneg.atBot_div_const (by norm_num)
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg_div
  simpa using hexp.div_const (Real.sqrt (2 * Real.pi))

private lemma hasDerivAt_φ (u : ℝ) : HasDerivAt φ (-u * φ u) u := by
  change
    HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi))
      (-u * (Real.exp (-(u ^ 2) / 2) / Real.sqrt (2 * Real.pi))) u
  have h_inner : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-u) u := by
    have h_pow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
      simpa using (hasDerivAt_pow (n := 2) (x := u))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (h_pow.neg.div_const (2 : ℝ))
  have h_exp :
      HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2))
        (Real.exp (-(u ^ 2) / 2) * (-u)) u := by
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (x := (-(u ^ 2) / 2))).comp u h_inner
  have h_div :
      HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi))
        (Real.exp (-(u ^ 2) / 2) * (-u) / Real.sqrt (2 * Real.pi)) u := by
    simpa [div_eq_mul_inv] using h_exp.div_const (Real.sqrt (2 * Real.pi))
  simpa [mul_assoc, mul_left_comm, mul_comm, mul_div_assoc, div_eq_mul_inv, neg_mul, neg_div] using
    h_div

private lemma integrable_mul_φ : Integrable (fun x : ℝ => x * φ x) := by
  have h : Integrable (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) := by
    have h' :
        (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) =
          fun x : ℝ => x * Real.exp (-((1 / 2 : ℝ) * x ^ 2)) := by
      funext x
      ring_nf
    simpa [h'] using (integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num))
  simpa [φ, mul_div_assoc, mul_assoc] using h.div_const (Real.sqrt (2 * Real.pi))

private lemma integral_mul_φ_eq (u : ℝ) : (∫ x in Set.Ici u, x * φ x) = φ u := by
  have hderiv : ∀ x ∈ Set.Ici u, HasDerivAt φ (-x * φ x) x := by
    intro x _hx
    simpa using (hasDerivAt_φ x)
  have hint : IntegrableOn (fun x : ℝ => -x * φ x) (Set.Ioi u) := by
    simpa [neg_mul] using (integrable_mul_φ.neg).integrableOn
  have hIoi : (∫ x in Set.Ioi u, -x * φ x) = -φ u := by
    simpa using
      (MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
        (a := u) (f := φ) (f' := fun x : ℝ => -x * φ x) (m := (0 : ℝ)) hderiv hint
        tendsto_φ_atTop)
  have hIoi' : (∫ x in Set.Ioi u, x * φ x) = φ u := by
    have : -(∫ x in Set.Ioi u, -x * φ x) = φ u := by
      simpa using congrArg Neg.neg hIoi
    simpa [MeasureTheory.integral_neg, neg_mul] using this
  simpa [MeasureTheory.integral_Ici_eq_integral_Ioi] using hIoi'

private lemma tnm_tail_eq_Φbar (u : ℝ) : TruncatedNormalMoments.tail u = Φbar u := by
  simp [TruncatedNormalMoments.tail, Φbar, TruncatedNormalMoments.φ, φ]

private lemma tnm_J_one_eq (u : ℝ) : TruncatedNormalMoments.J 1 u = φ u - u * Φbar u := by
  have h₁ : (∫ x in Set.Ici u, x * φ x) = φ u := integral_mul_φ_eq u
  have h :
      φ u - u * Φbar u = ∫ x in Set.Ici u, (x - u) * φ x := by
    calc
      φ u - u * Φbar u
          = (∫ x in Set.Ici u, x * φ x) - u * (∫ x in Set.Ici u, φ x) := by
              simp [h₁, Φbar]
      _ = (∫ x in Set.Ici u, x * φ x) - ∫ x in Set.Ici u, u * φ x := by
            simp [MeasureTheory.integral_const_mul]
      _ = ∫ x in Set.Ici u, (x * φ x - u * φ x) := by
            have hi₁ : IntegrableOn (fun x : ℝ => x * φ x) (Set.Ici u) := integrable_mul_φ.integrableOn
            have hi₂ : IntegrableOn (fun x : ℝ => u * φ x) (Set.Ici u) :=
              (integrable_φ.const_mul u).integrableOn
            simpa using (MeasureTheory.integral_sub hi₁ hi₂).symm
      _ = ∫ x in Set.Ici u, (x - u) * φ x := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici ?_
            intro x _hx
            ring
  simpa [TruncatedNormalMoments.J, TruncatedNormalMoments.φ, φ, pow_one, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using h.symm

private lemma tnm_d_eq (u : ℝ) : TruncatedNormalMoments.d u = E u - u := by
  have htail : TruncatedNormalMoments.tail u = Φbar u := tnm_tail_eq_Φbar u
  have hJ1 : TruncatedNormalMoments.J 1 u = φ u - u * Φbar u := tnm_J_one_eq u
  have hΦ : Φbar u ≠ 0 := (DecreasingG.Φbar_pos u).ne'
  calc
    TruncatedNormalMoments.d u = TruncatedNormalMoments.J 1 u / TruncatedNormalMoments.tail u := rfl
    _ = (φ u - u * Φbar u) / Φbar u := by simp [hJ1, htail]
    _ = φ u / Φbar u - u := by
          field_simp [hΦ]
    _ = E u - u := rfl

private lemma Cκ_eq_tnm_J_two_neg (κ : ℝ) : Cκ κ = TruncatedNormalMoments.J 2 (-κ) := by
  have hv : (1 : NNReal) ≠ 0 := by simp
  calc
    Cκ κ = ∫ x : ℝ, φ x * (max (κ - x) 0) ^ 2 := by
      simpa [Cκ, Expect, γ, φ_eq_gaussianPDFReal, ProbabilityTheory.integral_gaussianReal_eq_integral_smul,
        hv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = ∫ x : ℝ, Set.indicator (Set.Iic κ) (fun y => (κ - y) ^ 2 * φ y) x := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : x ≤ κ
      · simp [hx, max_eq_left (sub_nonneg.2 hx), mul_comm, mul_left_comm, mul_assoc]
      · have hκx : κ < x := lt_of_not_ge hx
        have hmax : max (κ - x) 0 = 0 := by
          apply max_eq_right
          linarith
        simp [hx, hmax, mul_comm, mul_left_comm, mul_assoc]
    _ = ∫ x in Set.Iic κ, (κ - x) ^ 2 * φ x := by
      simpa using
        (MeasureTheory.integral_indicator (μ := (volume : Measure ℝ)) (s := Set.Iic κ)
          (f := fun x : ℝ => (κ - x) ^ 2 * φ x) measurableSet_Iic)
    _ = ∫ x in Set.Ioi (-κ), (x - (-κ)) ^ 2 * φ x := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, φ_even] using
        (integral_comp_neg_Iic (c := κ) (f := fun x => (x - (-κ)) ^ 2 * φ x))
    _ = ∫ x in Set.Ici (-κ), (x - (-κ)) ^ 2 * φ x := by
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    _ = TruncatedNormalMoments.J 2 (-κ) := by
      simp [TruncatedNormalMoments.J, TruncatedNormalMoments.φ, φ]

theorem Cκ_closed_form (κ : ℝ) : Cκ κ = (κ ^ 2 + 1) * Φ κ + κ * φ κ := by
  have htail_ne : TruncatedNormalMoments.tail (-κ) ≠ 0 := TruncatedNormalMoments.tail_ne_zero (-κ)
  have hΦneg_ne : Φbar (-κ) ≠ 0 := (DecreasingG.Φbar_pos (-κ)).ne'
  calc
    Cκ κ = TruncatedNormalMoments.J 2 (-κ) := Cκ_eq_tnm_J_two_neg κ
    _ = TruncatedNormalMoments.tail (-κ) * TruncatedNormalMoments.μ 2 (-κ) := by
      rw [TruncatedNormalMoments.μ]
      field_simp [htail_ne]
    _ = TruncatedNormalMoments.tail (-κ) * (1 + κ * TruncatedNormalMoments.d (-κ)) := by
      simp [TruncatedNormalMoments.μ_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]
    _ = Φbar (-κ) * (1 + κ * (E (-κ) + κ)) := by
      simp [tnm_tail_eq_Φbar, tnm_d_eq]
    _ = Φbar (-κ) * (κ ^ 2 + 1) + κ * φ κ := by
      rw [E, φ_even]
      field_simp [hΦneg_ne]
      ring
    _ = (κ ^ 2 + 1) * Φ κ + κ * φ κ := by
      rw [Φbar_neg_eq_Φ]
      ring

lemma αc_closed_form (κ : ℝ) : αc κ = 2 / (Real.pi * ((κ ^ 2 + 1) * Φ κ + κ * φ κ)) := by
  rw [αc]
  simp [Cκ_closed_form]

lemma IsSolution_iff (κ α q r : ℝ) :
    IsSolution κ α q r ↔ Theorem1.IsSolution κ α q r := by
  simp [IsSolution, Theorem1.IsSolution, P_eq, R_eq]

private theorem existsUnique_solution
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    ∃! qr : ℝ × ℝ, IsSolution κ α qr.1 qr.2 := by
  have hα' : α < Theorem1.αc κ := by
    simpa [αc_eq κ] using hα
  simpa [IsSolution_iff] using
    (Theorem1.theorem_main (κ := κ) (α := α) hκ hα0 hα')

private theorem no_solution
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα : αc κ ≤ α) :
    ¬ ∃ q r : ℝ, IsSolution κ α q r := by
  have hα' : Theorem1.αc κ ≤ α := by
    simpa [αc_eq κ] using hα
  simpa [IsSolution_iff] using
    (Theorem1.theorem_main_no_solution (κ := κ) (α := α) hκ hα')

theorem main
    (κ α : ℝ)
    (hκ : 0 ≤ κ) :
    (0 < α ∧ α < αc κ → ∃! qr : ℝ × ℝ, IsSolution κ α qr.1 qr.2) ∧
    (αc κ ≤ α → ¬ ∃ q r : ℝ, IsSolution κ α q r) := by
  constructor
  · rintro ⟨hα0, hα⟩
    exact existsUnique_solution κ α hκ hα0 hα
  · intro hα
    exact no_solution κ α hκ hα

noncomputable def sol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ × ℝ :=
  Classical.choose (existsUnique_solution κ α hκ hα0 hα).exists

lemma sol_spec (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) :
    IsSolution κ α (sol κ α hκ hα0 hα).1 (sol κ α hκ hα0 hα).2 := by
  simpa [sol] using
    (Classical.choose_spec (existsUnique_solution κ α hκ hα0 hα).exists)

abbrev qSol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  (sol κ α hκ hα0 hα).1

abbrev rSol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  (sol κ α hκ hα0 hα).2

lemma sol_eq
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    sol κ α hκ hα0 hα =
      Theorem1.sol κ α hκ hα0 (by simpa [αc_eq κ] using hα) := by
  apply (existsUnique_solution κ α hκ hα0 hα).unique
  · exact sol_spec κ α hκ hα0 hα
  · simpa [IsSolution_iff] using
      (Theorem1.sol_spec κ α hκ hα0 (by simpa [αc_eq κ] using hα))

lemma qSol_eq
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    qSol κ α hκ hα0 hα =
      Theorem1.qSol κ α hκ hα0 (by simpa [αc_eq κ] using hα) := by
  simp [qSol, Theorem1.qSol, sol_eq κ α hκ hα0 hα]

lemma rSol_eq
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    rSol κ α hκ hα0 hα =
      Theorem1.rSol κ α hκ hα0 (by simpa [αc_eq κ] using hα) := by
  simp [rSol, Theorem1.rSol, sol_eq κ α hκ hα0 hα]

def RSFunctional (κ α q r : ℝ) : ℝ :=
  -(r * (1 - q) / 2)
    + Expect (fun z => Real.log (2 * Real.cosh (Real.sqrt r * z)))
    + α * Expect (fun z => Real.log (Φbar ((κ - Real.sqrt q * z) / Real.sqrt (1 - q))))

def RSStar (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  RSFunctional κ α (qSol κ α hκ hα0 hα) (rSol κ α hκ hα0 hα)

def qAlpha (κ : ℝ) (hκ : 0 ≤ κ) (α : ℝ) : ℝ :=
  if hα : 0 < α ∧ α < αc κ then qSol κ α hκ hα.1 hα.2 else 0

def rAlpha (κ : ℝ) (hκ : 0 ≤ κ) (α : ℝ) : ℝ :=
  if hα : 0 < α ∧ α < αc κ then rSol κ α hκ hα.1 hα.2 else 0

def RSStarAlpha (κ : ℝ) (hκ : 0 ≤ κ) (α : ℝ) : ℝ :=
  if hα : 0 < α ∧ α < αc κ then RSStar κ α hκ hα.1 hα.2 else 0

lemma qAlpha_eq_qSol
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    qAlpha κ hκ α = qSol κ α hκ hα0 hα := by
  simp [qAlpha, hα0, hα]

lemma rAlpha_eq_rSol
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    rAlpha κ hκ α = rSol κ α hκ hα0 hα := by
  simp [rAlpha, hα0, hα]

lemma RSStarAlpha_eq_RSStar
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    RSStarAlpha κ hκ α = RSStar κ α hκ hα0 hα := by
  simp [RSStarAlpha, hα0, hα]

lemma RSFunctional_eq (κ α q r : ℝ) :
    RSFunctional κ α q r = Theorem3.RSFunctional κ α q r := by
  simp [RSFunctional, Theorem3.RSFunctional, Theorem3.Expect, Theorem1.Expect, Expect, γ,
    Theorem1.γ, Theorem3.Φbar, Theorem1.Φbar, Φbar, DecreasingG.Φbar, φ, DecreasingG.φ]

lemma RSStar_eq
    (κ α : ℝ)
    (hκ : 0 ≤ κ)
    (hα0 : 0 < α)
    (hα : α < αc κ) :
    RSStar κ α hκ hα0 hα =
      Theorem3.RSStar κ α hκ hα0 (by simpa [αc_eq κ] using hα) := by
  simp [RSStar, Theorem3.RSStar, RSFunctional_eq, qSol_eq, rSol_eq]

theorem second_main_seq
    (κ : ℝ) (hκ : 0 ≤ κ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 < α n ∧ α n < αc κ)
    (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    (Tendsto (fun n => rSol κ (α n) hκ (hα n).1 (hα n).2) atTop atTop) ∧
      Tendsto (fun n => qSol κ (α n) hκ (hα n).1 (hα n).2) atTop (𝓝 (1 : ℝ)) := by
  let hα' : ∀ n, 0 < α n ∧ α n < Theorem1.αc κ := fun n =>
    ⟨(hα n).1, by simpa [αc_eq κ] using (hα n).2⟩
  have hlim' : Tendsto α atTop (𝓝 (Theorem1.αc κ)) := by
    simpa [αc_eq κ] using hlim
  simpa [hα', qSol_eq, rSol_eq] using
    (Theorem1.theorem_second_main_seq (κ := κ) hκ (α := α) (hα := hα') hlim')

theorem third_main_seq
    (κ : ℝ) (hκ : 0 ≤ κ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 < α n ∧ α n < αc κ)
    (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    Tendsto (fun n => RSStar κ (α n) hκ (hα n).1 (hα n).2) atTop atBot := by
  let hα' : ∀ n, 0 < α n ∧ α n < Theorem1.αc κ := fun n =>
    ⟨(hα n).1, by simpa [αc_eq κ] using (hα n).2⟩
  have hlim' : Tendsto α atTop (𝓝 (Theorem1.αc κ)) := by
    simpa [αc_eq κ] using hlim
  simpa [hα', RSStar_eq] using
    (Theorem3.theorem_three_seq (κ := κ) (hκ := hκ) (α := α) (hα := hα') hlim')

private theorem exists_good_approx_seq
    (κ : ℝ)
    (α : ℕ → ℝ)
    (hlim : Tendsto α atTop (𝓝[<] (αc κ))) :
    ∃ α' : ℕ → ℝ,
      (∀ n, 0 < α' n ∧ α' n < αc κ) ∧
      Tendsto α' atTop (𝓝 (αc κ)) ∧
      (α' =ᶠ[atTop] α) := by
  let α' : ℕ → ℝ := fun n =>
    if hα : 0 < α n ∧ α n < αc κ then α n else αc κ / 2
  have hαc_pos : 0 < αc κ := αc_pos κ
  have hhalf : 0 < αc κ / 2 ∧ αc κ / 2 < αc κ := by
    constructor <;> linarith
  have hnhds : Tendsto α atTop (𝓝 (αc κ)) := (tendsto_nhdsWithin_iff.mp hlim).1
  have hlt : ∀ᶠ n in atTop, α n < αc κ := by
    simpa [Set.mem_Iio] using (tendsto_nhdsWithin_iff.mp hlim).2
  have hpos : ∀ᶠ n in atTop, 0 < α n := by
    have hIoi : Set.Ioi (αc κ / 2) ∈ 𝓝 (αc κ) := by
      refine IsOpen.mem_nhds isOpen_Ioi ?_
      exact hhalf.2
    have hmem : ∀ᶠ n in atTop, α n ∈ Set.Ioi (αc κ / 2) := hnhds.eventually hIoi
    refine hmem.mono ?_
    intro n hn
    linarith [hhalf.1, hn]
  have hgood : ∀ᶠ n in atTop, 0 < α n ∧ α n < αc κ := hpos.and hlt
  have hα'_eq : α' =ᶠ[atTop] α := by
    filter_upwards [hgood] with n hn
    simp [α', hn, hn.1, hn.2]
  have hα'_good : ∀ n, 0 < α' n ∧ α' n < αc κ := by
    intro n
    by_cases hα : 0 < α n ∧ α n < αc κ
    · simpa [α', hα] using hα
    · simp [α', hα, hhalf]
  have hα'_tendsto : Tendsto α' atTop (𝓝 (αc κ)) := hnhds.congr' hα'_eq.symm
  exact ⟨α', hα'_good, hα'_tendsto, hα'_eq⟩

theorem second_main
    (κ : ℝ) (hκ : 0 ≤ κ) :
    Tendsto (qAlpha κ hκ) (𝓝[<] (αc κ)) (𝓝 (1 : ℝ)) ∧
      Tendsto (rAlpha κ hκ) (𝓝[<] (αc κ)) atTop := by
  constructor
  · refine Filter.tendsto_of_seq_tendsto ?_
    intro α hlim
    obtain ⟨α', hα', hα'lim, hα'eq⟩ := exists_good_approx_seq κ α hlim
    have hseq := second_main_seq κ hκ α' hα' hα'lim
    have hq' :
        Tendsto (fun n => qAlpha κ hκ (α' n)) atTop (𝓝 (1 : ℝ)) := by
      have hq_eq :
          (fun n => qAlpha κ hκ (α' n)) =
            fun n => qSol κ (α' n) hκ (hα' n).1 (hα' n).2 := by
        funext n
        exact qAlpha_eq_qSol κ (α' n) hκ (hα' n).1 (hα' n).2
      rw [hq_eq]
      exact hseq.2
    have hq_event :
        (fun n => qAlpha κ hκ (α' n)) =ᶠ[atTop] (fun n => qAlpha κ hκ (α n)) := by
      exact hα'eq.mono (fun n hn => by simp [hn])
    exact hq'.congr' hq_event
  · refine Filter.tendsto_of_seq_tendsto ?_
    intro α hlim
    obtain ⟨α', hα', hα'lim, hα'eq⟩ := exists_good_approx_seq κ α hlim
    have hseq := second_main_seq κ hκ α' hα' hα'lim
    have hr' :
        Tendsto (fun n => rAlpha κ hκ (α' n)) atTop atTop := by
      have hr_eq :
          (fun n => rAlpha κ hκ (α' n)) =
            fun n => rSol κ (α' n) hκ (hα' n).1 (hα' n).2 := by
        funext n
        exact rAlpha_eq_rSol κ (α' n) hκ (hα' n).1 (hα' n).2
      rw [hr_eq]
      exact hseq.1
    have hr_event :
        (fun n => rAlpha κ hκ (α' n)) =ᶠ[atTop] (fun n => rAlpha κ hκ (α n)) := by
      exact hα'eq.mono (fun n hn => by simp [hn])
    exact hr'.congr' hr_event

theorem third_main
    (κ : ℝ) (hκ : 0 ≤ κ) :
    Tendsto (RSStarAlpha κ hκ) (𝓝[<] (αc κ)) atBot := by
  refine Filter.tendsto_of_seq_tendsto ?_
  intro α hlim
  obtain ⟨α', hα', hα'lim, hα'eq⟩ := exists_good_approx_seq κ α hlim
  have hseq := third_main_seq κ hκ α' hα' hα'lim
  have hRS' :
      Tendsto (fun n => RSStarAlpha κ hκ (α' n)) atTop atBot := by
    have hRS_eq :
        (fun n => RSStarAlpha κ hκ (α' n)) =
          fun n => RSStar κ (α' n) hκ (hα' n).1 (hα' n).2 := by
      funext n
      exact RSStarAlpha_eq_RSStar κ (α' n) hκ (hα' n).1 (hα' n).2
    rw [hRS_eq]
    exact hseq
  have hRS_event :
      (fun n => RSStarAlpha κ hκ (α' n)) =ᶠ[atTop] (fun n => RSStarAlpha κ hκ (α n)) := by
    exact hα'eq.mono (fun n hn => by simp [hn])
  exact hRS'.congr' hRS_event

end

end MainResult
