import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Analysis.NormedSpace.EuclideanSpace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Real

namespace GaussianConcentration

abbrev E (n : ℕ) := Fin n → ℝ

def γ1 : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 1

def γ (n : ℕ) : Measure (E n) :=
  Measure.pi fun _ : Fin n => γ1

instance instProbGamma1 : IsProbabilityMeasure γ1 := by
  dsimp [γ1]
  infer_instance

instance instProbGamma (n : ℕ) : IsProbabilityMeasure (γ n) := by
  dsimp [γ]
  infer_instance

lemma measurable_of_lipschitz
    {n : ℕ} {f : E n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Measurable f :=
  hf.continuous.measurable

lemma integrable_of_lipschitz_gaussian
    {n : ℕ} {f : E n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Integrable f (γ n) := by
  sorry

def centered {n : ℕ} (f : E n → ℝ) (x : E n) : ℝ :=
  f x - ∫ y, f y ∂(γ n)

lemma measurable_centered_of_lipschitz
    {n : ℕ} {f : E n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Measurable (centered f) := by
  simpa [centered] using (measurable_of_lipschitz hf).sub measurable_const

lemma measurableSet_upper_tail
    {n : ℕ} {f : E n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (t : ℝ) :
    MeasurableSet {x | centered f x ≥ t} := by
  simpa [ge_iff_le] using
    measurableSet_le measurable_const (measurable_centered_of_lipschitz hf)

def Entropy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → ℝ) : ℝ :=
  (∫ x, F x * Real.log (F x) ∂μ) -
    (∫ x, F x ∂μ) * Real.log (∫ x, F x ∂μ)

def SmoothEnough {n : ℕ} (g : E n → ℝ) : Prop :=
  True

def localLipBound {n : ℕ} (g : E n → ℝ) (x : E n) : ℝ :=
  0

theorem gaussian_logSobolev
    {n : ℕ} {g : E n → ℝ}
    (hg_smooth : SmoothEnough g) :
    Entropy (γ n) (fun x => Real.exp (g x))
      ≤ (1 / 2 : ℝ) *
        ∫ x, Real.exp (g x) * localLipBound g x ^ 2 ∂(γ n) := by
  sorry

theorem gaussian_logSobolev_lipschitz
    {n : ℕ} {g : E n → ℝ}
    (hg : LocallyLipschitz g) :
    Entropy (γ n) (fun x => Real.exp (g x))
      ≤ (1 / 2 : ℝ) *
        ∫ x, Real.exp (g x) * localLipBound g x ^ 2 ∂(γ n) := by
  sorry

theorem herbst_mgf_bound
    {n : ℕ} {f : E n → ℝ} {L λ : ℝ}
    (hL : LipschitzWith (Real.toNNReal L) f)
    (hLnonneg : 0 ≤ L)
    (hλ : 0 ≤ λ) :
    ∫ x, Real.exp (λ * centered f x) ∂(γ n)
      ≤ Real.exp ((λ ^ 2 * L ^ 2) / 2) := by
  sorry

theorem chernoff_from_mgf
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ t : ℝ}
    (hσpos : 0 < σ)
    (ht : 0 ≤ t)
    (hmgf : ∀ λ : ℝ, 0 ≤ λ →
      ∫ ω, Real.exp (λ * X ω) ∂μ ≤ Real.exp (λ ^ 2 * σ ^ 2 / 2)) :
    μ {ω | X ω ≥ t}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * σ ^ 2))) := by
  sorry

theorem gaussian_concentration_one_sided
    {n : ℕ} {f : E n → ℝ} {L t : ℝ}
    (hL : LipschitzWith (Real.toNNReal L) f)
    (hLpos : 0 < L)
    (ht : 0 ≤ t) :
    γ n {x | f x - ∫ y, f y ∂(γ n) ≥ t}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * L ^ 2))) := by
  simpa [centered] using
    chernoff_from_mgf
      (μ := γ n)
      (X := centered f)
      (σ := L)
      hLpos
      ht
      (fun λ hλ => herbst_mgf_bound hL (le_of_lt hLpos) hλ)

theorem gaussian_concentration_two_sided
    {n : ℕ} {f : E n → ℝ} {L t : ℝ}
    (hL : LipschitzWith (Real.toNNReal L) f)
    (hLpos : 0 < L)
    (ht : 0 ≤ t) :
    γ n {x | |f x - ∫ y, f y ∂(γ n)| ≥ t}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * L ^ 2))) := by
  sorry

end GaussianConcentration
