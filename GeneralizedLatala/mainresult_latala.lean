import Proof_of_generalized_latala.proof

open MeasureTheory ProbabilityTheory BigOperators
open PhysLean.Probability.GaussianIBP

namespace SpinGlass
namespace GeneralizedLatala

universe uΩ uι

variable {Ω : Type uΩ} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## Model -/

/-- Spin configurations on `N` sites. -/
abbrev ModelConfig (N : ℕ) := Fin N → Bool

/-- A centered Gaussian SK disorder with covariance
`N β² R(σ,τ)² / 2`. The parameter `h` records the external field used with the disorder. -/
structure ModelSKDisorder (N : ℕ) (β h : ℝ) where
  /-- The random energy field indexed by spin configurations. -/
  U : Ω → EnergySpace N
  /-- The field is a finite-dimensional centered Gaussian random vector. -/
  hU : IsGaussianHilbert U
  /-- Its covariance is the SK covariance kernel. -/
  cov_eq : ∀ σ τ,
    inner ℝ ((covOp (g := U) hU) (std_basis N σ)) (std_basis N τ) =
      (N * β ^ 2 / 2) *
        ((1 / (N : ℝ)) * ∑ i : Fin N,
          (if σ i then (1 : ℝ) else -1) *
            (if τ i then (1 : ℝ) else -1)) ^ 2

/-- Convert the explicit model specification to the disorder interface used by `proof.lean`. -/
noncomputable def ModelSKDisorder.toSKDisorder
    (sk : ModelSKDisorder.{uΩ, uι} (Ω := Ω) N β h) :
    SKDisorder.{uΩ, uι} (Ω := Ω) N β h where
  U := sk.U
  hU := sk.hU
  cov_eq := by
    intro σ τ
    rw [sk.cov_eq]
    rfl

/-- The value `±1` of a Boolean spin. -/
def modelSpin {N : ℕ} (σ : ModelConfig N) (i : Fin N) : ℝ :=
  if σ i then 1 else -1

/-- The normalized overlap of two configurations. -/
noncomputable def modelOverlap (N : ℕ) (σ τ : ModelConfig N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i : Fin N, modelSpin σ i * modelSpin τ i

/-- The SK energy at fixed disorder. Gibbs weights below use `exp (-modelEnergy)`. -/
noncomputable def modelEnergy
    (N : ℕ) (h : ℝ)
    (sk : ModelSKDisorder.{uΩ, uι} (Ω := Ω) N β h)
    (ω : Ω) (σ : ModelConfig N) : ℝ :=
  sk.U ω σ + h * ∑ i : Fin N, modelSpin σ i

/-- The finite-volume partition function. -/
noncomputable def modelPartitionFunction
    (N : ℕ) (h : ℝ)
    (sk : ModelSKDisorder.{uΩ, uι} (Ω := Ω) N β h) (ω : Ω) : ℝ :=
  ∑ σ : ModelConfig N, Real.exp (-modelEnergy N h sk ω σ)

/-- The Gibbs probability of a configuration at fixed disorder. -/
noncomputable def modelGibbsProbability
    (N : ℕ) (h : ℝ)
    (sk : ModelSKDisorder.{uΩ, uι} (Ω := Ω) N β h)
    (ω : Ω) (σ : ModelConfig N) : ℝ :=
  Real.exp (-modelEnergy N h sk ω σ) / modelPartitionFunction N h sk ω

/-- The quenched finite-volume pressure `φ_N`. -/
noncomputable def modelPressure
    (N : ℕ) (h : ℝ)
    (sk : ModelSKDisorder.{uΩ, uι} (Ω := Ω) N β h) : ℝ :=
  ∫ ω, (1 / (N : ℝ)) * Real.log (modelPartitionFunction N h sk ω) ∂ℙ

/-- The quantity `E⟨(R₁₂ - q)²⟩` appearing in the concentration claim. -/
noncomputable def modelOverlapSecondMoment
    (N : ℕ) (h q : ℝ)
    (sk : ModelSKDisorder.{uΩ, uι} (Ω := Ω) N β h) : ℝ :=
  ∫ ω, ∑ σs : Fin 2 → ModelConfig N,
    (modelOverlap N (σs 0) (σs 1) - q) ^ 2 *
      ∏ a : Fin 2, modelGibbsProbability N h sk ω (σs a) ∂ℙ

/-! ## Scalar replica-symmetric data -/

/-- Expectation against a standard real Gaussian. -/
noncomputable def modelGaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂gaussianReal 0 1

/-- The fixed-point equation `q = E[tanh(h + β √q Z)²]`. -/
def ModelFixedPoint (β h q : ℝ) : Prop :=
  q = modelGaussianExpectation
    (fun z => Real.tanh (h + β * Real.sqrt q * z) ^ 2)

/-- The Bernoulli sub-Gaussian coefficient from the blueprint. -/
noncomputable def modelKappa (q : ℝ) : ℝ :=
  if q = 0 then 1 else q / Real.artanh q

/-- The improved high-temperature parameter `ρ = β² κ(q)`. -/
noncomputable def modelRho (β q : ℝ) : ℝ :=
  β ^ 2 * modelKappa q

/-- The replica-symmetric pressure. -/
noncomputable def modelRSPressure (β h q : ℝ) : ℝ :=
  Real.log 2 +
    modelGaussianExpectation
      (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) +
    (β ^ 2 / 4) * (1 - q) ^ 2

/-! ## Claims -/

/-- The two `O(1/N)` conclusions in the blueprint, with one common constant. -/
def ModelClaims
    (N : ℕ) (β h q : ℝ)
    (sk : ModelSKDisorder.{uΩ, uι} (Ω := Ω) N β h) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    modelOverlapSecondMoment N h q sk ≤ C / (N : ℝ) ∧
    0 ≤ modelRSPressure β h q - modelPressure N h sk ∧
    modelRSPressure β h q - modelPressure N h sk ≤ C / (N : ℝ)

/-- The model and claims above are verified under the improved-region assumption. -/
theorem model_result
    (N : ℕ) [NeZero N] (β h q : ℝ)
    (sk : ModelSKDisorder.{uΩ, uι} (Ω := Ω) N β h)
    (sim : SimpleDisorder.{uΩ, uι} (Ω := Ω) N β q)
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : ModelFixedPoint β h q)
    (hρ : modelRho β q < 1)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) :
    ModelClaims N β h q sk := by
  let formalSK : SKDisorder.{uΩ, uι} (Ω := Ω) N β h :=
    sk.toSKDisorder
  have henergy (ω : Ω) (σ : ModelConfig N) :
      H_t (N := N) (β := β) (h := h) (q := q) (sk := formalSK) (sim := sim) 1 ω σ =
        modelEnergy N h sk ω σ := by
    simp [formalSK, ModelSKDisorder.toSKDisorder, H_t, H_gauss, H_field,
      modelEnergy, magnetic_field_vector,
      magnetization, modelSpin, spin]
  have hpressure :
      modelPressure N h sk =
        interpolatedPressure
          (N := N) (β := β) (h := h) (q := q) (sk := formalSK) (sim := sim) 1 := by
    apply integral_congr_ae
    filter_upwards with ω
    simp [free_energy_density, modelPartitionFunction, Z, henergy]
  have hoverlap :
      modelOverlapSecondMoment N h q sk =
        overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := formalSK) (sim := sim) 1 := by
    apply integral_congr_ae
    filter_upwards with ω
    apply Finset.sum_congr rfl
    intro σs _
    simp [centeredOverlapSq, modelOverlap, overlap, modelGibbsProbability,
      gibbs_pmf, modelPartitionFunction, Z, modelSpin, spin, henergy]
  have hmain := generalized_latala
    (N := N) (β := β) (h := h) (q := q) (sk := formalSK) (sim := sim)
    hN hq0 hq1 hfp hρ hIndep
  have hlambda : 0 < lambdaStar β q :=
    lambdaStar_pos (β := β) (q := q) hq0 hq1 hρ
  have hQ : 0 < quadraticConstant β q :=
    quadraticConstant_pos (β := β) (q := q) hq0 hq1 hρ
  let A : ℝ := quadraticConstant β q / lambdaStar β q
  let B : ℝ := β ^ 2 * quadraticConstant β q / (4 * lambdaStar β q)
  have hA : 0 ≤ A := by
    exact div_nonneg (le_of_lt hQ) (le_of_lt hlambda)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hNr : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hN
  have hoverlapA : modelOverlapSecondMoment N h q sk ≤ A / (N : ℝ) := by
    rw [hoverlap]
    calc
      overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := formalSK) (sim := sim) 1
          ≤ quadraticConstant β q / (lambdaStar β q * (N : ℝ)) := hmain.1
      _ = A / (N : ℝ) := by
        dsimp only [A]
        field_simp [ne_of_gt hlambda, hNr]
  have hpressure0 :
      0 ≤ modelRSPressure β h q - modelPressure N h sk := by
    rw [hpressure]
    exact hmain.2.1
  have hpressureB :
      modelRSPressure β h q - modelPressure N h sk ≤ B / (N : ℝ) := by
    rw [hpressure]
    calc
      rsPressure β h q -
          interpolatedPressure
            (N := N) (β := β) (h := h) (q := q) (sk := formalSK) (sim := sim) 1
          ≤ (β ^ 2 * quadraticConstant β q) /
              (4 * lambdaStar β q * (N : ℝ)) := hmain.2.2
      _ = B / (N : ℝ) := by
        dsimp only [B]
        field_simp [ne_of_gt hlambda, hNr]
  refine ⟨A + B, add_nonneg hA hB, ?_, hpressure0, ?_⟩
  · exact hoverlapA.trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_right hB) (Nat.cast_nonneg N))
  · exact hpressureB.trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_left hA) (Nat.cast_nonneg N))

end GeneralizedLatala
end SpinGlass
