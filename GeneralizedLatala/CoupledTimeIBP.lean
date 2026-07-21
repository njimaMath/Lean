import latala

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass
namespace GeneralizedLatala

/-!
# Proof workspace for `coupledFreeEnergy_hasDerivAt_time_ibp`

This file deliberately imports `latala.lean` and proves a new theorem with the same
statement under the name

`coupledFreeEnergy_hasDerivAt_time_ibp_reproved`.

The proof is split into the following layers.

1. Differentiate under the disorder integral. This is already supplied by
   `coupledFreeEnergy_hasDerivAt_time_before_ibp`.
2. Apply joint Gaussian integration by parts to obtain a covariance/Hessian trace.
3. Evaluate that trace by finite replica algebra.
4. Rewrite the deterministic tilted observables as their annealed integrals.

The final theorem contains no additional analysis: it follows immediately from the
raw differentiation theorem and `coupledFreeEnergy_time_derivative_ibp_formula`.
-/

variable {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (N : ℕ) [NeZero N] (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) N β h)
variable (sim : SimpleDisorder (Ω := Ω) N β q)

/-! ## Tilted deterministic Gibbs averages -/

/-- Evaluation of a Hamiltonian direction on the two replicas. -/
noncomputable def pairEval
    (u : EnergySpace N) : ReplicaFun N 2 :=
  fun σs => u (σs 0) + u (σs 1)

/-- Expectation under the normalized quadratically tilted two-replica Gibbs law. -/
noncomputable def tiltedReplicaAverageDet
    (H : EnergySpace N) (coupling : ℝ)
    (f : ReplicaFun N 2) : ℝ :=
  gibbs_average_n_det (N := N) (n := 2) H
      (fun σs =>
        f σs *
          Real.exp
            (coupling * (N : ℝ) * centeredOverlapSq N q σs)) /
    tiltedReplicaPartitionDet (N := N) (q := q) H coupling

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma tiltedReplicaAverageDet_one
    (H : EnergySpace N) (coupling : ℝ) :
    tiltedReplicaAverageDet
        (N := N) (q := q) H coupling (fun _ => 1) = 1 := by
  unfold tiltedReplicaAverageDet tiltedReplicaPartitionDet
  simp only [one_mul]
  exact div_self
    (ne_of_gt
      (tiltedReplicaPartitionDet_pos
        (N := N) (q := q) H coupling))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma tiltedReplicaAverageDet_centeredOverlapSq
    (H : EnergySpace N) (coupling : ℝ) :
    tiltedReplicaAverageDet
        (N := N) (q := q) H coupling
        (centeredOverlapSq N q) =
      tiltedCenteredOverlapSqDet
        (N := N) (q := q) H coupling := by
  rfl

/-- Explicit Hessian of the normalized coupled two-replica free energy.

The formula is the covariance of `pairEval u` and `pairEval v` under the tilted law,
with normalization `1 / (2N)`.
-/
noncomputable def coupledHessianDet
    (H : EnergySpace N) (coupling : ℝ)
    (u v : EnergySpace N) : ℝ :=
  (1 / (2 * (N : ℝ))) *
    (tiltedReplicaAverageDet
        (N := N) (q := q) H coupling
        (fun σs =>
          pairEval (N := N) u σs * pairEval (N := N) v σs) -
      tiltedReplicaAverageDet
        (N := N) (q := q) H coupling
        (pairEval (N := N) u) *
      tiltedReplicaAverageDet
        (N := N) (q := q) H coupling
        (pairEval (N := N) v))

/-! ## Calculus layer

These are the first lemmas to prove. They use finite sums, the quotient rule,
`fderiv_gibbs_average_n_det_apply`, and positivity of
`tiltedReplicaPartitionDet`.
-/

/-- First Hamiltonian derivative of the deterministic coupled free energy. -/
lemma fderiv_coupledFreeEnergyDet_apply_workspace
    (H u : EnergySpace N) (Λ : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          coupledFreeEnergyDet (N := N) (q := q) K Λ)
        H u =
      -(1 / (2 * (N : ℝ))) *
        tiltedReplicaAverageDet
          (N := N) (q := q) H (Λ / 2)
          (pairEval (N := N) u) := by
  /-
  Suggested proof:

  * unfold `coupledFreeEnergyDet`;
  * differentiate `free_energy_density` using
    `fderiv_free_energy_density_apply`;
  * differentiate the logarithm of the tilted partition function;
  * use `fderiv_gibbs_average_n_det_apply` for its Hamiltonian derivative;
  * collect the two ordinary Gibbs-average terms, which cancel;
  * divide by the positive tilted partition function.
  -/
  sorry

/-- Second Hamiltonian derivative of the deterministic coupled free energy. -/
lemma fderiv_coupledFirstVariation_apply_workspace
    (H u v : EnergySpace N) (Λ : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          fderiv ℝ
            (fun L : EnergySpace N =>
              coupledFreeEnergyDet (N := N) (q := q) L Λ)
            K u)
        H v =
      coupledHessianDet
        (N := N) (q := q) H (Λ / 2) u v := by
  /-
  Rewrite the inner derivative with
  `fderiv_coupledFreeEnergyDet_apply_workspace` and differentiate the
  normalized tilted expectation. The quotient rule gives exactly the
  tilted covariance in `coupledHessianDet`.
  -/
  sorry

/-! ## Gaussian-IBP trace layer -/

/-- Joint Gaussian IBP for the smart-path derivative, expressed as a canonical
configuration-basis covariance trace.

This should be proved with `UV`, `isGaussianHilbert_UV`, and
`gaussian_integration_by_parts_hilbert_cov_op`, following the existing proof of
`pressure_derivative_ibp_trace` and the scratch development in
`.tmp_gaussian_interp.lean`.
-/
lemma coupledFreeEnergy_time_ibp_trace_workspace
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t Λ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ w,
        fderiv ℝ
          (fun H : EnergySpace N =>
            coupledFreeEnergyDet (N := N) (q := q) H Λ)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t w)
          (dH_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t w)
        ∂ℙ) =
      (1 / 2) *
        ∫ w,
          (∑ σ : Config N, ∑ τ : Config N,
            (sk_cov_kernel N β σ τ -
              simple_cov_kernel N β (fun x => q * x) σ τ) *
              coupledHessianDet
                (N := N) (q := q)
                (H_t
                  (N := N) (β := β) (h := h) (q := q)
                  (sk := sk) (sim := sim) t w)
                (Λ / 2)
                (std_basis N σ) (std_basis N τ))
          ∂ℙ := by
  /-
  Recommended structure:

  1. set `a = sqrt t`, `b = sqrt (1-t)`,
     `a' = 1/(2*sqrt t)`, `b' = -1/(2*sqrt (1-t))`;
  2. package `(sk.U, sim.V)` using `isGaussianHilbert_UV hIndep`;
  3. apply Gaussian IBP to the first variation of `coupledFreeEnergyDet`;
  4. rewrite the derivative using
     `fderiv_coupledFirstVariation_apply_workspace`;
  5. split the product-Hilbert eigenbasis trace into the U and V blocks;
  6. change each eigenbasis trace to the canonical `std_basis` trace;
  7. use `sk.cov_eq` and `sim.cov_eq`;
  8. simplify `a*a' = 1/2` and `b*b' = -1/2`.
  -/
  sorry

/-! ## Finite replica algebra -/

lemma covKernelDiff_eq_centered_sq_workspace
    (σ τ : Config N) :
    sk_cov_kernel N β σ τ -
        simple_cov_kernel N β (fun x => q * x) σ τ =
      ((N : ℝ) * β ^ 2 / 2) *
        ((overlap N σ τ - q) ^ 2 - q ^ 2) := by
  simp [sk_cov_kernel, simple_cov_kernel]
  ring

lemma sum_crossPairCenteredOverlapSq_workspace
    (σs : ReplicaSpace N 4) :
    (centeredOverlap
        (N := N) (q := q)
        (0 : Fin 4) (2 : Fin 4) σs) ^ 2 +
      (centeredOverlap
        (N := N) (q := q)
        (0 : Fin 4) (3 : Fin 4) σs) ^ 2 +
      (centeredOverlap
        (N := N) (q := q)
        (1 : Fin 4) (2 : Fin 4) σs) ^ 2 +
      (centeredOverlap
        (N := N) (q := q)
        (1 : Fin 4) (3 : Fin 4) σs) ^ 2 =
      4 * crossPairCenteredOverlapSq
        (N := N) (q := q) σs := by
  unfold crossPairCenteredOverlapSq
  ring

/-- Pointwise finite-volume trace identity.

This is the main algebraic goal. Unfold `coupledHessianDet`; the first tilted
expectation gives `(1-q)^2 + tilted Q₁₂²`, while the product of tilted means is
represented by four replicas and gives `2 * coupledCrossMomentDet` after all
normalizations are collected.
-/
lemma coupled_trace_algebra_workspace
    (hN : 0 < N)
    (H : EnergySpace N) (coupling : ℝ) :
    (1 / 2) *
        (∑ σ : Config N, ∑ τ : Config N,
          (sk_cov_kernel N β σ τ -
            simple_cov_kernel N β (fun x => q * x) σ τ) *
            coupledHessianDet
              (N := N) (q := q) H coupling
              (std_basis N σ) (std_basis N τ)) =
      (β ^ 2 / 4) *
        ((1 - q) ^ 2 +
          tiltedCenteredOverlapSqDet
            (N := N) (q := q) H coupling -
          2 * coupledCrossMomentDet
            (N := N) (q := q) H coupling) := by
  /-
  Useful ingredients:

  * `covKernelDiff_eq_centered_sq_workspace`;
  * `overlap_self hN`;
  * `sum_gibbs_pmf` and `sum_prod_gibbs_pmf_eq_one`;
  * `tiltedReplicaPartitionDet_pos`;
  * an explicit equivalence
    `ReplicaSpace N 4 ≃ ReplicaSpace N 2 × ReplicaSpace N 2`;
  * `sum_crossPairCenteredOverlapSq_workspace`.
  -/
  sorry

/-! ## Integrability of the normalized finite-state observables -/

lemma integrable_tiltedCenteredOverlapSqDet_Ht_workspace
    (t coupling : ℝ) :
    Integrable
      (fun ω =>
        tiltedCenteredOverlapSqDet
          (N := N) (q := q)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t ω)
          coupling) ℙ := by
  /-
  The tilted quantity is a normalized expectation of a fixed observable on a
  finite state space. Bound it by

    `∑ σs : ReplicaSpace N 2, |centeredOverlapSq N q σs|`.
  -/
  sorry

lemma integrable_coupledCrossMomentDet_Ht_workspace
    (t coupling : ℝ) :
    Integrable
      (fun ω =>
        coupledCrossMomentDet
          (N := N) (q := q)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t ω)
          coupling) ℙ := by
  /-
  Again use the normalized finite four-replica law and bound by the finite sum
  of `|crossPairCenteredOverlapSq|`.
  -/
  sorry

/-! ## Evaluate the raw differentiated integral -/

lemma coupledFreeEnergy_time_derivative_ibp_formula_workspace
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t Λ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ ω,
        fderiv ℝ
          (fun H : EnergySpace N =>
            coupledFreeEnergyDet (N := N) (q := q) H Λ)
          (H_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t ω)
          (dH_t
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t ω)
        ∂ℙ) =
      (β ^ 2 / 4) *
        ((1 - q) ^ 2 +
          tiltedCenteredOverlapSq
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2) -
          2 * coupledCrossMoment
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2)) := by
  let T : Ω → ℝ := fun ω =>
    tiltedCenteredOverlapSqDet
      (N := N) (q := q)
      (H_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t ω)
      (Λ / 2)
  let X : Ω → ℝ := fun ω =>
    coupledCrossMomentDet
      (N := N) (q := q)
      (H_t
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t ω)
      (Λ / 2)

  have hT : Integrable T ℙ := by
    simpa only [T] using
      integrable_tiltedCenteredOverlapSqDet_Ht_workspace
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t (Λ / 2)

  have hX : Integrable X ℙ := by
    simpa only [X] using
      integrable_coupledCrossMomentDet_Ht_workspace
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t (Λ / 2)

  have hconst : Integrable (fun _ : Ω => (1 - q) ^ 2) ℙ :=
    integrable_const _

  have hsum : Integrable (fun ω => (1 - q) ^ 2 + T ω) ℙ :=
    hconst.add hT

  have htwiceX : Integrable (fun ω => 2 * X ω) ℙ :=
    hX.const_mul 2

  rw [coupledFreeEnergy_time_ibp_trace_workspace
    (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) hIndep ht]

  rw [← integral_const_mul]

  rw [integral_congr_ae
    (ae_of_all _ fun ω =>
      coupled_trace_algebra_workspace
        (N := N) (β := β) (q := q) hN
        (H_t
          (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t ω)
        (Λ / 2))]

  rw [integral_const_mul]
  rw [integral_sub hsum htwiceX]
  rw [integral_add hconst hT]
  rw [integral_const]
  rw [integral_const_mul]

  simp only [probReal_univ, one_smul]

  change
    (β ^ 2 / 4) *
        ((1 - q) ^ 2 + (∫ ω, T ω ∂ℙ) - 2 * (∫ ω, X ω ∂ℙ)) =
      (β ^ 2 / 4) *
        ((1 - q) ^ 2 +
          tiltedCenteredOverlapSq
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2) -
          2 * coupledCrossMoment
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2))

  simp only [T, X, tiltedCenteredOverlapSq, coupledCrossMoment]

/-! ## Final theorem -/

/-- A non-circular reproof target for the theorem in `latala.lean`.

Once `coupledFreeEnergy_time_derivative_ibp_formula_workspace` is complete, this
proof should remain exactly this short.
-/
lemma coupledFreeEnergy_hasDerivAt_time_ibp_reproved
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t Λ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => coupledFreeEnergy
        (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) s Λ)
      ((β ^ 2 / 4) *
        ((1 - q) ^ 2 +
          tiltedCenteredOverlapSq
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2) -
          2 * coupledCrossMoment
            (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t (Λ / 2))) t := by
  rw [← coupledFreeEnergy_time_derivative_ibp_formula_workspace
    (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) hN hIndep ht]

  exact coupledFreeEnergy_hasDerivAt_time_before_ibp
    (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) ht

end GeneralizedLatala
end SpinGlass
