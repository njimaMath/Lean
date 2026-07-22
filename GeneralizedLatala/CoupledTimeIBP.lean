import latala

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

set_option maxHeartbeats 800000

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

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma fderiv_tiltedReplicaPartitionDet_apply_workspace
    (H u : EnergySpace N) (coupling : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          tiltedReplicaPartitionDet (N := N) (q := q) K coupling)
        H u =
      2 * (∑ τ : Config N, gibbs_pmf N H τ * u τ) *
          tiltedReplicaPartitionDet (N := N) (q := q) H coupling -
        gibbs_average_n_det (N := N) (n := 2) H
          (fun σs =>
            pairEval (N := N) u σs *
              Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs)) := by
  unfold gibbs_average_n_det pairEval;
  unfold gibbs_pmf tiltedReplicaPartitionDet;
  rw [ fderiv_gibbs_average_n_det_apply ];
  unfold gibbs_average_n_det gibbs_pmf;
  simp +decide [ Fin.sum_univ_two, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ]

/-
First Hamiltonian derivative of the deterministic coupled free energy.
-/
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
  erw [ fderiv_add ] <;> norm_num [ fderiv_free_energy_density_apply ];
  · erw [ fderiv_mul, fderiv.log ] <;> norm_num [ fderiv_tiltedReplicaPartitionDet_apply_workspace ];
    · unfold tiltedReplicaAverageDet; ring;
      rw [ mul_inv_cancel_right₀ ( ne_of_gt ( tiltedReplicaPartitionDet_pos _ _ _ _ ) ) ] ; ring;
    · -- The sum of differentiable functions is differentiable.
      have h_diff : ∀ σs : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (Λ / 2 * N * centeredOverlapSq N q σs) * ∏ l, Real.exp (-K.ofLp (σs l)) / Z N K) H := by
        intro σs;
        have h_diff : ∀ l : Fin 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (-K.ofLp (σs l)) / Z N K) H := by
          exact fun l => differentiableAt_gibbs_pmf N H (σs l)
        fun_prop
      exact DifferentiableAt.fun_sum fun i _ => h_diff i
    · exact ne_of_gt (tiltedReplicaPartitionDet_pos N q H (Λ / 2));
    · refine' DifferentiableAt.log _ _;
      · unfold tiltedReplicaPartitionDet gibbs_average_n_det;
        unfold gibbs_pmf; norm_num [ Real.exp_ne_zero, Finset.prod_eq_zero_iff, Real.differentiableAt_exp, differentiableAt_pi ] ;
        have h_diff : ∀ x : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (-K.ofLp (x 0)) * Real.exp (-K.ofLp (x 1)) / Z N K ^ 2) H := by
          intro x;
          apply_rules [ DifferentiableAt.div, DifferentiableAt.mul, DifferentiableAt.exp, differentiableAt_id, differentiableAt_const ];
          · fun_prop;
          · fun_prop;
          · apply_rules [ DifferentiableAt.inv, DifferentiableAt.pow, differentiableAt_id ];
            · unfold Z;
              fun_prop;
            · exact ne_of_gt ( sq_pos_of_pos ( Z_pos N H ) );
        fun_prop;
      · exact ne_of_gt ( tiltedReplicaPartitionDet_pos N q H ( Λ / 2 ) );
  · apply_rules [ DifferentiableAt.mul, DifferentiableAt.log ] <;> norm_num;
    · unfold Z ;
      fun_prop;
    · exact ne_of_gt ( Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty );
  · apply_rules [ DifferentiableAt.mul, DifferentiableAt.log ] <;> norm_num [ tiltedReplicaPartitionDet_pos ];
    · unfold tiltedReplicaPartitionDet;
      unfold gibbs_average_n_det; norm_num [ gibbs_average_n, gibbs_pmf ] ;
      have h_diff : DifferentiableAt ℝ (fun x : EnergySpace N => (∑ σ : Config N, Real.exp (-x σ))) H := by
        fun_prop;
      simp_all +decide [ ← mul_div_assoc, ← Finset.sum_div _ _ _ ];
      refine' DifferentiableAt.mul _ _;
      · fun_prop;
      · exact DifferentiableAt.inv ( h_diff.pow 2 ) ( ne_of_gt ( sq_pos_of_pos ( Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ( Finset.univ_nonempty ) ) ) );
    · exact ne_of_gt (tiltedReplicaPartitionDet_pos N q H (Λ / 2))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma differentiableAt_tiltedReplicaAverageDet_workspace
    (H : EnergySpace N) (coupling : ℝ) (f : ReplicaFun N 2) :
    DifferentiableAt ℝ
      (fun K : EnergySpace N =>
        tiltedReplicaAverageDet (N := N) (q := q) K coupling f) H := by
  refine' DifferentiableAt.congr_of_eventuallyEq _ _;
  exact fun K => (∑ σs : ReplicaSpace N 2, (∏ l : Fin 2, gibbs_pmf N K (σs l)) * f σs * Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs)) / (∑ σs : ReplicaSpace N 2, (∏ l : Fin 2, gibbs_pmf N K (σs l)) * Real.exp (coupling * (N : ℝ) * centeredOverlapSq N q σs));
  · refine' DifferentiableAt.mul _ _;
    · have h_diff : ∀ σs : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => ∏ l : Fin 2, gibbs_pmf N K (σs l)) H := by
        exact fun σs => differentiableAt_prod_gibbs_pmf N 2 H σs;
      fun_prop;
    · refine' DifferentiableAt.inv _ _;
      · have h_diff : ∀ σ : Config N, DifferentiableAt ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) H := by
          exact fun σ => differentiableAt_gibbs_pmf N H σ;
        fun_prop (disch := norm_num);
      · refine' ne_of_gt ( lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => _ ) ( Finset.mem_univ ( fun _ => fun _ => Bool.true ) ) ) );
        · exact mul_pos ( Finset.prod_pos fun _ _ => gibbs_pmf_pos _ _ _ ) ( Real.exp_pos _ );
        · exact mul_nonneg ( Finset.prod_nonneg fun _ _ => div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) ) ( Real.exp_nonneg _ );
  · filter_upwards [ ] with K ; unfold tiltedReplicaAverageDet gibbs_average_n_det tiltedReplicaPartitionDet ; simp +decide [ Finset.prod_mul_distrib, mul_assoc ] ;
    unfold gibbs_average_n_det; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma fderiv_tiltedReplicaAverageDet_apply_workspace
    (H u v : EnergySpace N) (coupling : ℝ) :
    fderiv ℝ
        (fun K : EnergySpace N =>
          tiltedReplicaAverageDet (N := N) (q := q) K coupling
            (pairEval (N := N) u))
        H v =
      - (tiltedReplicaAverageDet (N := N) (q := q) H coupling
            (fun σs => pairEval (N := N) u σs * pairEval (N := N) v σs) -
          tiltedReplicaAverageDet (N := N) (q := q) H coupling
            (pairEval (N := N) u) *
          tiltedReplicaAverageDet (N := N) (q := q) H coupling
            (pairEval (N := N) v)) := by
  unfold tiltedReplicaAverageDet;
  erw [ fderiv_mul ];
  · erw [ fderiv_comp _ ( show DifferentiableAt ℝ ( fun x => x⁻¹ ) _ from differentiableAt_inv _ ) ];
    · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, fderiv_tiltedReplicaPartitionDet_apply_workspace, fderiv_gibbs_average_n_det_apply ];
      unfold gibbs_average_n_det; ring;
      unfold pairEval; simp +decide [ Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ; ring;
      by_cases h : tiltedReplicaPartitionDet N q H coupling = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring;
      simp +decide [ Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring;
    · apply_rules [ ContDiff.differentiable ];
      apply_rules [ ContDiff.sum, ContDiff.mul, ContDiff.exp, contDiff_const, contDiff_id ];
      any_goals exact ⊤;
      · intro i hi; apply_rules [ ContDiff.mul, ContDiff.exp, contDiff_const, contDiff_id ] ;
        · fun_prop;
        · refine' ContDiff.inv _ _;
          · refine' ContDiff.sum fun σ _ => ContDiff.exp _;
            fun_prop;
          · exact fun x => ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty;
        · fun_prop;
        · refine' ContDiff.inv _ _;
          · refine' ContDiff.sum fun σ _ => ContDiff.exp _;
            fun_prop;
          · exact fun x => ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty;
      · norm_num;
    · refine' ne_of_gt ( _ );
      exact tiltedReplicaPartitionDet_pos _ _ _ _;
  · unfold gibbs_average_n_det;
    simp +decide [ gibbs_pmf ];
    have h_diff : DifferentiableAt ℝ (fun K : EnergySpace N => Z N K) H := by
      unfold Z ;
      fun_prop (disch := norm_num);
    have h_diff : ∀ x : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (-K.ofLp (x 0)) * Real.exp (-K.ofLp (x 1)) / Z N K ^ 2) H := by
      intro x;
      refine' DifferentiableAt.mul _ _;
      · fun_prop;
      · exact DifferentiableAt.inv ( h_diff.pow 2 ) ( by exact ne_of_gt ( sq_pos_of_pos ( Z_pos ( N := N ) H ) ) );
    fun_prop;
  · apply DifferentiableAt.inv;
    · unfold tiltedReplicaPartitionDet;
      unfold gibbs_average_n_det;
      unfold gibbs_pmf; norm_num [ Finset.prod_mul_distrib, Real.exp_ne_zero ] ;
      have h_diff : ∀ σ : Config N, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (-K.ofLp σ)) H := by
        fun_prop (disch := solve_by_elim);
      have h_diff : DifferentiableAt ℝ (fun K : EnergySpace N => Z N K) H := by
        convert DifferentiableAt.sum fun σ _ => h_diff σ using 1;
        swap;
        exacts [ Finset.univ, funext fun K => by simp +decide [ Z ] ];
      have h_diff : ∀ x : ReplicaSpace N 2, DifferentiableAt ℝ (fun K : EnergySpace N => Real.exp (-K.ofLp (x 0)) * Real.exp (-K.ofLp (x 1)) / Z N K ^ 2) H := by
        intro x;
        apply_rules [ DifferentiableAt.div, DifferentiableAt.mul, DifferentiableAt.exp, differentiableAt_id, differentiableAt_const ];
        exact DifferentiableAt.inv ( h_diff.pow 2 ) ( pow_ne_zero _ <| ne_of_gt <| Z_pos N H );
      fun_prop;
    · refine' ne_of_gt ( _ );
      exact tiltedReplicaPartitionDet_pos _ _ _ _

/-
Second Hamiltonian derivative of the deterministic coupled free energy.
-/
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
  have h_deriv : (fderiv ℝ (fun K => (fderiv ℝ (fun L => coupledFreeEnergyDet N q L Λ) K) u) H) v = -(1 / (2 * (N : ℝ))) * (fderiv ℝ (fun K => tiltedReplicaAverageDet N q K (Λ / 2) (pairEval N u)) H) v := by
    rw [ show ( fun K => ( fderiv ℝ ( fun L => coupledFreeEnergyDet N q L Λ ) K ) u ) = fun K => - ( 1 / ( 2 * N ) ) * tiltedReplicaAverageDet N q K ( Λ / 2 ) ( pairEval N u ) from funext fun K => fderiv_coupledFreeEnergyDet_apply_workspace N q K u Λ ];
    rw [ fderiv_const_mul ] ; norm_num [ differentiableAt_tiltedReplicaAverageDet_workspace ];
    exact differentiableAt_tiltedReplicaAverageDet_workspace N q H (Λ / 2) (pairEval N u)
  rw [ h_deriv, fderiv_tiltedReplicaAverageDet_apply_workspace ] ; unfold coupledHessianDet ; ring

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

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma sum_pairEval_std_basis_product_workspace
    (D : Config N → Config N → ℝ) (σs : ReplicaSpace N 2) :
    (∑ σ : Config N, ∑ τ : Config N,
      D σ τ * pairEval N (std_basis N σ) σs *
        pairEval N (std_basis N τ) σs) =
      D (σs 0) (σs 0) + D (σs 0) (σs 1) +
        D (σs 1) (σs 0) + D (σs 1) (σs 1) := by
  simp only [pairEval, std_basis]
  ring_nf
  simp_rw [Finset.sum_add_distrib]
  simp

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma sum_pairEval_std_basis_cross_workspace
    (D : Config N → Config N → ℝ)
    (σs ρs : ReplicaSpace N 2) :
    (∑ σ : Config N, ∑ τ : Config N,
      D σ τ * pairEval N (std_basis N σ) σs *
        pairEval N (std_basis N τ) ρs) =
      D (σs 0) (ρs 0) + D (σs 0) (ρs 1) +
        D (σs 1) (ρs 0) + D (σs 1) (ρs 1) := by
  simp only [pairEval, std_basis]
  ring_nf
  simp_rw [Finset.sum_add_distrib]
  simp

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

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma fourReplicaTiltWeight_sum_workspace
    (H : EnergySpace N) (coupling : ℝ) :
    (∑ σs : ReplicaSpace N 4,
      Real.exp (coupling * (N : ℝ) *
        ((centeredOverlap (N := N) (q := q) (0 : Fin 4) (1 : Fin 4) σs) ^ 2 +
          (centeredOverlap (N := N) (q := q) (2 : Fin 4) (3 : Fin 4) σs) ^ 2)) *
        ∏ l, gibbs_pmf N H (σs l)) =
      (tiltedReplicaPartitionDet (N := N) (q := q) H coupling) ^ 2 := by
  rw [ sq, tiltedReplicaPartitionDet ];
  unfold gibbs_average_n_det;
  simp +decide only [Fin.prod_univ_two, Finset.sum_mul];
  simp +decide only [Finset.mul_sum _ _ _];
  rw [ ← Finset.sum_product' ];
  refine' Finset.sum_bij ( fun x _ => ( fun i => x ( if i = 0 then 0 else 1 ), fun i => x ( if i = 0 then 2 else 3 ) ) ) _ _ _ _ <;> simp +decide;
  · simp +decide [ funext_iff, Fin.forall_fin_succ ];
    tauto;
  · exact fun a b => ⟨ fun i => if i = 0 then a 0 else if i = 1 then a 1 else if i = 2 then b 0 else b 1, by ext i; fin_cases i <;> rfl, by ext i; fin_cases i <;> rfl ⟩;
  · simp +decide [ Fin.prod_univ_four, centeredOverlapSq ];
    simp +decide [ centeredOverlap, overlap ] ; intros ; ring;
    simpa only [ mul_assoc, ← Real.exp_add ] using by ring;

lemma measurable_H_t_workspace (t : ℝ) :
    Measurable
      (H_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) t) := by
  have hU : Measurable sk.U := sk.hU.repr_measurable
  have hV : Measurable sim.V := sim.hV.repr_measurable
  simpa [H_t, H_gauss] using
    ((hU.const_smul (Real.sqrt t)).add
      (hV.const_smul (Real.sqrt (1 - t)))).add measurable_const

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma measurable_coupledCrossMomentDet_workspace (coupling : ℝ) :
    Measurable
      (fun H : EnergySpace N =>
        coupledCrossMomentDet (N := N) (q := q) H coupling) := by
  refine' Measurable.mul _ _;
  · apply_rules [ Finset.measurable_sum, Finset.measurable_prod ];
    refine' fun σ _ => Measurable.mul _ _;
    · fun_prop;
    · exact Finset.measurable_prod _ fun _ _ => ( contDiff_gibbs_pmf N ( σ _ ) |> ContDiff.continuous |> Continuous.measurable );
  · refine' Measurable.inv ( Measurable.pow_const _ _ );
    refine' Finset.measurable_sum _ fun σs _ => _;
    refine' Measurable.mul _ _;
    · exact measurable_const;
    · exact Finset.measurable_prod _ fun _ _ => ( contDiff_gibbs_pmf ( N := N ) ( σ := σs _ ) |> ContDiff.continuous |> Continuous.measurable )

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
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => ( ∑ σs : ReplicaSpace N 2, ( N : ℝ ) * centeredOverlapSq N q σs );
  · norm_num;
  · have h_measurable : Measurable (fun H : EnergySpace N => tiltedCenteredOverlapSqDet (N := N) (q := q) H coupling) := by
      refine' Measurable.div _ _;
      · refine' Finset.measurable_sum _ fun σs _ => _;
        refine' Measurable.mul _ _;
        · fun_prop;
        · refine' Finset.measurable_prod _ fun i _ => _;
          refine' Measurable.div _ _;
          · fun_prop;
          · refine' Finset.measurable_sum _ fun σ _ => _;
            fun_prop;
      · refine' Finset.measurable_sum _ fun σs _ => _;
        refine' Measurable.mul _ _;
        · exact measurable_const;
        · refine' Finset.measurable_prod _ fun i _ => _;
          refine' Measurable.div _ _;
          · fun_prop;
          · exact Finset.measurable_sum _ fun _ _ => Real.continuous_exp.measurable.comp ( measurable_neg.comp ( by measurability ) );
    have h_measurable : Measurable (fun ω => H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) := by
      apply_rules [ Measurable.add, Measurable.smul, measurable_const ];
      · exact sk.hU.repr_measurable;
      · convert sim.hV.repr_measurable using 1;
    exact Measurable.aestronglyMeasurable ( by measurability );
  · refine' Filter.Eventually.of_forall fun ω => _;
    rw [ tiltedCenteredOverlapSqDet ];
    rw [ gibbs_average_n_det, tiltedReplicaPartitionDet ];
    rw [ gibbs_average_n_det ];
    rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => mul_nonneg ( mul_nonneg ( by exact sq_nonneg _ ) ( Real.exp_nonneg _ ) ) ( Finset.prod_nonneg fun _ _ => by exact div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) ) ) ( Finset.sum_nonneg fun _ _ => mul_nonneg ( Real.exp_nonneg _ ) ( Finset.prod_nonneg fun _ _ => by exact div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) ) ) ) ];
    rw [ div_le_iff₀ ];
    · rw [ Finset.sum_mul _ _ _ ];
      refine' Finset.sum_le_sum fun i _ => _;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun a _ => mul_nonneg ( Real.exp_nonneg _ ) ( Finset.prod_nonneg fun b _ => _ ) ) ( Finset.mem_univ i ) ) _ );
      · rw [ mul_assoc ];
        gcongr;
        · exact mul_nonneg ( Real.exp_nonneg _ ) ( Finset.prod_nonneg fun _ _ => div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) );
        · exact le_mul_of_one_le_left ( sq_nonneg _ ) ( mod_cast NeZero.pos N );
      · exact div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ );
      · exact mul_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ );
    · refine' Finset.sum_pos _ _ <;> simp +decide [ gibbs_pmf ];
      exact fun _ => mul_pos ( Real.exp_pos _ ) ( div_pos ( mul_pos ( Real.exp_pos _ ) ( Real.exp_pos _ ) ) ( sq_pos_of_pos ( Z_pos _ _ ) ) )

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
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => ∑ σs : ReplicaSpace N 4, |crossPairCenteredOverlapSq N q σs|;
  · norm_num;
  · exact Measurable.aestronglyMeasurable ( by exact Measurable.comp ( measurable_coupledCrossMomentDet_workspace N q coupling ) ( measurable_H_t_workspace N β h q sk sim t ) );
  · refine' Filter.Eventually.of_forall fun ω => _;
    unfold coupledCrossMomentDet gibbs_average_n_det;
    rw [ norm_div ];
    refine' div_le_of_le_mul₀ _ _ _;
    · positivity;
    · exact Finset.sum_nonneg fun _ _ => abs_nonneg _;
    · refine' le_trans ( norm_sum_le _ _ ) _;
      rw [ Finset.sum_mul _ _ _ ];
      refine' Finset.sum_le_sum fun σs _ => _;
      rw [ ← fourReplicaTiltWeight_sum_workspace ];
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( le_abs_self _ ) ( abs_nonneg _ ) );
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Finset.single_le_sum ( fun σs _ => _ ) ( Finset.mem_univ σs ) ) ( abs_nonneg _ ) );
      · simp +decide [ abs_mul, abs_of_nonneg, Real.exp_nonneg, gibbs_pmf_nonneg ];
        rw [ mul_assoc ];
      · exact mul_nonneg ( Real.exp_nonneg _ ) ( Finset.prod_nonneg fun _ _ => div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) )

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
