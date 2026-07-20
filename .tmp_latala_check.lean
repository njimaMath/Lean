import SpinGlass.Replicas

open MeasureTheory ProbabilityTheory Real BigOperators SpinGlass
open PhysLean.Probability.GaussianIBP
open scoped ENNReal NNReal

universe uΩ uD
variable {Ω : Type uΩ} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) (β h q : ℝ)
variable (sk : SKDisorder.{uΩ, uD} (Ω := Ω) N β h)
  (sim : SimpleDisorder.{uΩ, uD} (Ω := Ω) N β q)

noncomputable def smartLinear (t : ℝ) :
    WithLp 2 (EnergySpace N × EnergySpace N) →L[ℝ] EnergySpace N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => Real.sqrt t • p.fst + Real.sqrt (1 - t) • p.snd
      map_add' := by intro x y; simp [add_add_add_comm]
      map_smul' := by intro c x; simp [smul_add, smul_smul, mul_comm] }

example (t : ℝ) (ω : Ω) :
    smartLinear (N := N) t (UV (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) ω) + H_field (N := N) (h := h) =
    H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω := by
  rfl

example (t : ℝ) : ContDiff ℝ (⊤ : WithTop ℕ∞)
    (fun p : WithLp 2 (EnergySpace N × EnergySpace N) =>
      smartLinear (N := N) t p + H_field (N := N) (h := h)) := by
  fun_prop

lemma fderiv_gibbs_norm_le_two (H : EnergySpace N) (σ : Config N) :
    ‖fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) H‖ ≤ 2 := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro x
  have havg : |∑ τ : Config N, gibbs_pmf N H τ * x τ| ≤ ‖x‖ := by
    calc
      |∑ τ : Config N, gibbs_pmf N H τ * x τ|
          ≤ ∑ τ : Config N, |gibbs_pmf N H τ * x τ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ τ : Config N, gibbs_pmf N H τ * |x τ| := by
        apply Finset.sum_congr rfl
        intro τ _
        rw [abs_mul, abs_of_nonneg (gibbs_pmf_nonneg N H τ)]
      _ ≤ ∑ τ : Config N, gibbs_pmf N H τ * ‖x‖ := by
        apply Finset.sum_le_sum
        intro τ _
        exact mul_le_mul_of_nonneg_left (abs_apply_le_norm N x τ)
          (gibbs_pmf_nonneg N H τ)
      _ = ‖x‖ := by rw [← Finset.sum_mul, sum_gibbs_pmf]; simp
  rw [Real.norm_eq_abs, fderiv_gibbs_pmf_apply]
  have hgabs : |gibbs_pmf N H σ| ≤ 1 := by
    rw [abs_of_nonneg (gibbs_pmf_nonneg N H σ)]
    exact gibbs_pmf_le_one N H σ
  calc
    |gibbs_pmf N H σ * (∑ τ, gibbs_pmf N H τ * x τ - x σ)|
        ≤ |∑ τ, gibbs_pmf N H τ * x τ - x σ| := by
      simpa [abs_mul] using mul_le_mul_of_nonneg_right hgabs (abs_nonneg _)
    _ ≤ |∑ τ, gibbs_pmf N H τ * x τ| + |x σ| := abs_sub _ _
    _ ≤ ‖x‖ + ‖x‖ := add_le_add havg (abs_apply_le_norm N x σ)
    _ = 2 * ‖x‖ := by ring

noncomputable def moderateGrowth_gibbs_smart (t : ℝ) (σ : Config N) :
    HasModerateGrowth (fun p : WithLp 2 (EnergySpace N × EnergySpace N) =>
      gibbs_pmf N (smartLinear (N := N) t p + H_field (N := N) (h := h)) σ) := by
  let L := smartLinear (N := N) t
  let A : WithLp 2 (EnergySpace N × EnergySpace N) → EnergySpace N :=
    fun p => L p + H_field (N := N) (h := h)
  let C : ℝ := 2 * ‖L‖ + 1
  refine ⟨C, 0, by simp [C]; positivity, ?_, ?_⟩
  · intro p
    have hnonneg := gibbs_pmf_nonneg N (A p) σ
    have hle := gibbs_pmf_le_one N (A p) σ
    have hC : (1 : ℝ) ≤ C := by dsimp [C]; linarith [norm_nonneg L]
    simpa [A, C, L, abs_of_nonneg hnonneg] using hle.trans hC
  · intro p
    have hA : HasFDerivAt A L p := by
      simpa [A] using L.hasFDerivAt.add_const (H_field (N := N) (h := h))
    have hg : HasFDerivAt (fun K : EnergySpace N => gibbs_pmf N K σ)
        (fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) (A p)) (A p) :=
      ((contDiff_gibbs_pmf N σ).differentiable (by simp)).differentiableAt.hasFDerivAt
    have hderiv :
        fderiv ℝ (fun z : WithLp 2 (EnergySpace N × EnergySpace N) =>
          gibbs_pmf N (smartLinear (N := N) t z + H_field (N := N) (h := h)) σ) p =
        (fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) (A p)).comp L := by
      simpa [A, L] using (hg.comp p hA).fderiv
    rw [hderiv]
    calc
      ‖(fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) (A p)).comp L‖
          ≤ ‖fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) (A p)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * ‖L‖ := mul_le_mul_of_nonneg_right
        (fderiv_gibbs_norm_le_two N (A p) σ) (norm_nonneg L)
      _ ≤ C * (1 + ‖p‖) ^ 0 := by simp [C]

example (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) (σ : Config N) (ω : Ω) :
    inner ℝ
      (UV (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ω)
      (WithLp.toLp 2 (std_basis N σ, (0 : EnergySpace N))) = sk.U ω σ := by
  simp [UV, std_basis, PiLp.inner_apply]

lemma covOp_joint_inl (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) (σ : Config N) :
    ((covOp (isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hIndep)
      (WithLp.toLp 2 (std_basis N σ, (0 : EnergySpace N)))).fst) =
    covOp sk.hU (std_basis N σ) := by
  rw [covOp_apply, covOp_apply]
  simp [isGaussianHilbert_UV, OrthonormalBasis.prod_apply]
  let a : sk.hU.ι → ℝ := fun x => (sk.hU.τ x : ℝ) * inner ℝ (std_basis N σ) (sk.hU.w x)
  have hx : (∑ x, a x • WithLp.toLp 2 (sk.hU.w x, (0 : EnergySpace N))) =
      WithLp.toLp 2 (∑ x, a x • sk.hU.w x, (0 : EnergySpace N)) := by
    apply (WithLp.linearEquiv 2 ℝ _).injective
    simp only [map_sum, map_smul]
    apply Prod.ext
    · rw [Prod.fst_sum]
      simp [a]
    · rw [Prod.snd_sum]
      simp [a]
  rw [show (∑ x, ((sk.hU.τ x : ℝ) * inner ℝ (std_basis N σ) (sk.hU.w x)) •
      WithLp.toLp 2 (sk.hU.w x, (0 : EnergySpace N))) =
      WithLp.toLp 2 (∑ x, ((sk.hU.τ x : ℝ) * inner ℝ (std_basis N σ) (sk.hU.w x)) •
        sk.hU.w x, (0 : EnergySpace N)) by simpa [a] using hx]
  rfl

lemma covOp_joint_inl_full (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) (σ : Config N) :
    covOp (isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hIndep)
      (WithLp.toLp 2 (std_basis N σ, (0 : EnergySpace N))) =
    WithLp.toLp 2 (covOp sk.hU (std_basis N σ), (0 : EnergySpace N)) := by
  rw [covOp_apply, covOp_apply]
  simp [isGaussianHilbert_UV, OrthonormalBasis.prod_apply]
  let a : sk.hU.ι → ℝ := fun x => (sk.hU.τ x : ℝ) * inner ℝ (std_basis N σ) (sk.hU.w x)
  have hx : (∑ x, a x • WithLp.toLp 2 (sk.hU.w x, (0 : EnergySpace N))) =
      WithLp.toLp 2 (∑ x, a x • sk.hU.w x, (0 : EnergySpace N)) := by
    apply (WithLp.linearEquiv 2 ℝ _).injective
    simp only [map_sum, map_smul]
    apply Prod.ext
    · rw [Prod.fst_sum]
      simp [a]
    · rw [Prod.snd_sum]
      simp [a]
  simpa [a] using hx

lemma covOp_joint_inr (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) (σ : Config N) :
    covOp (isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hIndep)
      (WithLp.toLp 2 ((0 : EnergySpace N), std_basis N σ)) =
    WithLp.toLp 2 ((0 : EnergySpace N), covOp sim.hV (std_basis N σ)) := by
  rw [covOp_apply, covOp_apply]
  simp [isGaussianHilbert_UV, OrthonormalBasis.prod_apply]
  let a : sim.hV.ι → ℝ := fun x => (sim.hV.τ x : ℝ) * inner ℝ (std_basis N σ) (sim.hV.w x)
  have hx : (∑ x, a x • WithLp.toLp 2 ((0 : EnergySpace N), sim.hV.w x)) =
      WithLp.toLp 2 ((0 : EnergySpace N), ∑ x, a x • sim.hV.w x) := by
    apply (WithLp.linearEquiv 2 ℝ _).injective
    simp only [map_sum, map_smul]
    apply Prod.ext
    · rw [Prod.fst_sum]
      simp [a]
    · rw [Prod.snd_sum]
      simp [a]
  simpa [a] using hx

lemma ibp_U (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (σ : Config N) :
    (∫ ω, sk.U ω σ * gibbs_pmf N
      (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ ∂ℙ) =
    Real.sqrt t * ∫ ω,
      fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ)
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        (covOp sk.hU (std_basis N σ)) ∂ℙ := by
  let G := UV (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  let hg : IsGaussianHilbert G := isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) hIndep
  let L := smartLinear (N := N) t
  let A : WithLp 2 (EnergySpace N × EnergySpace N) → EnergySpace N :=
    fun p => L p + H_field (N := N) (h := h)
  let F : WithLp 2 (EnergySpace N × EnergySpace N) → ℝ :=
    fun p => gibbs_pmf N (A p) σ
  have hFdiff : ContDiff ℝ 1 F := by
    exact ((contDiff_gibbs_pmf N σ).of_le (by simp)).comp (by fun_prop)
  have hFgrowth : HasModerateGrowth F := by
    simpa [F, A, L] using moderateGrowth_gibbs_smart (N := N) (h := h) t σ
  have hibp :=
    PhysLean.Probability.GaussianIBP.ProbabilityTheory.gaussian_integration_by_parts_hilbert_cov_op
      (g := G) hg (WithLp.toLp 2 (std_basis N σ, (0 : EnergySpace N)))
      hFdiff hFgrowth
  have hchain (p z : WithLp 2 (EnergySpace N × EnergySpace N)) :
      fderiv ℝ F p z =
        fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) (A p) (L z) := by
    have hA : HasFDerivAt A L p := by
      simpa [A] using L.hasFDerivAt.add_const (H_field (N := N) (h := h))
    have hgp : HasFDerivAt (fun K : EnergySpace N => gibbs_pmf N K σ)
        (fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) (A p)) (A p) :=
      ((contDiff_gibbs_pmf N σ).differentiable (by simp)).differentiableAt.hasFDerivAt
    simpa [F] using congrArg (fun T : WithLp 2 (EnergySpace N × EnergySpace N) →L[ℝ] ℝ => T z)
      (hgp.comp p hA).fderiv
  rw [show (covOp hg (WithLp.toLp 2 (std_basis N σ, (0 : EnergySpace N)))) =
      WithLp.toLp 2 (covOp sk.hU (std_basis N σ), (0 : EnergySpace N)) by
    simpa [hg] using covOp_joint_inl_full (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hIndep σ] at hibp
  calc
    (∫ ω, sk.U ω σ * gibbs_pmf N
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ ∂ℙ) =
        ∫ ω, inner ℝ (G ω) (WithLp.toLp 2 (std_basis N σ, (0 : EnergySpace N))) *
          F (G ω) ∂ℙ := by
      apply integral_congr_ae
      filter_upwards with ω
      simp [G, F, A, L, UV, H_t, H_gauss, smartLinear, std_basis, PiLp.inner_apply]
    _ = ∫ ω, fderiv ℝ F (G ω)
        (WithLp.toLp 2 (covOp sk.hU (std_basis N σ), (0 : EnergySpace N))) ∂ℙ := hibp
    _ = Real.sqrt t * ∫ ω,
        fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
          (covOp sk.hU (std_basis N σ)) ∂ℙ := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      rw [hchain]
      simp [G, A, L, UV, H_t, H_gauss, smartLinear]

lemma ibp_V (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (σ : Config N) :
    (∫ ω, sim.V ω σ * gibbs_pmf N
      (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ ∂ℙ) =
    Real.sqrt (1 - t) * ∫ ω,
      fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ)
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
        (covOp sim.hV (std_basis N σ)) ∂ℙ := by
  let G := UV (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  let hg : IsGaussianHilbert G := isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) hIndep
  let L := smartLinear (N := N) t
  let A : WithLp 2 (EnergySpace N × EnergySpace N) → EnergySpace N :=
    fun p => L p + H_field (N := N) (h := h)
  let F : WithLp 2 (EnergySpace N × EnergySpace N) → ℝ :=
    fun p => gibbs_pmf N (A p) σ
  have hFdiff : ContDiff ℝ 1 F := by
    exact ((contDiff_gibbs_pmf N σ).of_le (by simp)).comp (by fun_prop)
  have hFgrowth : HasModerateGrowth F := by
    simpa [F, A, L] using moderateGrowth_gibbs_smart (N := N) (h := h) t σ
  have hibp :=
    PhysLean.Probability.GaussianIBP.ProbabilityTheory.gaussian_integration_by_parts_hilbert_cov_op
      (g := G) hg (WithLp.toLp 2 ((0 : EnergySpace N), std_basis N σ))
      hFdiff hFgrowth
  have hchain (p z : WithLp 2 (EnergySpace N × EnergySpace N)) :
      fderiv ℝ F p z =
        fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) (A p) (L z) := by
    have hA : HasFDerivAt A L p := by
      simpa [A] using L.hasFDerivAt.add_const (H_field (N := N) (h := h))
    have hgp : HasFDerivAt (fun K : EnergySpace N => gibbs_pmf N K σ)
        (fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) (A p)) (A p) :=
      ((contDiff_gibbs_pmf N σ).differentiable (by simp)).differentiableAt.hasFDerivAt
    simpa [F] using congrArg (fun T : WithLp 2 (EnergySpace N × EnergySpace N) →L[ℝ] ℝ => T z)
      (hgp.comp p hA).fderiv
  rw [show (covOp hg (WithLp.toLp 2 ((0 : EnergySpace N), std_basis N σ))) =
      WithLp.toLp 2 ((0 : EnergySpace N), covOp sim.hV (std_basis N σ)) by
    simpa [hg] using covOp_joint_inr (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hIndep σ] at hibp
  calc
    (∫ ω, sim.V ω σ * gibbs_pmf N
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) σ ∂ℙ) =
        ∫ ω, inner ℝ (G ω) (WithLp.toLp 2 ((0 : EnergySpace N), std_basis N σ)) *
          F (G ω) ∂ℙ := by
      apply integral_congr_ae
      filter_upwards with ω
      simp [G, F, A, L, UV, H_t, H_gauss, smartLinear, std_basis, PiLp.inner_apply]
    _ = ∫ ω, fderiv ℝ F (G ω)
        (WithLp.toLp 2 ((0 : EnergySpace N), covOp sim.hV (std_basis N σ))) ∂ℙ := hibp
    _ = Real.sqrt (1 - t) * ∫ ω,
        fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
          (covOp sim.hV (std_basis N σ)) ∂ℙ := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      rw [hchain]
      simp [G, A, L, UV, H_t, H_gauss, smartLinear]

lemma neg_inv_mul_fderiv_gibbs (H : EnergySpace N) (σ : Config N) (k : EnergySpace N) :
    -(1 / (N : ℝ)) * fderiv ℝ (fun K : EnergySpace N => gibbs_pmf N K σ) H k =
      hessian_free_energy N H (std_basis N σ) k := by
  classical
  rw [fderiv_gibbs_pmf_apply]
  simp [hessian_free_energy, std_basis]
  ring

lemma covOp_sk_std_basis (σ : Config N) :
    covOp sk.hU (std_basis N σ) =
      ∑ τ : Config N, sk_cov_kernel N β σ τ • std_basis N τ := by
  classical
  ext ρ
  rw [← inner_std_basis_apply]
  rw [real_inner_comm]
  rw [sk.cov_eq]
  simp [std_basis]

lemma covOp_simple_std_basis (σ : Config N) :
    covOp sim.hV (std_basis N σ) =
      ∑ τ : Config N, simple_cov_kernel N β (fun x => q * x) σ τ • std_basis N τ := by
  classical
  ext ρ
  rw [← inner_std_basis_apply]
  rw [real_inner_comm]
  rw [sim.cov_eq]
  simp [std_basis]

lemma hessian_covOp_sk (H : EnergySpace N) (σ : Config N) :
    hessian_free_energy N H (std_basis N σ) (covOp sk.hU (std_basis N σ)) =
      ∑ τ : Config N, sk_cov_kernel N β σ τ *
        hessian_free_energy N H (std_basis N σ) (std_basis N τ) := by
  rw [covOp_sk_std_basis (N := N) (β := β) (sk := sk)]
  simp only [← hessian_free_energy_fderiv_eq_hessian_free_energy,
    map_sum, map_smul, smul_eq_mul]

lemma hessian_covOp_simple (H : EnergySpace N) (σ : Config N) :
    hessian_free_energy N H (std_basis N σ) (covOp sim.hV (std_basis N σ)) =
      ∑ τ : Config N, simple_cov_kernel N β (fun x => q * x) σ τ *
        hessian_free_energy N H (std_basis N σ) (std_basis N τ) := by
  rw [covOp_simple_std_basis (N := N) (β := β) (q := q) (sim := sim)]
  simp only [← hessian_free_energy_fderiv_eq_hessian_free_energy,
    map_sum, map_smul, smul_eq_mul]

example (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) (σ : Config N) :
    ((covOp (isGaussianHilbert_UV (N := N) (β := β) (h := h) (q := q)
      (sk := sk) (sim := sim) hIndep)
      (WithLp.toLp 2 ((0 : EnergySpace N), std_basis N σ))).snd) =
    covOp sim.hV (std_basis N σ) := by
  rw [covOp_apply, covOp_apply]
  simp [isGaussianHilbert_UV, OrthonormalBasis.prod_apply]
  let a : sim.hV.ι → ℝ := fun x => (sim.hV.τ x : ℝ) * inner ℝ (std_basis N σ) (sim.hV.w x)
  have hx : (∑ x, a x • WithLp.toLp 2 ((0 : EnergySpace N), sim.hV.w x)) =
      WithLp.toLp 2 ((0 : EnergySpace N), ∑ x, a x • sim.hV.w x) := by
    apply (WithLp.linearEquiv 2 ℝ _).injective
    simp only [map_sum, map_smul]
    apply Prod.ext
    · rw [Prod.fst_sum]
      simp [a]
    · rw [Prod.snd_sum]
      simp [a]
  rw [show (∑ x, ((sim.hV.τ x : ℝ) * inner ℝ (std_basis N σ) (sim.hV.w x)) •
      WithLp.toLp 2 ((0 : EnergySpace N), sim.hV.w x)) =
      WithLp.toLp 2 ((0 : EnergySpace N), ∑ x, ((sim.hV.τ x : ℝ) *
        inner ℝ (std_basis N σ) (sim.hV.w x)) • sim.hV.w x) by simpa [a] using hx]
  rfl
