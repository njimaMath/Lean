import latala

open Real BigOperators

private lemma norm_fderiv_log_sum_exp_le
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Nonempty ι] (φ : ι → E → ℝ) (x : E)
    (hφ : ∀ i, DifferentiableAt ℝ (φ i) x) :
    ‖fderiv ℝ (fun y => Real.log (∑ i, Real.exp (φ i y))) x‖ ≤
      ∑ i, ‖fderiv ℝ (φ i) x‖ := by
  classical
  let S : ℝ := ∑ i, Real.exp (φ i x)
  have hS : 0 < S := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hsum : HasFDerivAt (fun y => ∑ i, Real.exp (φ i y))
      (∑ i, Real.exp (φ i x) • fderiv ℝ (φ i) x) x := by
    exact HasFDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hφ i).hasFDerivAt.exp)
  have hlog := hsum.log hS.ne'
  rw [hlog.fderiv]
  calc
    ‖S⁻¹ • ∑ i, Real.exp (φ i x) • fderiv ℝ (φ i) x‖ =
        S⁻¹ * ‖∑ i, Real.exp (φ i x) • fderiv ℝ (φ i) x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hS)]
    _ ≤ S⁻¹ * ∑ i, ‖Real.exp (φ i x) • fderiv ℝ (φ i) x‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = ∑ i, (Real.exp (φ i x) / S) * ‖fderiv ℝ (φ i) x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, ‖fderiv ℝ (φ i) x‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hi : Real.exp (φ i x) ≤ S :=
        Finset.single_le_sum (fun j _ => (Real.exp_pos (φ j x)).le) (Finset.mem_univ i)
      have hw : Real.exp (φ i x) / S ≤ 1 := (div_le_one hS).2 hi
      exact mul_le_of_le_one_left (norm_nonneg _) hw

open MeasureTheory ProbabilityTheory
namespace SpinGlass.GeneralizedLatala
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) [NeZero N] (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) N β h)
variable (sim : SimpleDisorder (Ω := Ω) N β q)

private lemma test_raw (H : EnergySpace N) (c : ℝ) :
    Real.log (tiltedReplicaPartitionDet (N := N) (q := q) H c) =
      Real.log (∑ σs : ReplicaSpace N 2, Real.exp
        (c * (N : ℝ) * centeredOverlapSq N q σs - H (σs 0) - H (σs 1))) -
      2 * Real.log (Z N H) := by
  classical
  have hZ : 0 < Z N H := Z_pos (N := N) (H := H)
  have hS : 0 < ∑ σs : ReplicaSpace N 2, Real.exp
      (c * (N : ℝ) * centeredOverlapSq N q σs - H (σs 0) - H (σs 1)) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have heq : tiltedReplicaPartitionDet (N := N) (q := q) H c =
      (∑ σs : ReplicaSpace N 2, Real.exp
        (c * (N : ℝ) * centeredOverlapSq N q σs - H (σs 0) - H (σs 1))) /
        (Z N H) ^ 2 := by
    unfold tiltedReplicaPartitionDet gibbs_average_n_det gibbs_pmf
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σs _
    simp only [Fin.prod_univ_two]
    field_simp [hZ.ne'] <;>
      simp only [← Real.exp_add] <;>
      congr 1 <;> ring
  rw [heq, Real.log_div hS.ne' (pow_ne_zero 2 hZ.ne'), Real.log_pow]
  ring

end SpinGlass.GeneralizedLatala

open MeasureTheory ProbabilityTheory Real BigOperators
namespace SpinGlass.GeneralizedLatala
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) [NeZero N] (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) N β h)
variable (sim : SimpleDisorder (Ω := Ω) N β q)

private lemma test_phase_bound (x c A : ℝ) (ω : Ω) (σ τ : Config N)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ‖fderiv ℝ (fun p : ℝ × ℝ => p.2 * A -
      H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 ω σ -
      H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 ω τ) (x,c)‖ ≤
      |A| + 2 * ‖dH_t (N := N) (β := β) (h := h) (q := q)
        (sk := sk) (sim := sim) x ω‖ := by
  let dH := dH_t (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) x ω
  have hHt := (hasDerivAt_H_t (N := N) (β := β) (h := h) (q := q)
    (sk := sk) (sim := sim) x hx ω).hasFDerivAt.comp (x,c)
      (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ))
  have hσ := (evalCLM (N := N) σ).hasFDerivAt.comp (x,c) hHt
  have hτ := (evalCLM (N := N) τ).hasFDerivAt.comp (x,c) hHt
  have hA := (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)
    (p := (x,c))).const_mul A
  have hphase := (hA.sub hσ).sub hτ
  have hphase' : HasFDerivAt (fun p : ℝ × ℝ => p.2 * A -
      H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 ω σ -
      H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) p.1 ω τ)
      (A • ContinuousLinearMap.snd ℝ ℝ ℝ -
        (evalCLM (N := N) σ).comp
          ((ContinuousLinearMap.toSpanSingleton ℝ dH).comp
            (ContinuousLinearMap.fst ℝ ℝ ℝ)) -
        (evalCLM (N := N) τ).comp
          ((ContinuousLinearMap.toSpanSingleton ℝ dH).comp
            (ContinuousLinearMap.fst ℝ ℝ ℝ))) (x,c) := by
    convert hphase using 1
    ext p
    simp [Function.comp_def, mul_comm]
  rw [hphase'.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro v
  change ‖A * v.2 - (v.1 • dH) σ - (v.1 • dH) τ‖ ≤
    (|A| + 2 * ‖dH‖) * ‖v‖
  calc
    ‖A * v.2 - (v.1 • dH) σ - (v.1 • dH) τ‖ ≤
        |A| * ‖v.2‖ + 2 * ‖dH‖ * ‖v.1‖ := by
      rw [Real.norm_eq_abs]
      calc
        |A * v.2 - (v.1 • dH) σ - (v.1 • dH) τ| ≤
            |A * v.2| + |(v.1 • dH) σ| + |(v.1 • dH) τ| := by
          linarith [abs_sub (A * v.2 - (v.1 • dH) σ) ((v.1 • dH) τ),
            abs_sub (A * v.2) ((v.1 • dH) σ)]
        _ ≤ |A| * ‖v.2‖ + 2 * ‖dH‖ * ‖v.1‖ := by
          have hσeval : |dH σ| ≤ ‖dH‖ := abs_apply_le_norm (N := N) dH σ
          have hτeval : |dH τ| ≤ ‖dH‖ := abs_apply_le_norm (N := N) dH τ
          change |A * v.2| + |v.1 * dH σ| + |v.1 * dH τ| ≤ _
          simp only [abs_mul, Real.norm_eq_abs]
          nlinarith [abs_nonneg v.1, abs_nonneg v.2, norm_nonneg dH]
    _ ≤ (|A| + 2 * ‖dH‖) * ‖v‖ := by
      nlinarith [norm_fst_le v, norm_snd_le v, abs_nonneg A, norm_nonneg dH]

end SpinGlass.GeneralizedLatala
