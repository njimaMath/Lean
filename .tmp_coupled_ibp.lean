import latala

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass.GeneralizedLatala

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) [NeZero N] (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) N β h)
variable (sim : SimpleDisorder (Ω := Ω) N β q)

example
    {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (volume : Measure Ω')]
    (g : Ω' → EnergySpace N)
    (hg : PhysLean.Probability.GaussianIBP.IsGaussianHilbert g)
    (H : EnergySpace N) (coupling : ℝ) :
    (∑ i : hg.ι, (hg.τ i : ℝ) *
      coupledHessianDet N q H coupling (hg.w i) (hg.w i)) =
      ∑ σ : Config N, ∑ τ : Config N,
        inner ℝ ((PhysLean.Probability.GaussianIBP.covOp (g := g) hg)
          (std_basis N σ)) (std_basis N τ) *
        coupledHessianDet N q H coupling (std_basis N σ) (std_basis N τ) := by
  classical
  simp only [PhysLean.Probability.GaussianIBP.covOp_apply]
  simp_rw [inner_std_basis_apply]
  have hinner_eq_symm (v : EnergySpace N) (σ : Config N) :
      inner ℝ (std_basis N σ) v = v σ := inner_std_basis_apply N σ v
  have hstd (σ τ : Config N) :
      (std_basis N σ) τ = if σ = τ then 1 else 0 := by simp [std_basis]
  simp only [coupledHessianDet, tiltedReplicaAverageDet, pairEval]
  simp only [sum_inner, inner_smul_left]
  simp [gibbs_average_n_det, hinner_eq_symm, hstd,
    real_inner_comm, hg.w.repr_apply_apply, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_sub_distrib]
  ring_nf
  simp

end SpinGlass.GeneralizedLatala
