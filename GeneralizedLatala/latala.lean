import SpinGlass.Replicas
import SpinGlass.GuerraBound
import SpinGlass.KS_inequality
import EndpointScratch
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ENNReal NNReal

namespace SpinGlass
namespace GeneralizedLatala

/-!
# Generalized Latała argument for the SK model

This file follows `blueprint_latala.txt`.  It uses the finite-volume SK and simple Gaussian
disorders from `SpinGlass.SKModel` and the smart path, replica Gibbs averages, and annealed
expectation `nu` from `SpinGlass.Replicas`.

The scalar order parameter `q` is kept as an input satisfying the replica-symmetric fixed-point
equation.  This is preferable to making an arbitrary global choice of a fixed point.  The
remaining analytic work is split into small lemmas below, with comments recording the intended
Gaussian-IBP and characteristic arguments.  The final overlap and free-energy bounds are then
assembled from those ingredients.
-/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-!
**# Hubbard--Stratonovich identity**

This file records the scalar Gaussian identity used to linearize a positive
quadratic exponential.  It depends only on mathlib.
-/

/-- The moment-generating function identity for a standard real Gaussian,
written directly as an integral. -/
lemma integral_exp_mul_standardGaussian (t : ℝ) :
    ∫ z, Real.exp (t * z) ∂gaussianReal 0 1 = Real.exp (t ^ 2 / 2) := by
  simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t

/-- The scalar Hubbard--Stratonovich identity.  If `a` is nonnegative and
`Z` is a standard real Gaussian, then
`exp (a * x ^ 2 / 2) = E[exp (sqrt a * x * Z)]`. -/
lemma hubbard_stratonovich (a x : ℝ) (ha : 0 ≤ a) :
    Real.exp (a * x ^ 2 / 2) =
      ∫ z, Real.exp (Real.sqrt a * x * z) ∂gaussianReal 0 1 := by
  rw [integral_exp_mul_standardGaussian, mul_pow, Real.sq_sqrt ha]

/-! ## Scalar replica-symmetric data -/

/-- Expectation against a standard real Gaussian. -/
noncomputable def standardGaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂ProbabilityTheory.gaussianReal 0 1

/-- The replica-symmetric fixed-point equation
`q = E[tanh (h + β sqrt(q) Z)^2]`. -/
def IsRSFixedPoint (β h q : ℝ) : Prop :=
  q = standardGaussianExpectation
    (fun z => Real.tanh (h + β * Real.sqrt q * z) ^ 2)

/-- The sharp Bernoulli sub-Gaussian coefficient used at the independent endpoint. -/
noncomputable def kappa (q : ℝ) : ℝ :=
  if q = 0 then 1 else q / Real.artanh q

/-- The improved high-temperature parameter `ρ = β² κ(q)`. -/
noncomputable def rho (β q : ℝ) : ℝ :=
  β ^ 2 * kappa q

/-- Coupling strength used in the quadratic replica estimate. -/
noncomputable def lambdaStar (β q : ℝ) : ℝ :=
  ((kappa q)⁻¹ - β ^ 2) / 4

/-- The constant on the right side of the uniform logarithmic quadratic estimate. -/
noncomputable def quadraticConstant (β q : ℝ) : ℝ :=
  (1 / 2) * Real.exp (2 * rho β q / (1 - rho β q)) *
    Real.log (2 / (1 - rho β q))

/-- The replica-symmetric free-energy prediction. -/
noncomputable def rsPressure (β h q : ℝ) : ℝ :=
  Real.log 2 +
    standardGaussianExpectation
      (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) +
    (β ^ 2 / 4) * (1 - q) ^ 2

lemma kappa_zero : kappa 0 = 1 := by
  simp [kappa]

lemma kappa_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < kappa q := by
  by_cases hq : q = 0
  · simp [hq, kappa]
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have ha : 0 < Real.artanh q := Real.artanh_pos ⟨hqpos, hq1⟩
    simp only [kappa, if_neg hq]
    exact div_pos hqpos ha

lemma rho_eq (β q : ℝ) : rho β q = β ^ 2 * kappa q := by
  rfl

lemma lambdaStar_eq (β q : ℝ) :
    lambdaStar β q = ((kappa q)⁻¹ - β ^ 2) / 4 := by
  rfl

/-! ## Smart-path observables -/

variable (N : ℕ) (β h q : ℝ)
variable (sk : SKDisorder (Ω := Ω) N β h)
variable (sim : SimpleDisorder (Ω := Ω) N β q)

/-- Centered overlap `Q_ab = R_ab - q`. -/
noncomputable def centeredOverlap {n : ℕ} (a b : Fin n) : ReplicaFun N n :=
  fun σs => overlap N (σs a) (σs b) - q

/-- The square of the centered overlap of the first two replicas. -/
noncomputable def centeredOverlapSq : ReplicaFun N 2 :=
  fun σs => (overlap N (σs 0) (σs 1) - q) ^ 2

/-- Annealed second moment `ν_t[Q_12²]`. -/
noncomputable def overlapVariance (t : ℝ) : ℝ :=
  nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    2 t (centeredOverlapSq N q)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma overlapVariance_nonneg (t : ℝ) :
    0 ≤ overlapVariance
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t := by
  classical
  apply integral_nonneg
  intro ω
  apply Finset.sum_nonneg
  intro σs _
  apply mul_nonneg (sq_nonneg _)
  apply Finset.prod_nonneg
  intro l _
  exact gibbs_pmf_nonneg
    (N := N)
    (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
    (σ := σs l)

/-- The interpolated pressure `N⁻¹ E log Z_{N,t}`. -/
noncomputable def interpolatedPressure (t : ℝ) : ℝ :=
  ∫ ω, free_energy_density (N := N)
    (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) ∂ℙ

/-- The logarithmic quadratic moment
`E log ⟨exp(λ N Q_12²)⟩_t`. -/
noncomputable def logQuadraticMoment (t coupling : ℝ) : ℝ :=
  ∫ ω, Real.log
    (gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      2 t (fun σs => Real.exp (coupling * (N : ℝ) * (centeredOverlapSq N q σs))) ω) ∂ℙ

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Finite-volume Jensen inequality for an arbitrary replica observable. -/
lemma gibbs_average_n_det_exp_jensen {n : ℕ}
    (H : EnergySpace N) (f : ReplicaFun N n) :
    Real.exp (gibbs_average_n_det (N := N) (n := n) H f) ≤
      gibbs_average_n_det (N := N) (n := n) H (fun σs => Real.exp (f σs)) := by
  classical
  let weight : ReplicaSpace N n → ℝ :=
    fun σs => ∏ l, gibbs_pmf N H (σs l)
  have hweight : ∀ σs ∈ (Finset.univ : Finset (ReplicaSpace N n)), 0 ≤ weight σs := by
    intro σs _
    exact Finset.prod_nonneg fun l _ =>
      gibbs_pmf_nonneg (N := N) (H := H) (σ := σs l)
  have hsum : ∑ σs : ReplicaSpace N n, weight σs = 1 := by
    simpa [weight] using sum_prod_gibbs_pmf_eq_one (N := N) (n := n) H
  have hjensen := convexOn_exp.map_sum_le
    (t := (Finset.univ : Finset (ReplicaSpace N n)))
    (w := weight) (p := f) hweight hsum
    (fun σs _ => Set.mem_univ (f σs))
  simpa [gibbs_average_n_det, weight, smul_eq_mul, mul_comm] using hjensen

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Logarithmic form of the finite-volume Jensen inequality. -/
lemma gibbs_average_n_det_le_log_exp {n : ℕ}
    (H : EnergySpace N) (f : ReplicaFun N n) :
    gibbs_average_n_det (N := N) (n := n) H f ≤
      Real.log
        (gibbs_average_n_det (N := N) (n := n) H (fun σs => Real.exp (f σs))) := by
  have hjensen := gibbs_average_n_det_exp_jensen (N := N) H f
  calc
    gibbs_average_n_det (N := N) (n := n) H f =
        Real.log (Real.exp (gibbs_average_n_det (N := N) (n := n) H f)) := by
          rw [Real.log_exp]
    _ ≤ Real.log
        (gibbs_average_n_det (N := N) (n := n) H (fun σs => Real.exp (f σs))) :=
      Real.log_le_log (Real.exp_pos _) hjensen

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Jensen's inequality specialized to the scaled centered-overlap square. -/
lemma scaled_centeredOverlapSq_le_log_gibbs_exp
    (H : EnergySpace N) (coupling : ℝ) :
    coupling * (N : ℝ) *
        gibbs_average_n_det (N := N) (n := 2) H (centeredOverlapSq N q) ≤
      Real.log
        (gibbs_average_n_det (N := N) (n := 2) H
          (fun σs => Real.exp
            (coupling * (N : ℝ) * centeredOverlapSq N q σs))) := by
  have hjensen := gibbs_average_n_det_le_log_exp (N := N) H
    (fun σs : ReplicaSpace N 2 =>
      coupling * (N : ℝ) * centeredOverlapSq N q σs)
  simpa only [gibbs_average_n_det, Finset.mul_sum, mul_assoc] using hjensen

/-- Excess coupled free energy with coupling `(Λ N / 2) Q_12²`.

Adding this quantity to `interpolatedPressure` gives the two-replica coupled free energy from
the blueprint, normalized by `2N`.
-/
noncomputable def coupledExcess (t Λ : ℝ) : ℝ :=
  (1 / (2 * (N : ℝ))) * logQuadraticMoment
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t (Λ / 2)

/-- The normalized coupled two-replica free energy. -/
noncomputable def coupledFreeEnergy (t Λ : ℝ) : ℝ :=
  interpolatedPressure
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t +
    coupledExcess
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t Λ

/-! ## Independent endpoint -/

/-- The one-site moment generating function for the product of two replicas. -/
noncomputable def localPairMGF (a q c : ℝ) : ℝ :=
  ∑ bs : Fin 2 → Bool,
    Real.exp (c * (boolSpin (bs 0) * boolSpin (bs 1) - q)) *
      ∏ l : Fin 2,
        Real.exp (-(a * boolSpin (bs l))) /
          (∑ b : Bool, Real.exp (-(a * boolSpin b)))

private lemma sum_replica_site_factor (N n : ℕ)
    (G : Fin N → (Fin n → Bool) → ℝ) :
    ∑ σs : ReplicaSpace N n, ∏ i, G i (fun l => σs l i) =
      ∏ i, ∑ bs : Fin n → Bool, G i bs := by
  classical
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv (transposeReplicaEquiv N n)
    (fun σs => ∏ i, G i (fun l => σs l i))
    (fun x => ∏ i, G i (x i)) (fun _ => rfl)

private lemma gibbs_average_siteEnergy_pair_mgf
    (N : ℕ) (a : Fin N → ℝ) (q c : ℝ) :
    gibbs_average_n_det (N := N) (n := 2) (siteEnergy N a)
        (fun σs => Real.exp
          (c * ∑ i : Fin N, (spin N (σs 0) i * spin N (σs 1) i - q))) =
      ∏ i : Fin N, localPairMGF (a i) q c := by
  classical
  simp only [gibbs_average_n_det, gibbs_pmf_siteEnergy, spin_eq_boolSpin]
  rw [show (∑ σs : ReplicaSpace N 2,
      Real.exp (c * ∑ i : Fin N,
        (boolSpin (σs 0 i) * boolSpin (σs 1 i) - q)) *
        ∏ l : Fin 2,
          (∏ i : Fin N,
            Real.exp (-(a i * boolSpin (σs l i))) /
              ∑ b : Bool, Real.exp (-(a i * boolSpin b)))) =
      ∑ σs : ReplicaSpace N 2,
        ∏ i : Fin N,
          (Real.exp (c *
              (boolSpin (σs 0 i) * boolSpin (σs 1 i) - q)) *
            ∏ l : Fin 2,
              Real.exp (-(a i * boolSpin (σs l i))) /
                ∑ b : Bool, Real.exp (-(a i * boolSpin b))) by
    congr 1
    funext σs
    rw [Finset.prod_comm]
    rw [Finset.mul_sum, Real.exp_sum]
    simp only [Finset.prod_mul_distrib]]
  exact sum_replica_site_factor N 2
    (fun i bs =>
      Real.exp (c * (boolSpin (bs 0) * boolSpin (bs 1) - q)) *
        ∏ l : Fin 2,
          Real.exp (-(a i * boolSpin (bs l))) /
            ∑ b : Bool, Real.exp (-(a i * boolSpin b)))

private lemma localPairMGF_eq (a q c : ℝ) :
    localPairMGF a q c =
      ((1 + Real.tanh a ^ 2) / 2) * Real.exp (c * (1 - q)) +
      ((1 - Real.tanh a ^ 2) / 2) * Real.exp (-c * (1 + q)) := by
  let F : (Fin 2 → Bool) → ℝ := fun bs =>
    Real.exp (c * (boolSpin (bs 0) * boolSpin (bs 1) - q)) *
      ∏ l : Fin 2,
        Real.exp (-(a * boolSpin (bs l))) /
          (∑ b : Bool, Real.exp (-(a * boolSpin b)))
  rw [show localPairMGF a q c = ∑ bs, F bs by rfl]
  rw [Fintype.sum_equiv (finTwoArrowEquiv Bool) F
    (fun p => F ((finTwoArrowEquiv Bool).symm p)) (by
      intro x
      apply congrArg F
      funext i
      fin_cases i <;> rfl)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [F, boolSpin, Fin.prod_univ_two, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_eq, Real.cosh_eq]
  ring_nf
  simp only [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

/-- Kearns--Saul at the independent endpoint, in the form needed for the smart path. -/
lemma endpoint_subGaussian
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q) (u : ℝ) :
    nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        2 0
        (fun σs => Real.exp
          ((u / Real.sqrt N) *
            ∑ i : Fin N,
              (spin N (σs 0) i * spin N (σs 1) i - q)))
      ≤ Real.exp (kappa q * u ^ 2 / 2) := by
  classical
  let c : ℝ := u / Real.sqrt N
  let f : ReplicaFun N 2 := fun σs => Real.exp
    (c * ∑ i : Fin N, (spin N (σs 0) i * spin N (σs 1) i - q))
  let F : EnergySpace N → ℝ := fun H =>
    gibbs_average_n_det (N := N) (n := 2)
      (H + H_field (N := N) (h := h)) f
  have hFcont : Continuous F := by
    simp only [F, gibbs_average_n_det]
    apply continuous_finset_sum
    intro σs _
    apply Continuous.mul continuous_const
    apply continuous_finset_prod
    intro l _
    exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous.comp
      (continuous_id.add continuous_const)
  have hHt0 (ω : Ω) :
      H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω =
        sim.V ω + H_field (N := N) (h := h) := by
    simp [H_t, H_gauss]
  have hrefLaw := referenceField_hasGaussianLaw N β q
  have hnu :
      nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 f =
        ∫ z, F (referenceField N β q z) ∂gaussianProduct N := by
    calc
      nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 f =
          ∫ ω, F (sim.V ω) ∂ℙ := by
            rw [nu]
            apply integral_congr_ae
            filter_upwards with ω
            simp only [gibbs_average_n]
            rw [hHt0]
      _ = ∫ H, F H ∂Measure.map sim.V ℙ := by
            rw [integral_map sim.hV.repr_measurable.aemeasurable hFcont.aestronglyMeasurable]
      _ = ∫ H, F H ∂Measure.map (referenceField N β q) (gaussianProduct N) := by
            rw [simpleDisorder_law_eq_reference N β q sim hN hq0]
      _ = ∫ z, F (referenceField N β q z) ∂gaussianProduct N := by
            rw [integral_map hrefLaw.aemeasurable hFcont.aestronglyMeasurable]
  let A : ℝ :=
    ((1 + q) / 2) * Real.exp (c * (1 - q)) +
      ((1 - q) / 2) * Real.exp (-c * (1 + q))
  have htanh : Integrable
      (fun z : ℝ => Real.tanh (h + β * Real.sqrt q * z) ^ 2)
      (gaussianReal 0 1) := by
    have htanh_cont : Continuous Real.tanh := by
      rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x by
        funext x
        exact Real.tanh_eq_sinh_div_cosh x]
      exact Real.continuous_sinh.div Real.continuous_cosh
        (fun x => (Real.cosh_pos x).ne')
    apply (integrable_const (1 : ℝ)).mono
    · exact (htanh_cont.comp (by fun_prop)).pow 2 |>.aestronglyMeasurable
    · filter_upwards with z
      simp only [Real.norm_eq_abs, abs_pow, abs_one]
      rw [sq_abs]
      exact (Real.tanh_sq_lt_one _).le
  have hlocal :
      ∫ z, localPairMGF (h + β * Real.sqrt q * z) q c ∂gaussianReal 0 1 = A := by
    have hT :
        ∫ z, Real.tanh (h + β * Real.sqrt q * z) ^ 2 ∂gaussianReal 0 1 = q := by
      simpa [IsRSFixedPoint, standardGaussianExpectation] using hfp.symm
    rw [show (∫ z, localPairMGF (h + β * Real.sqrt q * z) q c
          ∂gaussianReal 0 1) =
        ∫ z,
          ((Real.exp (c * (1 - q)) + Real.exp (-c * (1 + q))) / 2 +
            Real.tanh (h + β * Real.sqrt q * z) ^ 2 *
              ((Real.exp (c * (1 - q)) - Real.exp (-c * (1 + q))) / 2))
          ∂gaussianReal 0 1 by
      apply integral_congr_ae
      filter_upwards with z
      rw [localPairMGF_eq]
      ring]
    rw [integral_add (integrable_const _)
      (htanh.mul_const ((Real.exp (c * (1 - q)) - Real.exp (-c * (1 + q))) / 2))]
    simp only [integral_const, probReal_univ, one_smul, integral_mul_const, hT]
    simp only [A]
    ring
  have hfactor :
      ∫ z, F (referenceField N β q z) ∂gaussianProduct N = A ^ N := by
    rw [show (∫ z, F (referenceField N β q z) ∂gaussianProduct N) =
        ∫ z, ∏ i : Fin N,
          localPairMGF (h + β * Real.sqrt q * z i) q c ∂gaussianProduct N by
      apply integral_congr_ae
      filter_upwards with z
      simp only [F]
      change gibbs_average_n_det (N := N) (n := 2)
        (referenceField N β q z + magnetic_field_vector (N := N) h) f = _
      rw [reference_add_field_eq_siteEnergy,
        gibbs_average_siteEnergy_pair_mgf]]
    rw [gaussianProduct]
    calc
      (∫ z : Fin N → ℝ, ∏ i : Fin N,
          localPairMGF (h + β * Real.sqrt q * z i) q c
          ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
          (∫ z, localPairMGF (h + β * Real.sqrt q * z) q c
            ∂gaussianReal 0 1) ^ Fintype.card (Fin N) :=
        MeasureTheory.integral_fintype_prod_eq_pow
          (f := fun z : ℝ => localPairMGF (h + β * Real.sqrt q * z) q c)
      _ = A ^ N := by simpa using congrArg (fun x => x ^ N) hlocal
  have hkappa : kappa q = ksCoefficient q := by
    simp [kappa, ksCoefficient]
  have hKS : A ≤ Real.exp (kappa q * c ^ 2 / 2) := by
    simpa only [A, hkappa] using
      (kearns_saul_inequality (u := c) hq0 hq1)
  have hA0 : 0 ≤ A := by
    simp only [A]
    apply add_nonneg
    · exact mul_nonneg (div_nonneg (by linarith) (by norm_num)) (Real.exp_nonneg _)
    · exact mul_nonneg (div_nonneg (by linarith) (by norm_num)) (Real.exp_nonneg _)
  have hpow : A ^ N ≤ (Real.exp (kappa q * c ^ 2 / 2)) ^ N :=
    pow_le_pow_left₀ hA0 hKS N
  rw [show nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      2 0 (fun σs => Real.exp
        ((u / Real.sqrt N) * ∑ i : Fin N,
          (spin N (σs 0) i * spin N (σs 1) i - q))) = A ^ N by
    change nu (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      2 0 f = A ^ N
    exact hnu.trans hfactor]
  calc
    A ^ N ≤ (Real.exp (kappa q * c ^ 2 / 2)) ^ N := hpow
    _ = Real.exp (kappa q * u ^ 2 / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
      simp only [c]
      rw [div_pow, Real.sq_sqrt hNr.le]
      field_simp [ne_of_gt hNr]

/-- Hubbard--Stratonovich combined with `endpoint_subGaussian`. -/
lemma endpoint_quadratic
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q) {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛ : kappa q * Λ < 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 (Λ / 2)
      ≤ (1 / 2) * Real.log (1 / (1 - kappa q * Λ)) := by
  classical
  let F : ReplicaFun N 2 := fun σs => Real.exp
    ((Λ / 2) * (N : ℝ) * centeredOverlapSq N q σs)
  let A : Ω → ℝ := gibbs_average_n
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 F
  let S : ReplicaSpace N 2 → ℝ := fun σs =>
    ∑ i : Fin N, (spin N (σs 0) i * spin N (σs 1) i - q)
  let B : ℝ → Ω → ℝ := fun z ω =>
    gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0
      (fun σs => Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs)) ω
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrtN : Real.sqrt (N : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hNr
  have hS (σs : ReplicaSpace N 2) :
      S σs = (N : ℝ) * (overlap N (σs 0) (σs 1) - q) := by
    simp only [S, overlap, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul]
    field_simp
  have hHS (σs : ReplicaSpace N 2) :
      F σs = ∫ z, Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs)
        ∂gaussianReal 0 1 := by
    calc
      F σs = Real.exp (Λ * (Real.sqrt N *
          (overlap N (σs 0) (σs 1) - q)) ^ 2 / 2) := by
        simp only [F, centeredOverlapSq]
        congr 1
        rw [mul_pow, Real.sq_sqrt hNr.le]
        ring
      _ = ∫ z, Real.exp (Real.sqrt Λ *
          (Real.sqrt N * (overlap N (σs 0) (σs 1) - q)) * z)
          ∂gaussianReal 0 1 := hubbard_stratonovich Λ _ hΛ0
      _ = ∫ z, Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs)
          ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hS]
        congr 1
        field_simp
        rw [Real.sq_sqrt hNr.le]
        ring
  have hlin_int (σs : ReplicaSpace N 2) :
      Integrable (fun z => Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs))
        (gaussianReal 0 1) := by
    convert integrable_exp_mul_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (Real.sqrt Λ * S σs / Real.sqrt N) using 1
    funext z
    congr 1
    ring
  have hAeq (ω : Ω) : A ω = ∫ z, B z ω ∂gaussianReal 0 1 := by
    simp only [A, B, gibbs_average_n, gibbs_average_n_det]
    rw [show (∑ σs : ReplicaSpace N 2,
        F σs * ∏ l, gibbs_pmf N
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)
          (σs l)) =
        ∑ σs : ReplicaSpace N 2,
          (∫ z, Real.exp ((Real.sqrt Λ * z / Real.sqrt N) * S σs)
            ∂gaussianReal 0 1) *
          ∏ l, gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)
            (σs l) by
      congr 1
      funext σs
      rw [hHS]]
    simp_rw [← integral_mul_const]
    rw [integral_finset_sum]
    intro σs _
    exact (hlin_int σs).mul_const _
  have hAint : Integrable A ℙ := by
    exact integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 F
  have hAone (ω : Ω) : 1 ≤ A ω := by
    simp only [A, gibbs_average_n, F, centeredOverlapSq, gibbs_average_n_det]
    rw [← sum_prod_gibbs_pmf_eq_one
      (N := N) (n := 2)
      (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)]
    apply Finset.sum_le_sum
    intro σs _
    have hexp : 1 ≤ Real.exp
        (Λ / 2 * (N : ℝ) * (overlap N (σs 0) (σs 1) - q) ^ 2) :=
      Real.one_le_exp (mul_nonneg
        (mul_nonneg (div_nonneg hΛ0 (by norm_num)) (Nat.cast_nonneg N))
        (sq_nonneg _))
    have hweight : 0 ≤ ∏ l, gibbs_pmf N
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)
        (σs l) := by
      apply Finset.prod_nonneg
      intro l _
      exact gibbs_pmf_nonneg
        (N := N)
        (H := H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) 0 ω)
        (σ := σs l)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hweight
  have hlogAint : Integrable (fun ω => Real.log (A ω)) ℙ := by
    apply hAint.mono'
    · exact (Real.measurable_log.comp_aemeasurable hAint.aemeasurable).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (hAone ω))]
      exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le (hAone ω))).trans
        (sub_le_self _ zero_le_one)
  have hJensen : (∫ ω, Real.log (A ω) ∂ℙ) ≤ Real.log (∫ ω, A ω ∂ℙ) := by
    have hj := (strictConcaveOn_log_Ioi.concaveOn.subset
      (Set.Ici_subset_Ioi.2 zero_lt_one) (convex_Ici (1 : ℝ))).le_map_integral
      (f := A) (μ := ℙ)
      (Real.continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (zero_lt_one.trans_le hx)))
      isClosed_Ici (ae_of_all _ hAone) hAint
      (by simpa only [Function.comp_apply] using hlogAint)
    simpa only [Function.comp_apply] using hj
  have hweight_int (σs : ReplicaSpace N 2) : Integrable (fun ω =>
      ∏ l, gibbs_pmf N
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω)
        (σs l)) ℙ := by
    let I : ReplicaFun N 2 := fun τs => if τs = σs then 1 else 0
    have hi := integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 0 I
    convert hi using 1
    funext ω
    simp [I, gibbs_average_n, gibbs_average_n_det]
  have hBprod : Integrable (fun p : ℝ × Ω => B p.1 p.2)
      ((gaussianReal 0 1).prod ℙ) := by
    simp only [B, gibbs_average_n, gibbs_average_n_det]
    apply integrable_finset_sum
    intro σs _
    exact (hlin_int σs).mul_prod (hweight_int σs)
  have hBbound (z : ℝ) :
      (∫ ω, B z ω ∂ℙ) ≤ Real.exp (kappa q * Λ * z ^ 2 / 2) := by
    have hend := endpoint_subGaussian
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hq0 hq1 hfp (Real.sqrt Λ * z)
    simpa only [B, S, nu, mul_pow, Real.sq_sqrt hΛ0, mul_assoc] using hend
  have hquad_int : Integrable (fun z : ℝ => Real.exp (kappa q * Λ * z ^ 2 / 2))
      (gaussianReal 0 1) := by
    have hi := ProbabilityTheory.integrable_polynomial_exp_sq_gaussian_param_nondeg
      (v := (1 : ℝ≥0)) (by norm_num) 0
      (s := kappa q * Λ / 2) (by norm_num; linarith)
    convert hi using 1
    funext z
    ring
  have hquad_eq :
      (∫ z, Real.exp (kappa q * Λ * z ^ 2 / 2) ∂gaussianReal 0 1) =
        1 / Real.sqrt (1 - kappa q * Λ) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    simp only [smul_eq_mul, gaussianPDFReal]
    norm_num only [NNReal.coe_one, zero_sub, sub_zero, mul_one]
    rw [show (∫ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
        Real.exp (kappa q * Λ * x ^ 2 / 2)) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-((1 - kappa q * Λ) / 2) * x ^ 2) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring]
    rw [integral_gaussian]
    have hgap : 0 < 1 - kappa q * Λ := sub_pos.mpr hΛ
    rw [show Real.pi / ((1 - kappa q * Λ) / 2) =
        (2 * Real.pi) / (1 - kappa q * Λ) by field_simp]
    rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
    field_simp [Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi),
      Real.sqrt_ne_zero'.mpr hgap]
  have hAmean : (∫ ω, A ω ∂ℙ) ≤ 1 / Real.sqrt (1 - kappa q * Λ) := by
    calc
      (∫ ω, A ω ∂ℙ) = ∫ ω, ∫ z, B z ω ∂gaussianReal 0 1 ∂ℙ := by
        apply integral_congr_ae
        exact ae_of_all _ hAeq
      _ = ∫ z, ∫ ω, B z ω ∂ℙ ∂gaussianReal 0 1 := by
        exact (integral_integral_swap hBprod).symm
      _ ≤ ∫ z, Real.exp (kappa q * Λ * z ^ 2 / 2) ∂gaussianReal 0 1 := by
        exact integral_mono hBprod.integral_prod_left hquad_int hBbound
      _ = 1 / Real.sqrt (1 - kappa q * Λ) := hquad_eq
  have hAmean_one : 1 ≤ ∫ ω, A ω ∂ℙ := by
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono (integrable_const (1 : ℝ)) hAint hAone
  change (∫ ω, Real.log (A ω) ∂ℙ) ≤
    (1 / 2) * Real.log (1 / (1 - kappa q * Λ))
  calc
    (∫ ω, Real.log (A ω) ∂ℙ) ≤ Real.log (∫ ω, A ω ∂ℙ) := hJensen
    _ ≤ Real.log (1 / Real.sqrt (1 - kappa q * Λ)) :=
      Real.log_le_log (zero_lt_one.trans_le hAmean_one) hAmean
    _ = (1 / 2) * Real.log (1 / (1 - kappa q * Λ)) := by
      have hgap : 0 ≤ 1 - kappa q * Λ := (sub_pos.mpr hΛ).le
      simp only [one_div, ← Real.sqrt_inv]
      rw [Real.log_sqrt (inv_nonneg.mpr hgap)]
      ring

/-! ## Gaussian interpolation and quadratic coupling -/

/-- Differentiation of the smart-path pressure before Gaussian integration by parts. -/
lemma pressure_derivative_before_ibp
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
      (∫ w,
        fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
        ∂ℙ) t := by
  classical
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have h1t0 : 0 < 1 - t := by linarith
  let ε : ℝ := (min t (1 - t)) / 2
  have hε_pos : 0 < ε := by
    have hmin : 0 < min t (1 - t) := lt_min ht0 h1t0
    have : 0 < (min t (1 - t)) / 2 := by linarith
    simpa [ε] using this
  have hball_Ioo : ∀ x ∈ Metric.ball t ε, x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    have hx' : |x - t| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, ε] using hx
    have hx1 : x - t < ε := (abs_sub_lt_iff.1 hx').1
    have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
    have hε_le_t : ε ≤ t / 2 := by
      have : min t (1 - t) ≤ t := min_le_left _ _
      have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
      simpa [ε] using this
    have hε_le_1t : ε ≤ (1 - t) / 2 := by
      have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
      have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
      simpa [ε] using this
    have hx_lower : t / 2 < x := by
      have ht_eps : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
      have hx_gt : t - ε < x := by linarith
      exact lt_of_le_of_lt ht_eps hx_gt
    have hx_gt0 : 0 < x := by
      have ht_eps : t - ε ≥ t / 2 := by nlinarith [hε_le_t]
      have hx_gt : t - ε < x := by linarith
      have : t / 2 < x := lt_of_le_of_lt ht_eps hx_gt
      have : 0 < t / 2 := by nlinarith [ht0]
      exact Std.lt_trans this hx_lower
    have hx_lt1 : x < 1 := by
      have hx_lt : x < t + ε := by linarith
      have ht_eps : t + ε ≤ (1 + t) / 2 := by nlinarith [hε_le_1t]
      have : x < (1 + t) / 2 := lt_of_lt_of_le hx_lt ht_eps
      have : (1 + t) / 2 < 1 := by nlinarith [ht1]
      simp; grind
    exact ⟨hx_gt0, hx_lt1⟩
  let F : ℝ → Ω → ℝ :=
    fun s w => free_energy_density (N := N) (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
  let F' : ℝ → Ω → ℝ :=
    fun s w =>
      fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
  have hF_meas : ∀ᶠ s in nhds t, AEStronglyMeasurable (F s) (ℙ : Measure Ω) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have hH_meas : Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s) := by
      have hU := sk.hU.repr_measurable.const_smul (Real.sqrt s)
      have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - s))
      simpa [H_t, H_gauss] using (hU.add hV).add measurable_const
    exact ((contDiff_free_energy_density (N := N)).continuous.measurable.comp
      hH_meas).aestronglyMeasurable
  have hF_int : Integrable (F t) (ℙ : Measure Ω) := by
    let C : ℝ := (SpinGlass.hasModerateGrowth_free_energy_density N).C
    have hH_meas : Measurable
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
      have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
      have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
      simpa [H_t, H_gauss] using (hU.add hV).add measurable_const
    have hF_meas : AEStronglyMeasurable (F t) (ℙ : Measure Ω) :=
      ((contDiff_free_energy_density (N := N)).continuous.measurable.comp
        hH_meas).aestronglyMeasurable
    let boundFun : Ω → ℝ := fun w => C * (1 + ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖)
    have hbound_int : Integrable boundFun (ℙ : Measure Ω) := by
      apply Integrable.const_mul
      exact (((integrable_const (1 : ℝ)).add
        (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sk.U) sk.hU)).add
          (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sim.V) sim.hV)).add
            (integrable_const _)
    refine MeasureTheory.Integrable.mono' hbound_int hF_meas ?_
    have hsqrtt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
    have hsqrtt1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr (le_of_lt ht1)
    have hsqrt1t0 : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
    have hsqrt1t1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [ht0])
    filter_upwards with w
    have hnorm : ‖H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖ ≤
        ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
      calc
        ‖H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖
            ≤ ‖(Real.sqrt t) • sk.U w‖ + ‖(Real.sqrt (1 - t)) • sim.V w‖ +
                ‖H_field (N := N) (h := h)‖ := by
          simp only [H_t, H_gauss]
          exact (norm_add_le
            ((Real.sqrt t) • sk.U w + (Real.sqrt (1 - t)) • sim.V w)
            (H_field (N := N) (h := h))).trans
            (by
              gcongr
              exact norm_add_le ((Real.sqrt t) • sk.U w)
                ((Real.sqrt (1 - t)) • sim.V w))
        _ ≤ ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hsqrtt0, abs_of_nonneg hsqrt1t0]
            gcongr
            · exact mul_le_of_le_one_left (norm_nonneg _) hsqrtt1
            · exact mul_le_of_le_one_left (norm_nonneg _) hsqrt1t1
    have hgrowth :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).F_bound
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
    have hm : (SpinGlass.hasModerateGrowth_free_energy_density N).m = 1 := by rfl
    rw [hm, pow_one] at hgrowth
    rw [Real.norm_eq_abs]
    have hinside : 1 + ‖H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖ ≤
        1 + ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hinside
      (le_of_lt (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos)
    exact hgrowth.trans (by simpa only [C] using hmul)
  -- Define the bound
  let Cf : ℝ := 1 / (N : ℝ)
  let cU : ℝ := 1 / (2 * Real.sqrt (t / 2))
  let cV : ℝ := 1 / (2 * Real.sqrt ((1 - t) / 2))
  let bound : Ω → ℝ := fun w => Cf * (cU * ‖sk.U w‖ + cV * ‖sim.V w‖)
  have hCf_nonneg : 0 ≤ Cf := by positivity
  have hcU_nonneg : 0 ≤ cU := by positivity
  have hcV_nonneg : 0 ≤ cV := by positivity
  have hbound_int : Integrable bound (ℙ : Measure Ω) := by
    have hU_int : Integrable (fun w => ‖sk.U w‖) (ℙ : Measure Ω) :=
      (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sk.U) sk.hU)
    have hV_int : Integrable (fun w => ‖sim.V w‖) (ℙ : Measure Ω) :=
      (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sim.V) sim.hV)
    have h1 : Integrable (fun w => cU * ‖sk.U w‖) (ℙ : Measure Ω) := (hU_int.const_mul cU)
    have h2 : Integrable (fun w => cV * ‖sim.V w‖) (ℙ : Measure Ω) := (hV_int.const_mul cV)
    have hsum : Integrable (fun w => cU * ‖sk.U w‖ + cV * ‖sim.V w‖) (ℙ : Measure Ω) := h1.add h2
    simpa [bound, Cf, mul_add, mul_assoc] using hsum.const_mul Cf
  have hF'_meas : AEStronglyMeasurable (F' t) (ℙ : Measure Ω) := by
    have hdH_meas : Measurable (fun w => dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      simp only [dH_t]
      have hU := sk.hU.repr_measurable.const_smul ((1 : ℝ) / (2 * Real.sqrt t))
      have hV := sim.hV.repr_measurable.const_smul ((1 : ℝ) / (2 * Real.sqrt (1 - t)))
      simpa [sub_eq_add_neg, neg_smul] using hU.add (hV.neg)
    have hHM : Measurable (fun w => H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
      have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
      simpa [H_t, H_gauss] using (hU.add hV).add measurable_const
    have hfderiv_cont : Continuous (fun p : EnergySpace N × EnergySpace N =>
        fderiv ℝ (fun H => free_energy_density (N := N) H) p.1 p.2) := by
      have hcd := contDiff_free_energy_density (N := N)
      have hfderiv_cont' : Continuous (fun H => fderiv ℝ (fun H => free_energy_density (N := N) H) H) :=
        hcd.continuous_fderiv (by simp)
      exact ((hfderiv_cont'.comp continuous_fst).clm_apply continuous_snd)
    have hpair : Measurable (fun w => (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w,
        dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)) :=
      hHM.prodMk hdH_meas
    exact (hfderiv_cont.measurable.comp hpair).aestronglyMeasurable
  have h_bound :
      ∀ᵐ w ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε, ‖F' x w‖ ≤ bound w := by
    refine ae_of_all _ (fun w => ?_)
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := hball_Ioo x hx
    -- Bound the operator norm of the derivative of free_energy_density
    have h_op :
        ‖fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ ≤ (1 / (N : ℝ)) := by
      refine ContinuousLinearMap.opNorm_le_bound _ hCf_nonneg ?_
      intro v
      have h_eval :
          (fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)) v =
            -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * v σ :=
        fderiv_free_energy_density_apply (N := N)
          (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) (h := v)
      have hs1 : (∑ σ : Config N, gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) = 1 :=
        sum_gibbs_pmf (N := N)
          (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)
      have hsum_bound :
          |∑ σ : Config N, gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| ≤ ‖v‖ := by
        have h_abs_le :
            |∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ|
              ≤ ∑ σ : Config N, |gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σ : Config N => gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ)
              (s := (Finset.univ : Finset (Config N))))
        have h_abs_term :
            (∑ σ : Config N, |gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ|)
              = ∑ σ : Config N, (gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * |v σ| := by
          refine Finset.sum_congr rfl ?_
          intro σ _hσ
          have hg : 0 ≤ gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ :=
            gibbs_pmf_nonneg (N := N)
              (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ
          simp [abs_mul, abs_of_nonneg hg]
        have hsum_le :
            (∑ σ : Config N, (gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * |v σ|)
              ≤ (∑ σ : Config N, gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖ := by
          have hterm : ∀ σ : Config N, (gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * |v σ|
                ≤ (gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖ := by
            intro σ
            have hσ : |v σ| ≤ ‖v‖ := (abs_apply_le_norm (N := N) v σ)
            exact mul_le_mul_of_nonneg_left hσ (gibbs_pmf_nonneg (N := N)
              (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ)
          have hsum' :=
            (Finset.sum_le_sum (s := (Finset.univ : Finset (Config N)))
              (fun σ _ => hterm σ))
          have hfactor :
              (∑ σ : Config N, (gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖)
                = (∑ σ : Config N, gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖ := by
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
                (f := fun σ : Config N => gibbs_pmf N
                  (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ)
                (a := ‖v‖)).symm
          simpa [hfactor] using hsum'
        calc
          |∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ|
            ≤ ∑ σ : Config N, |gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| := h_abs_le
          _ = ∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * |v σ| := h_abs_term
          _ ≤ (∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ) * ‖v‖ := hsum_le
          _ = ‖v‖ := by simp [hs1]
      have : ‖(fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)) v‖
          ≤ (1 / (N : ℝ)) * ‖v‖ := by
        have :
            ‖(fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)) v‖
              = (1 / (N : ℝ)) * |∑ σ : Config N, gibbs_pmf N
                (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| := by
          simp [h_eval, Real.norm_eq_abs]
        calc
          ‖(fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)) v‖
          = (1 / (N : ℝ)) * |∑ σ : Config N, gibbs_pmf N
              (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) σ * v σ| := this
          _ ≤ (1 / (N : ℝ)) * ‖v‖ := by
                exact mul_le_mul_of_nonneg_left hsum_bound hCf_nonneg
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    have hL :
        ‖fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ ≤ Cf := by
      simpa [Cf] using h_op
    -- Bound the coefficients
    have hCoeffU :
        |1 / (2 * Real.sqrt x)| ≤ cU := by
      have hx_gt0 : 0 < x := hxIoo.1
      have hx_lower : t / 2 ≤ x := by
        have hx' : |x - t| < ε := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
        have hx2 : t - x < ε := (abs_sub_lt_iff.1 hx').2
        have hε_le_t : ε ≤ t / 2 := by
          have : min t (1 - t) ≤ t := min_le_left _ _
          have : (min t (1 - t)) / 2 ≤ t / 2 := by nlinarith
          simpa [ε] using this
        have hx_gt : t - ε < x := by linarith
        have ht_eps : t / 2 ≤ t - ε := by nlinarith [hε_le_t]
        exact le_trans ht_eps (le_of_lt hx_gt)
      have hsqrt_le : Real.sqrt (t / 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx_lower
      have hpos : 0 < 2 * Real.sqrt (t / 2) := by
        have : 0 < Real.sqrt (t / 2) := by
          have : 0 < t / 2 := by nlinarith [ht0]
          exact Real.sqrt_pos.2 this
        nlinarith
      have hle :
          2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt x := by nlinarith [hsqrt_le]
      have : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt (t / 2)) := by
        simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
      have hnonneg : 0 ≤ 1 / (2 * Real.sqrt x) := by positivity
      have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt (t / 2)) := by positivity
      simpa [cU, abs_of_nonneg hnonneg, abs_of_nonneg hnonneg', abs_of_nonneg (Real.sqrt_nonneg x), one_div]
        using this
    have hCoeffV :
        |1 / (2 * Real.sqrt (1 - x))| ≤ cV := by
      have hx_lt1 : x < 1 := hxIoo.2
      have h1x_pos : 0 < 1 - x := by linarith
      have h1x_lower : (1 - t) / 2 ≤ 1 - x := by
        have hx' : |x - t| < ε := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx
        have hx1 : x - t < ε := (abs_sub_lt_iff.1 hx').1
        have hε_le_1t : ε ≤ (1 - t) / 2 := by
          have : min t (1 - t) ≤ (1 - t) := min_le_right _ _
          have : (min t (1 - t)) / 2 ≤ (1 - t) / 2 := by nlinarith
          simpa [ε] using this
        have hx_le : x ≤ t + (1 - t) / 2 := by
          have hx_le' : x ≤ t + ε := by linarith
          exact le_trans hx_le' (by nlinarith [hε_le_1t])
        nlinarith [hx_le]
      have hsqrt_le : Real.sqrt ((1 - t) / 2) ≤ Real.sqrt (1 - x) := Real.sqrt_le_sqrt h1x_lower
      have hpos : 0 < 2 * Real.sqrt ((1 - t) / 2) := by
        have : 0 < (1 - t) / 2 := by nlinarith [h1t0]
        have : 0 < Real.sqrt ((1 - t) / 2) := Real.sqrt_pos.2 this
        nlinarith
      have hle :
          2 * Real.sqrt ((1 - t) / 2) ≤ 2 * Real.sqrt (1 - x) := by nlinarith [hsqrt_le]
      have : 1 / (2 * Real.sqrt (1 - x)) ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by
        simpa [one_div] using (one_div_le_one_div_of_le hpos hle)
      have hnonneg : 0 ≤ 1 / (2 * Real.sqrt (1 - x)) := by positivity
      have hnonneg' : 0 ≤ 1 / (2 * Real.sqrt ((1 - t) / 2)) := by positivity
      simpa [cV, abs_of_nonneg hnonneg, abs_of_nonneg hnonneg',
        abs_of_nonneg (Real.sqrt_nonneg (1 - x)), one_div] using this
    -- Bound ‖dH_t x w‖
    have hdH_norm :
        ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
          ≤ cU * ‖sk.U w‖ + cV * ‖sim.V w‖ := by
      have htri :
          ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
            ≤ |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
              |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖ := by
        simpa [dH_t, sub_eq_add_neg, norm_add_le, norm_smul, abs_mul] using
          (norm_add_le ((1 / (2 * Real.sqrt x)) • sk.U w) (-(1 / (2 * Real.sqrt (1 - x))) • sim.V w))
      have : |1 / (2 * Real.sqrt x)| * ‖sk.U w‖ +
            |1 / (2 * Real.sqrt (1 - x))| * ‖sim.V w‖
          ≤ cU * ‖sk.U w‖ + cV * ‖sim.V w‖ := by
        gcongr
      exact le_trans htri this
    -- Combine bounds
    have hF'_bound :
        ‖F' x w‖ ≤ Cf * ‖dH_t (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) x w‖ := by
      have hop : ‖(fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
            (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖
          ≤ ‖fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ *
            ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hmul :
          ‖fderiv ℝ (fun H' => free_energy_density (N := N) H')
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w)‖ *
            ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖
          ≤ Cf * ‖dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      simpa [F'] using le_trans hop hmul
    have : ‖F' x w‖ ≤ bound w := by
      have : ‖F' x w‖ ≤ Cf * (cU * ‖sk.U w‖ + cV * ‖sim.V w‖) := by
        exact le_trans hF'_bound (mul_le_mul_of_nonneg_left hdH_norm (hCf_nonneg))
      simpa [bound, mul_add, mul_assoc, mul_left_comm, mul_comm] using this
    exact this
  have h_diff :
      ∀ᵐ w ∂(ℙ : Measure Ω), ∀ x ∈ Metric.ball t ε,
        HasDerivAt (fun s => F s w) (F' x w) x := by
    refine ae_of_all _ (fun w => ?_)
    intro x hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := hball_Ioo x hx
    -- Chain rule: F = free_energy_density ∘ H_t, so dF/ds = fderiv(free_energy_density) ∘ dH_t/ds
    have hHt_diff : HasDerivAt
        (fun s => H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s w)
        (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) x :=
      hasDerivAt_H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x hxIoo w
    have hFed : HasFDerivAt (fun H => free_energy_density (N := N) H)
        (fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w))
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) x w) :=
      ((contDiff_free_energy_density (N := N)).differentiable (by simp) ).differentiableAt.hasFDerivAt
    have hcomp := hFed.comp_hasDerivAt x hHt_diff
    simpa [F, F'] using hcomp
  have hMain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (ℙ : Measure Ω)) (F := F) (F' := F') (x₀ := t) (bound := bound)
      (s := Metric.ball t ε) (hs := Metric.ball_mem_nhds t hε_pos)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  simpa [interpolatedPressure, F] using hMain

/-!
### How to invoke the Hilbert-space Gaussian IBP theorem

The theorem intended here is
`PhysLean.Probability.GaussianIBP.gaussian_integration_by_parts_hilbert_cov_op` from
`SpinGlass.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert`.  Its schematic form is

```
E[⟪g, e⟫ * F(g)] = E[(fderiv ℝ F (g)) ((covOp hg) e)].
```

It requires `hg : IsGaussianHilbert g`, `ContDiff ℝ 1 F`, and
`HasModerateGrowth F`.  The disorder structures already provide the Gaussian models
`sk.hU` and `sim.hV`, while `sk.cov_eq` and `sim.cov_eq` identify the matrix entries of their
covariance operators in the configuration basis.

There is one important formal point.  The first-variation test function depends on both
`sk.U` and `sim.V`, so calling the theorem on `sk.hU` while leaving `sim.V ω` inside the test
function is not valid.  A convenient bridge is a local lemma constructing

```
G ω := (sk.U ω, sim.V ω)
```

as an `IsGaussianHilbert` random variable on the product Hilbert space.  Build its basis from
the two component bases, and use `hIndep` to prove that the two coordinate families are jointly
independent.  Its covariance operator is block diagonal.  This bridge is the only additional
Gaussian-model construction needed by the two lemmas below.

For the SK term, set

```
Φ p := free_energy_density (N := N) (a • p.1 + b • p.2 + field)
Fσ p := (fderiv ℝ Φ p) (std_basis N σ, 0)
```

and expand the random direction in the configuration basis.  For each `σ`, the main call is
schematically

```
have hIBP :=
  PhysLean.Probability.GaussianIBP.gaussian_integration_by_parts_hilbert_cov_op
    (hg := hG) (h := (std_basis N σ, 0)) (F := Fσ)
    (hF_diff := hFσ_diff) (hF_growth := hFσ_growth)
```

The derivative of `Fσ` is the Hessian of the pressure.  Expand the block covariance vector in
the configuration basis, use `sk.cov_eq σ τ`, interchange the finite sums with the integral,
and collect `a * a'`.  The simple-disorder term uses `(0, std_basis N σ)` and
`sim.cov_eq σ τ` in exactly the same way.

The required smoothness follows from `contDiff_free_energy_density`.  For moderate growth,
prove a small helper for each `Fσ`; the explicit Gibbs Hessian is uniformly bounded in finite
volume, so a constant polynomial bound suffices.  The integrability helpers surrounding the
IBP theorem then justify every finite-sum and expectation interchange.
-/

/-- The `SKDisorder` contribution to joint Gaussian integration by parts.

Proof route: use the joint Gaussian model `G` described above and apply
`gaussian_integration_by_parts_hilbert_cov_op` along `(std_basis N σ, 0)`.  The derivative of
the test function is `hessian_free_energy`; reconstruct the SK covariance block from its basis
entries and rewrite them with `sk.cov_eq`. -/
lemma sk_affine_firstVariation_ibp
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    (a b a' : ℝ) (field : EnergySpace N) :
    (∫ w,
      fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
        (a • sk.U w + b • sim.V w + field) (a' • sk.U w) ∂ℙ) =
      (a * a') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
        sk_cov_kernel N β σ τ * hessian_free_energy N
          (a • sk.U w + b • sim.V w + field)
          (std_basis N σ) (std_basis N τ)) ∂ℙ := by
  sorry

/-- The `SimpleDisorder` contribution to joint Gaussian integration by parts.

Use the same joint model and the same operator-form theorem, now along
`(0, std_basis N σ)`.  Block diagonality removes all cross-covariance terms, and `sim.cov_eq`
turns the remaining covariance entries into `simple_cov_kernel`. -/
lemma simple_affine_firstVariation_ibp
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    (a b b' : ℝ) (field : EnergySpace N) :
    (∫ w,
      fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
        (a • sk.U w + b • sim.V w + field) (b' • sim.V w) ∂ℙ) =
      (b * b') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
        simple_cov_kernel N β (fun x => q * x) σ τ * hessian_free_energy N
          (a • sk.U w + b • sim.V w + field)
          (std_basis N σ) (std_basis N τ)) ∂ℙ := by
  sorry

/-- Gaussian integration by parts for an affine combination of two independent Gaussian
Hamiltonians, expressed in the canonical configuration basis.

Proof route: use linearity of the first variation in its direction, split the integral into the
`sk.U` and `sim.V` parts, apply `sk_affine_firstVariation_ibp` and
`simple_affine_firstVariation_ibp`, and collect the scalar coefficients. -/
lemma independent_gaussian_affine_ibp
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    (a b a' b' : ℝ) (field : EnergySpace N) :
    (∫ w,
      fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
        (a • sk.U w + b • sim.V w + field) (a' • sk.U w + b' • sim.V w) ∂ℙ) =
      (a * a') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
        sk_cov_kernel N β σ τ * hessian_free_energy N
          (a • sk.U w + b • sim.V w + field)
          (std_basis N σ) (std_basis N τ)) ∂ℙ +
      (b * b') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
        simple_cov_kernel N β (fun x => q * x) σ τ * hessian_free_energy N
          (a • sk.U w + b • sim.V w + field)
          (std_basis N σ) (std_basis N τ)) ∂ℙ := by
  sorry

/-- Joint Gaussian integration by parts for the raw smart-path derivative, before evaluating
its two covariance traces. -/
lemma pressure_derivative_ibp_trace
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ w,
        fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
        ∂ℙ) =
      (1 / 2) * ∫ w,
        (∑ σ : Config N, ∑ τ : Config N,
          (sk_cov_kernel N β σ τ -
            simple_cov_kernel N β (fun x => q * x) σ τ) *
          hessian_free_energy N
            (H_t (N := N) (β := β) (h := h) (q := q)
              (sk := sk) (sim := sim) t w)
            (std_basis N σ) (std_basis N τ)) ∂ℙ := by
  have ht0 : t > 0 := ht.1
  have ht1 : t < 1 := ht.2
  -- Set up the IBP parameters
  set a := Real.sqrt t with ha_def
  set b := Real.sqrt (1 - t) with hb_def
  set a' := 1 / (2 * Real.sqrt t) with ha'_def
  set b' := -1 / (2 * Real.sqrt (1 - t)) with hb'_def
  -- Apply the independent_gaussian_affine_ibp lemma
  have h_ibp := independent_gaussian_affine_ibp (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hIndep a b a' b' (H_field (N := N) (h := h))
  -- Show that a * a' = 1/2 and b * b' = -1/2
  have ha_aa' : a * a' = 1 / 2 := by
    simp [ha_def, ha'_def]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr ht0)]
  have hb_bb' : b * b' = -(1 / 2) := by
    simp [hb_def, hb'_def]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr ht1))]
  -- Show that a • sk.U w + b • sim.V w + H_field = H_t t w
  have h_eq_H : H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t =
      fun w => a • sk.U w + b • sim.V w + H_field (N := N) (h := h) := by
    unfold H_t H_gauss
    simp [ha_def, hb_def]
  -- Show that a' • sk.U w + b' • sim.V w = dH_t t w
  have h_eq_dH : dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t =
      fun w => a' • sk.U w + b' • sim.V w := by
    unfold dH_t
    ext w
    simp [ha'_def, hb'_def]
    ring
  -- Rewrite h_ibp using the equalities
  have h_ibp' : ∫ w, fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) ∂ℙ =
    (a * a') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
      sk_cov_kernel N β σ τ * hessian_free_energy N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (std_basis N σ) (std_basis N τ)) ∂ℙ +
    (b * b') * ∫ w, (∑ σ : Config N, ∑ τ : Config N,
      simple_cov_kernel N β (fun x => q * x) σ τ * hessian_free_energy N (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) (std_basis N σ) (std_basis N τ)) ∂ℙ := by
    simp only [h_eq_H, h_eq_dH] at *
    convert h_ibp using 2
  -- Substitute a * a' = 1/2 and b * b' = -1/2
  rw [ha_aa', hb_bb'] at h_ibp'
  -- Combine the integrals
  convert h_ibp' using 1
  have integral_eq : ∀ w, ∑ σ, ∑ τ, (sk_cov_kernel N β σ τ - simple_cov_kernel N β (fun x => q * x) σ τ) *
      hessian_free_energy N (H_t N β h q sk sim t w) (std_basis N σ) (std_basis N τ) =
      (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N (H_t N β h q sk sim t w) (std_basis N σ) (std_basis N τ)) -
      (∑ σ, ∑ τ, simple_cov_kernel N β (fun x => q * x) σ τ * hessian_free_energy N (H_t N β h q sk sim t w) (std_basis N σ) (std_basis N τ)) := by
    intro w
    simp_rw [sub_mul]
    simp only [Finset.sum_sub_distrib]
  -- Bound on hessian_free_energy for standard basis
  have std_basis_apply : ∀ σ τ : Config N, (std_basis N σ) τ = if σ = τ then 1 else 0 := by
    intro σ τ
    simp [std_basis]
  have hess_bound : ∀ H : EnergySpace N, ∀ σ τ : Config N,
      |hessian_free_energy N H (std_basis N σ) (std_basis N τ)| ≤ 1 / (N : ℝ) := by
    intro H σ τ
    simp only [hessian_free_energy, std_basis_apply]
    -- Simplify the sums
    have sum1 : ∑ x : Config N, gibbs_pmf N H x * (if σ = x then (1 : ℝ) else 0) = gibbs_pmf N H σ := by
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq (s := Finset.univ)]
      simp [Finset.mem_univ]
    have sum2 : ∑ x : Config N, gibbs_pmf N H x * (if τ = x then (1 : ℝ) else 0) = gibbs_pmf N H τ := by
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq (s := Finset.univ)]
      simp [Finset.mem_univ]
    -- Note: the actual form is (gibbs_pmf N H x * if σ = x then 1 else 0) * if τ = x then 1 else 0
    have sum_cross : ∑ x : Config N, (gibbs_pmf N H x * (if σ = x then (1 : ℝ) else 0)) * (if τ = x then (1 : ℝ) else 0) =
        if σ = τ then gibbs_pmf N H σ else 0 := by
      by_cases hστ : σ = τ
      · subst hστ
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq (s := Finset.univ)]
        simp
      · simp [hστ]
    rw [sum1, sum2, sum_cross]
    split_ifs with hστ
    · -- Case σ = τ
      subst hστ
      have hp := gibbs_pmf_nonneg N H σ
      have hp' := gibbs_pmf_le_one N H σ
      have habs : |gibbs_pmf N H σ - gibbs_pmf N H σ * gibbs_pmf N H σ| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith
      have hN_nonneg : (0 : ℝ) ≤ 1 / N := by positivity
      rw [abs_mul, abs_of_nonneg hN_nonneg]
      by_cases hN0 : N = 0
      · simp [hN0]
      · have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
        have hNge : 1 ≤ N := Nat.pos_of_ne_zero hN0
        have hN : (1 : ℝ) / N ≤ 1 := by
          rw [div_le_iff₀ hN_pos]
          simp [hNge]
        exact mul_le_of_le_one_right hN_nonneg habs
    · -- Case σ ≠ τ
      have hp := gibbs_pmf_nonneg N H σ
      have hp := gibbs_pmf_nonneg N H σ
      have hp' := gibbs_pmf_le_one N H σ
      have hq := gibbs_pmf_nonneg N H τ
      have hq' := gibbs_pmf_le_one N H τ
      have hprod : |gibbs_pmf N H σ * gibbs_pmf N H τ| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
        nlinarith
      have hN_nonneg : (0 : ℝ) ≤ 1 / N := by positivity
      rw [abs_mul, abs_of_nonneg hN_nonneg]
      by_cases hN0 : N = 0
      · simp [hN0]
      · have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
        have hNge : 1 ≤ N := Nat.pos_of_ne_zero hN0
        have hN : (1 : ℝ) / N ≤ 1 := by
          rw [div_le_iff₀ hN_pos]
          simp [hNge]
        have heq : |0 - gibbs_pmf N H σ * gibbs_pmf N H τ| = |gibbs_pmf N H σ * gibbs_pmf N H τ| := by
          rw [zero_sub, abs_neg]
        nlinarith
  -- Integrability of finite sums of bounded functions
  have h_int1 : MeasureTheory.Integrable
      (fun x => ∑ σ : Config N, ∑ τ : Config N,
        sk_cov_kernel N β σ τ * hessian_free_energy N (H_t N β h q sk sim t x) (std_basis N σ) (std_basis N τ))
      ℙ := by
    apply MeasureTheory.integrable_finset_sum _
    intro σ _
    apply MeasureTheory.integrable_finset_sum _
    intro τ _
    refine MeasureTheory.Integrable.const_mul ?_ (sk_cov_kernel N β σ τ)
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 / (N : ℝ))) ?_ ?_
    · have hH_meas : Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
        have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
        have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
        simpa [H_t, H_gauss] using (hU.add hV).add measurable_const
      have hheff_meas : Measurable (fun H => hessian_free_energy N H (std_basis N σ) (std_basis N τ)) := by
        have h1 : Measurable (fun H => gibbs_pmf N H σ) := (contDiff_gibbs_pmf (N := N) (σ := σ)).continuous.measurable
        have h2 : Measurable (fun H => gibbs_pmf N H τ) := (contDiff_gibbs_pmf (N := N) (σ := τ)).continuous.measurable
        simp_rw [hessian_free_energy]
        apply Measurable.mul measurable_const
        apply Measurable.sub
        · exact Finset.measurable_sum _ fun x _ => by
            apply Measurable.mul _ measurable_const
            apply Measurable.mul _ measurable_const
            exact (contDiff_gibbs_pmf (N := N) (σ := x)).continuous.measurable
        · apply Measurable.mul
          · exact Finset.measurable_sum _ fun x _ => by
              apply Measurable.mul
              · exact (contDiff_gibbs_pmf (N := N) (σ := x)).continuous.measurable
              exact measurable_const
          · exact Finset.measurable_sum _ fun x _ => by
              apply Measurable.mul
              · exact (contDiff_gibbs_pmf (N := N) (σ := x)).continuous.measurable
              exact measurable_const
      exact (hheff_meas.comp hH_meas).aestronglyMeasurable
    · filter_upwards with x
      exact hess_bound (H_t N β h q sk sim t x) σ τ
  have h_int2 : MeasureTheory.Integrable
      (fun x => ∑ σ : Config N, ∑ τ : Config N,
        simple_cov_kernel N β (fun x => q * x) σ τ * hessian_free_energy N (H_t N β h q sk sim t x) (std_basis N σ) (std_basis N τ))
      ℙ := by
    apply MeasureTheory.integrable_finset_sum _
    intro σ _
    apply MeasureTheory.integrable_finset_sum _
    intro τ _
    refine MeasureTheory.Integrable.const_mul ?_ (simple_cov_kernel N β (fun x => q * x) σ τ)
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 / (N : ℝ))) ?_ ?_
    · have hH_meas : Measurable (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
        have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
        have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
        simpa [H_t, H_gauss] using (hU.add hV).add measurable_const
      have hheff_meas : Measurable (fun H => hessian_free_energy N H (std_basis N σ) (std_basis N τ)) := by
        have h1 : Measurable (fun H => gibbs_pmf N H σ) := (contDiff_gibbs_pmf (N := N) (σ := σ)).continuous.measurable
        have h2 : Measurable (fun H => gibbs_pmf N H τ) := (contDiff_gibbs_pmf (N := N) (σ := τ)).continuous.measurable
        simp_rw [hessian_free_energy]
        apply Measurable.mul measurable_const
        apply Measurable.sub
        · exact Finset.measurable_sum _ fun x _ => by
            apply Measurable.mul _ measurable_const
            apply Measurable.mul _ measurable_const
            exact (contDiff_gibbs_pmf (N := N) (σ := x)).continuous.measurable
        · apply Measurable.mul
          · exact Finset.measurable_sum _ fun x _ => by
              apply Measurable.mul
              · exact (contDiff_gibbs_pmf (N := N) (σ := x)).continuous.measurable
              exact measurable_const
          · exact Finset.measurable_sum _ fun x _ => by
              apply Measurable.mul
              · exact (contDiff_gibbs_pmf (N := N) (σ := x)).continuous.measurable
              exact measurable_const
      exact (hheff_meas.comp hH_meas).aestronglyMeasurable
    · filter_upwards with x
      exact hess_bound (H_t N β h q sk sim t x) σ τ
  rw [funext integral_eq, MeasureTheory.integral_sub h_int1 h_int2]
  rw [mul_sub]
  ring

/-
The covariance-trace difference is the centered-overlap square, pointwise in the disorder.
-/
lemma pressure_trace_algebra
    (hN : 0 < N) (H : EnergySpace N) :
    (1 / 2) *
        (∑ σ : Config N, ∑ τ : Config N,
          (sk_cov_kernel N β σ τ -
            simple_cov_kernel N β (fun x => q * x) σ τ) *
          hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
      (β ^ 2 / 4) * ((1 - q) ^ 2 -
        gibbs_average_n_det (N := N) (n := 2) H (centeredOverlapSq N q)) := by
  unfold gibbs_average_n_det centeredOverlapSq;
  have h_sum_gibbs_pmf : ∑ σ : Config N, gibbs_pmf N H σ = 1 := by
    exact sum_gibbs_pmf (N := N) (H := H)
  have h_sum_prod_gibbs_pmf : ∑ σs : ReplicaSpace N 2, (∏ l, gibbs_pmf N H (σs l)) * (overlap N (σs 0) (σs 1) - q) ^ 2 = ∑ σ : Config N, ∑ τ : Config N, gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ - q) ^ 2 := by
    rw [ ← Finset.sum_product' ];
    refine' Finset.sum_bij ( fun x _ => ( x 0, x 1 ) ) _ _ _ _ <;> simp +decide;
    · exact fun a₁ a₂ h₀ h₁ => funext fun i => by fin_cases i <;> assumption;
    · exact fun a b => ⟨ fun i => if i = 0 then a else b, rfl, rfl ⟩;
  convert congr_arg ( fun x : ℝ => β ^ 2 / 4 * ( ( 1 - q ) ^ 2 - x ) ) h_sum_prod_gibbs_pmf using 1;
  · convert SpinGlass.guerra_derivative_bound_algebra_core hN H ( fun x => q * x ) using 1;
    any_goals exact β;
    · simp +decide only [sub_mul, Finset.sum_sub_distrib];
    · rw [ h_sum_prod_gibbs_pmf ] ; ring;
      norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ; ring;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h_sum_gibbs_pmf ] ; ring;
  · simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ]

/-- The annealed Gibbs average of the centered overlap square is `overlapVariance`. -/
lemma integral_centeredOverlapSq_eq_overlapVariance (t : ℝ) :
    (∫ w, gibbs_average_n_det (N := N) (n := 2)
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w) (centeredOverlapSq N q) ∂ℙ) =
      overlapVariance
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t := by
  rfl

/-
Gaussian integration by parts evaluates the raw smart-path pressure derivative.
-/
lemma pressure_derivative_ibp
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ w,
        fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H)
          (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
          (dH_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w)
        ∂ℙ) =
      (β ^ 2 / 4) * ((1 - q) ^ 2 -
        overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
  have := @SpinGlass.GeneralizedLatala.pressure_derivative_ibp_trace;
  rw [ this N β h q sk sim hIndep ht, MeasureTheory.integral_congr_ae ( Filter.Eventually.of_forall fun w => ?_ ) ];
  any_goals exact fun w => ( β ^ 2 / 4 ) * ( ( 1 - q ) ^ 2 - gibbs_average_n_det ( N := N ) ( n := 2 ) ( H_t N β h q sk sim t w ) ( centeredOverlapSq N q ) ) * 2;
  · rw [ MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul ];
    rw [ MeasureTheory.integral_sub ] <;> norm_num;
    · rw [ integral_centeredOverlapSq_eq_overlapVariance ] ; ring;
    · apply_rules [ SpinGlass.integrable_gibbs_average_n ];
  · grind +suggestions

/-- The ordinary Guerra smart-path sum-rule derivative.

The repository already provides the smart path and Hilbert-space Gaussian integration by parts.
This lemma records their specialization to the centered overlap square.
-/
lemma pressure_derivative
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
      ((β ^ 2 / 4) * ((1 - q) ^ 2 -
        overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t)) t := by
  rw [← pressure_derivative_ibp
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep ht]
  exact pressure_derivative_before_ibp
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) ht

/-! ## Coupled smart path and its characteristic

The lemmas in this section deliberately use `HasDerivAt`.  Thus the differential identities
also carry the regularity needed by the later chain-rule and endpoint arguments.
-/

/-- Differentiability of the coupled free energy in the coupling variable.

Proof route: for fixed disorder the partition sum is a finite sum of exponentials, so it is
smooth in `Λ`.  Differentiate the logarithm, identify the result as the tilted Gibbs expectation
of `N * Q₁₂² / 2`, and then differentiate under the disorder integral.  A uniform finite-volume
bound on `Q₁₂²` gives the required domination. -/
lemma coupledFreeEnergy_hasDerivAt_coupling
    (t Λ : ℝ) :
    HasDerivAt
      (fun L => coupledFreeEnergy
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t L)
      (deriv
        (fun L => coupledFreeEnergy
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t L) Λ) Λ := by
  sorry

/-- Gaussian IBP formula for the time derivative of the coupled free energy.

The witness `crossMoment` is the annealed four-replica square generated by the covariance
trace.  Its explicit finite-sum representation should be introduced in the proof, the IBP trace
expanded in the configuration basis, and its nonnegativity discharged pointwise as a square.

Use the same joint Gaussian model and the same call to
`gaussian_integration_by_parts_hilbert_cov_op` as in the ordinary pressure calculation.  Replace
`Φ` by the normalized logarithm of the coupled two-replica partition sum.  Its first derivative
is the tilted two-replica Gibbs average, while its second derivative is the corresponding Gibbs
covariance.  After applying `sk.cov_eq` and `sim.cov_eq`, introduce enough replicas to express
that covariance as the ordinary overlap term minus the nonnegative four-replica cross moment.
Finite configuration space again gives `ContDiff` and a constant moderate-growth bound for each
basis-direction test function. -/
lemma coupledFreeEnergy_hasDerivAt_time_ibp
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t Λ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ crossMoment : ℝ,
      0 ≤ crossMoment ∧
      HasDerivAt
        (fun s => coupledFreeEnergy
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) s Λ)
        ((β ^ 2 / 4) *
          ((1 - q) ^ 2 +
            4 * deriv
              (fun L => coupledFreeEnergy
                (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t L) Λ -
            2 * crossMoment)) t := by
  sorry

/-- The logarithmic quadratic moment is differentiable in the smart-path variable away from
the endpoints.

Proof route: subtract `pressure_derivative` from
`coupledFreeEnergy_hasDerivAt_time_ibp`, unfold `coupledExcess`, and rescale by `2N`.
The resulting derivative is retained existentially because only its inequality is used later. -/
lemma logQuadraticMoment_hasDerivAt_time
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t coupling : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ dt : ℝ,
      HasDerivAt
        (fun s => logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          s coupling) dt t := by
  sorry

/-- The logarithmic quadratic moment is differentiable in its coupling variable.

This is the rescaled coupling derivative from
`coupledFreeEnergy_hasDerivAt_coupling`. -/
lemma logQuadraticMoment_hasDerivAt_coupling
    (t coupling : ℝ) :
    HasDerivAt
      (fun c => logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t c)
      (deriv
        (fun c => logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          t c) coupling) coupling := by
  sorry

/-- The first-order differential inequality behind the moving-coupling estimate.

Proof route: combine the two preceding derivative lemmas with the coupled Gaussian-IBP
identity.  Drop the nonnegative cross moment, cancel the ordinary pressure derivative, and use
the standard tilted-moment estimate to bound the remaining covariance term by
`β² * logQuadraticMoment / (2 * coupling)`. -/
lemma logQuadraticMoment_differential_inequality
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t coupling : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hcoupling : 0 < coupling) :
    deriv
        (fun s => logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          s coupling) t -
        (β ^ 2 / 2) * deriv
          (fun c => logQuadraticMoment
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            t c) coupling
      ≤ (β ^ 2 / (2 * coupling)) *
          logQuadraticMoment
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
            t coupling := by
  sorry

/-- Coupling followed backwards from time `u` to the independent endpoint. -/
noncomputable def characteristicCoupling (coupling u s : ℝ) : ℝ :=
  coupling + (β ^ 2 / 2) * (u - s)

/-- The logarithmic moment restricted to the moving-coupling characteristic. -/
noncomputable def characteristicQuadraticMoment (coupling u s : ℝ) : ℝ :=
  logQuadraticMoment
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    s (characteristicCoupling β coupling u s)

/-- The moving coupling stays at least as large as its terminal value. -/
lemma characteristicCoupling_ge
    {coupling u s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) u) :
    coupling ≤ characteristicCoupling β coupling u s := by
  unfold characteristicCoupling
  have hus : 0 ≤ u - s := sub_nonneg.mpr hs.2
  nlinarith [sq_nonneg β]

/-- Chain rule and PDE inequality along the characteristic.

Proof route: obtain `HasDerivAt` in both variables, note that the coupling path has derivative
`-β² / 2`, and use `HasDerivAt.scomp` or the two-variable Fréchet chain rule.  Apply
`logQuadraticMoment_differential_inequality`; then use `characteristicCoupling_ge` and
nonnegativity of the logarithmic moment to replace the moving denominator by `coupling`. -/
lemma characteristicQuadraticMoment_differential_inequality
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {coupling u s : ℝ} (hcoupling : 0 < coupling)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) u) :
    ∃ d : ℝ,
      HasDerivAt
        (characteristicQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          coupling u) d s ∧
      d ≤ (β ^ 2 / (2 * coupling)) *
        characteristicQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          coupling u s := by
  sorry

/-- Continuity on the closed characteristic, including both endpoints.

Proof route: use the same dominated-convergence argument as
`interpolatedPressure_continuousOn`.  The finite replica sum is continuous jointly in time and
coupling.  On the compact characteristic its exponential tilt is uniformly bounded, which
provides an integrable disorder-independent dominator. -/
lemma characteristicQuadraticMoment_continuousOn
    {coupling u : ℝ} (hcoupling : 0 < coupling) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn
      (characteristicQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        coupling u) (Set.Icc (0 : ℝ) u) := by
  sorry

/-- One-dimensional integrating-factor estimate with explicit endpoint hypotheses.

Proof route: multiply `f` by `exp (-a * s)`, use the product rule to show that the result has
nonpositive derivative on `Ioo 0 u`, apply monotonicity on `Icc 0 u`, and rearrange. -/
lemma gronwall_le_endpoint
    {f : ℝ → ℝ} {a u : ℝ} (hu : 0 ≤ u)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) u))
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) u, ∃ d : ℝ,
      HasDerivAt f d s ∧ d ≤ a * f s) :
    f u ≤ Real.exp (a * u) * f 0 := by
  sorry

/-- Characteristic (Grönwall) estimate for the logarithmic quadratic moment.

This theorem is now only the assembly of the characteristic regularity, its differential
inequality, and the generic integrating-factor lemma. -/
lemma logQuadraticMoment_characteristic
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {coupling u : ℝ} (hcoupling : 0 < coupling)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        u coupling
      ≤ Real.exp (β ^ 2 * u / (2 * coupling)) *
        logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          0 ((2 * coupling + β ^ 2 * u) / 2) := by
  have hgronwall := gronwall_le_endpoint
    (f := characteristicQuadraticMoment
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      coupling u)
    (a := β ^ 2 / (2 * coupling)) hu.1
    (characteristicQuadraticMoment_continuousOn
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hcoupling hu)
    (fun s hs => characteristicQuadraticMoment_differential_inequality
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hIndep hcoupling hu hs)
  simp only [characteristicQuadraticMoment, characteristicCoupling] at hgronwall ⊢
  convert hgronwall using 1 <;> ring

/-- Positivity of the coupling scale in the improved region. -/
lemma lambdaStar_pos
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1) :
    0 < lambdaStar β q := by
  have hk : 0 < kappa q := kappa_pos hq0 hq1
  have hβ : β ^ 2 < (kappa q)⁻¹ := by
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hk).2 (by simpa [rho] using hρ)
  simp only [lambdaStar]
  linarith

/-- The parameter `rho` is nonnegative on the physical range of `q`. -/
lemma rho_nonneg
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ rho β q := by
  exact mul_nonneg (sq_nonneg β) (le_of_lt (kappa_pos hq0 hq1))

/-- The coupling scale written in terms of the distance to the boundary `rho = 1`. -/
lemma lambdaStar_eq_one_sub_rho_div
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    lambdaStar β q = (1 - rho β q) / (4 * kappa q) := by
  have hk0 : kappa q ≠ 0 := ne_of_gt (kappa_pos hq0 hq1)
  simp only [lambdaStar, rho]
  field_simp [hk0]

/-- Algebraic identity for the moving coupling used in the quadratic interpolation. -/
lemma kappa_mul_movingCoupling
    (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    kappa q * (2 * lambdaStar β q + β ^ 2 * t) =
      (1 - rho β q) / 2 + rho β q * t := by
  have hk0 : kappa q ≠ 0 := ne_of_gt (kappa_pos hq0 hq1)
  simp only [lambdaStar, rho]
  field_simp [hk0]
  ring

/-- The moving coupling remains in the range allowed by the endpoint estimate. -/
lemma movingCoupling_admissible
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    kappa q * (2 * lambdaStar β q + β ^ 2 * t) < 1 := by
  rw [kappa_mul_movingCoupling (β := β) (q := q) hq0 hq1]
  have hρ0 : 0 ≤ rho β q := rho_nonneg (β := β) (q := q) hq0 hq1
  have hmul : rho β q * t ≤ rho β q :=
    mul_le_of_le_one_right hρ0 ht.2
  linarith

/-- Quantitative slack in the endpoint admissibility inequality. -/
lemma movingCoupling_gap
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - rho β q) / 2 ≤
      1 - kappa q * (2 * lambdaStar β q + β ^ 2 * t) := by
  rw [kappa_mul_movingCoupling (β := β) (q := q) hq0 hq1]
  have hρ0 : 0 ≤ rho β q := rho_nonneg (β := β) (q := q) hq0 hq1
  have hmul : rho β q * t ≤ rho β q :=
    mul_le_of_le_one_right hρ0 ht.2
  linarith

/-- The moving coupling is strictly positive throughout the interpolation interval. -/
lemma movingCoupling_pos
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < 2 * lambdaStar β q + β ^ 2 * t := by
  have hlambda : 0 < lambdaStar β q :=
    lambdaStar_pos (β := β) (q := q) hq0 hq1 hρ
  have hβt : 0 ≤ β ^ 2 * t := mul_nonneg (sq_nonneg β) ht.1
  linarith

/-- Exact exponent appearing after applying Grönwall's inequality. -/
lemma beta_sq_div_two_lambdaStar
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1) :
    β ^ 2 / (2 * lambdaStar β q) =
      2 * rho β q / (1 - rho β q) := by
  have hk0 : kappa q ≠ 0 := ne_of_gt (kappa_pos hq0 hq1)
  have hgap0 : 1 - rho β q ≠ 0 := ne_of_gt (sub_pos.mpr hρ)
  rw [lambdaStar_eq_one_sub_rho_div (β := β) (q := q) hq0 hq1]
  simp only [rho]
  field_simp [hk0, hgap0]
  ring

/-- The explicit constant in the quadratic estimate is positive in the improved region. -/
lemma quadraticConstant_pos
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hρ : rho β q < 1) :
    0 < quadraticConstant β q := by
  have hρ0 : 0 ≤ rho β q := rho_nonneg (β := β) (q := q) hq0 hq1
  have hgap : 0 < 1 - rho β q := sub_pos.mpr hρ
  have hratio : 1 < 2 / (1 - rho β q) := by
    rw [lt_div_iff₀ hgap]
    linarith
  have hlog : 0 < Real.log (2 / (1 - rho β q)) := Real.log_pos hratio
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hlog

/-- Endpoint control for the moving coupling, already simplified to the uniform bound. -/
lemma endpoint_movingCoupling
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q) (hρ : rho β q < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        0 ((2 * lambdaStar β q + β ^ 2 * t) / 2)
      ≤ (1 / 2) * Real.log (2 / (1 - rho β q)) := by
  let Λ : ℝ := 2 * lambdaStar β q + β ^ 2 * t
  have hΛ0 : 0 ≤ Λ := le_of_lt
    (movingCoupling_pos (β := β) (q := q) hq0 hq1 hρ ht)
  have hΛ : kappa q * Λ < 1 :=
    movingCoupling_admissible (β := β) (q := q) hq0 hq1 hρ ht
  have hend := endpoint_quadratic
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hq0 hq1 hfp hΛ0 hΛ
  have hgap : (1 - rho β q) / 2 ≤ 1 - kappa q * Λ :=
    movingCoupling_gap (β := β) (q := q) hq0 hq1 ht
  have hdenom : 0 < 1 - kappa q * Λ := sub_pos.mpr hΛ
  have hρgap : 0 < 1 - rho β q := sub_pos.mpr hρ
  have hratio : 1 / (1 - kappa q * Λ) ≤ 2 / (1 - rho β q) := by
    rw [div_le_div_iff₀ hdenom hρgap]
    linarith
  have hlog :
      Real.log (1 / (1 - kappa q * Λ)) ≤
        Real.log (2 / (1 - rho β q)) := by
    exact Real.log_le_log (by positivity) hratio
  exact hend.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

/-- The moving-coupling estimate obtained by following the characteristic
`Λ(s) = 2 * coupling + β² * (t - s)` in the coupled interpolation. -/
lemma logQuadraticMoment_le_endpoint
    (hN : 0 < N)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {coupling t : ℝ} (hcoupling : 0 < coupling)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t coupling
      ≤ Real.exp (β ^ 2 * t / (2 * coupling)) *
        logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          0 ((2 * coupling + β ^ 2 * t) / 2) := by
  exact logQuadraticMoment_characteristic
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hIndep hcoupling ht

/-
Proposition `quadratic-estimate` from the blueprint.
-/
theorem uniform_quadratic_coupling
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q)
    (hρ : rho β q < 1)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    logQuadraticMoment
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        t (lambdaStar β q)
      ≤ quadraticConstant β q := by
  -- Apply the lemma `logQuadraticMoment_le_endpoint` with coupling `lambdaStar β q`.
  have h_logQuadraticMoment_le_endpoint : logQuadraticMoment N β h q sk sim t (lambdaStar β q) ≤ Real.exp (β ^ 2 * t / (2 * lambdaStar β q)) * logQuadraticMoment N β h q sk sim 0 ((2 * lambdaStar β q + β ^ 2 * t) / 2) := by
    apply logQuadraticMoment_le_endpoint;
    · exact hN;
    · exact hIndep;
    · exact lambdaStar_pos (β := β) (q := q) hq0 hq1 hρ
    · exact ht;
  have h_logQuadraticMoment_le_endpoint : logQuadraticMoment N β h q sk sim 0 ((2 * lambdaStar β q + β ^ 2 * t) / 2) ≤ (1 / 2) * Real.log (2 / (1 - rho β q)) := by
    apply_rules [ endpoint_movingCoupling ];
  refine' le_trans ‹_› ( le_trans ( mul_le_mul_of_nonneg_left h_logQuadraticMoment_le_endpoint ( Real.exp_nonneg _ ) ) _ );
  -- Simplify the exponent using the fact that `β^2 / (2 * lambdaStar β q) = 2 * rho β q / (1 - rho β q)`.
  have h_exp_simplified : Real.exp (β ^ 2 * t / (2 * lambdaStar β q)) ≤ Real.exp (2 * rho β q / (1 - rho β q)) := by
    have h_exp_bound : β ^ 2 / (2 * lambdaStar β q) = 2 * rho β q / (1 - rho β q) :=
      beta_sq_div_two_lambdaStar (β := β) (q := q) hq0 hq1 hρ
    exact Real.exp_le_exp.mpr ( by rw [ ← h_exp_bound ] ; exact div_le_div_of_nonneg_right ( mul_le_of_le_one_right ( sq_nonneg _ ) ht.2 ) ( mul_nonneg zero_le_two ( by exact le_of_lt ( lambdaStar_pos ( hq0 := hq0 ) ( hq1 := hq1 ) ( hρ := hρ ) ) ) ) );
  refine' le_trans ( mul_le_mul_of_nonneg_right h_exp_simplified ( mul_nonneg ( by norm_num ) ( Real.log_nonneg _ ) ) ) _;
  · rw [le_div_iff₀] <;>
      linarith [rho_nonneg (β := β) (q := q) hq0 hq1]
  · unfold quadraticConstant; ring_nf; norm_num;

/-! ## Consequences -/

/-
Integrated finite-volume Jensen inequality for the centered overlap square.
-/
lemma scaled_overlapVariance_le_logQuadraticMoment
    (coupling : ℝ) (hcoupling : 0 ≤ coupling) (t : ℝ) :
    coupling * (N : ℝ) *
        overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
      ≤ logQuadraticMoment
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
          t coupling := by
  refine' trans _ ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
  case refine'_2 => exact fun ω => coupling * N * gibbs_average_n_det N 2 ( H_t N β h q sk sim t ω ) ( centeredOverlapSq N q );
  · rw [ MeasureTheory.integral_const_mul ] ; rfl;
  · refine' Filter.Eventually.of_forall fun ω => mul_nonneg ( mul_nonneg hcoupling ( Nat.cast_nonneg _ ) ) _;
    refine' Finset.sum_nonneg fun σs _ => mul_nonneg _ _;
    · exact sq_nonneg _;
    · exact Finset.prod_nonneg fun _ _ => div_nonneg ( Real.exp_nonneg _ ) ( Z_pos _ _ |> le_of_lt );
  · have h_integrable : Integrable (fun ω => gibbs_average_n N β h q sk sim 2 t (fun σs => Real.exp (coupling * N * centeredOverlapSq N q σs)) ω) ℙ := by
      apply SpinGlass.integrable_gibbs_average_n;
    refine' h_integrable.mono' _ _;
    · exact Real.measurable_log.comp_aemeasurable h_integrable.aemeasurable |> fun h => h.aestronglyMeasurable;
    · filter_upwards [ ] with ω;
      rw [ Real.norm_eq_abs, abs_of_nonneg ( Real.log_nonneg _ ) ];
      · refine' le_trans ( Real.log_le_sub_one_of_pos _ ) _;
        · refine' Finset.sum_pos _ _;
          · intro σs _;
            refine' mul_pos ( Real.exp_pos _ ) ( Finset.prod_pos fun l _ => _ );
            exact div_pos ( Real.exp_pos _ ) ( Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ( Finset.univ_nonempty ) );
          · exact ⟨ fun _ => fun _ => Bool.true, Finset.mem_univ _ ⟩;
        · linarith;
      · have h_gibbs_exp : ∀ H : EnergySpace N, gibbs_average_n_det N 2 H (fun σs => Real.exp (coupling * N * centeredOverlapSq N q σs)) ≥ 1 := by
          intro H
          have h_gibbs_exp : gibbs_average_n_det N 2 H (fun σs => Real.exp (coupling * N * centeredOverlapSq N q σs)) ≥ Real.exp (gibbs_average_n_det N 2 H (fun σs => coupling * N * centeredOverlapSq N q σs)) := by
            apply gibbs_average_n_det_exp_jensen;
          refine' le_trans _ h_gibbs_exp;
          refine' Real.one_le_exp _;
          refine' Finset.sum_nonneg fun σs _ => mul_nonneg _ _;
          · exact mul_nonneg ( mul_nonneg hcoupling ( Nat.cast_nonneg _ ) ) ( sq_nonneg _ );
          · exact Finset.prod_nonneg fun _ _ => gibbs_pmf_nonneg N H _;
        exact h_gibbs_exp _;
  · filter_upwards [ ] with ω using scaled_centeredOverlapSq_le_log_gibbs_exp _ _ _ _

/-- Convexity of the log moment converts the quadratic exponential estimate into an overlap
second-moment estimate, uniformly along the smart path. -/
theorem overlap_concentration_uniform
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q)
    (hρ : rho β q < 1)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    overlapVariance
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
      ≤ quadraticConstant β q / (lambdaStar β q * (N : ℝ)) := by
  have hΛpos : 0 < lambdaStar β q := lambdaStar_pos (β := β) (q := q) hq0 hq1 hρ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hΛN : 0 < lambdaStar β q * (N : ℝ) := mul_pos hΛpos hNpos
  -- Apply the pointwise Jensen inequality and integrate
  have hiver : ∫ ω, lambdaStar β q * (N : ℝ) *
      (gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 t
        (centeredOverlapSq N q) ω) ∂ℙ ≤
      ∫ ω, Real.log (gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 t
        (fun σs => Real.exp (lambdaStar β q * (N : ℝ) * centeredOverlapSq N q σs)) ω) ∂ℙ := by
    apply integral_mono_ae
    · exact Integrable.const_mul
        (integrable_gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 t
          (centeredOverlapSq N q)) (lambdaStar β q * (N : ℝ))
    · let A := fun ω => gibbs_average_n (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 t
        (fun σs => Real.exp (lambdaStar β q * (N : ℝ) * centeredOverlapSq N q σs)) ω
      have hAint : Integrable A ℙ := integrable_gibbs_average_n
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 2 t
        (fun σs => Real.exp (lambdaStar β q * (N : ℝ) * centeredOverlapSq N q σs))
      have hAone : ∀ ω, 1 ≤ A ω := by
        intro ω
        simp only [A, gibbs_average_n, gibbs_average_n_det]
        rw [← sum_prod_gibbs_pmf_eq_one
          (N := N) (n := 2)
          (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)]
        apply Finset.sum_le_sum
        intro σs _
        have hexp : 1 ≤ Real.exp (lambdaStar β q * (N : ℝ) * centeredOverlapSq N q σs) :=
          Real.one_le_exp (mul_nonneg (le_of_lt hΛN) (sq_nonneg _))
        have hweight : 0 ≤ ∏ l, gibbs_pmf N
            (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
            (σs l) := by
          apply Finset.prod_nonneg
          intro l _
          exact gibbs_pmf_nonneg
            (N := N)
            (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω)
            (σ := σs l)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hweight
      apply hAint.mono'
      · exact (Real.measurable_log.comp_aemeasurable hAint.aemeasurable).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (hAone ω))]
        exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le (hAone ω))).trans
          (sub_le_self _ zero_le_one)
    · filter_upwards with ω
      simp only [gibbs_average_n]
      exact scaled_centeredOverlapSq_le_log_gibbs_exp (q := q) (H := H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ω) (coupling := lambdaStar β q)
  -- Relate hiver to overlapVariance
  have h1 : lambdaStar β q * (N : ℝ) * overlapVariance (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
      ≤ logQuadraticMoment (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t (lambdaStar β q) := by
    simp only [overlapVariance, logQuadraticMoment, nu]
    rw [← MeasureTheory.integral_const_mul]
    exact hiver
  -- Use uniform_quadratic_coupling
  have h2 : logQuadraticMoment (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t (lambdaStar β q) ≤ quadraticConstant β q :=
    uniform_quadratic_coupling (hN := hN) (hq0 := hq0) (hq1 := hq1)
      (hfp := hfp) (hρ := hρ) (hIndep := hIndep) (ht := ht)
  -- Combine and divide
  have h3 : lambdaStar β q * (N : ℝ) * overlapVariance (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ≤ quadraticConstant β q := h1.trans h2
  rw [mul_comm] at h3
  exact (le_div_iff₀ hΛN).mpr h3

private lemma overlapVariance_continuous : Continuous (overlapVariance
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)) := by
  let f : ReplicaFun N 2 := centeredOverlapSq N q
  let B : ℝ := ∑ σs : ReplicaSpace N 2, ‖f σs‖
  rw [continuous_iff_continuousAt]
  intro t
  apply MeasureTheory.continuousAt_of_dominated
  · filter_upwards with s
    exact (integrable_gibbs_average_n
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      (n := 2) (t := s) (f := f)).aestronglyMeasurable
  · filter_upwards with s
    filter_upwards with w
    simpa [B, Real.norm_eq_abs] using
      (abs_gibbs_average_n_le
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        (n := 2) (t := s) (f := f) w)
  · exact integrable_const B
  · filter_upwards with w
    have hHt : Continuous (fun t =>
        H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      simp only [H_t, H_gauss]
      fun_prop
    have hg : Continuous (fun H : EnergySpace N =>
        gibbs_average_n_det (N := N) (n := 2) H f) := by
      simp only [gibbs_average_n_det]
      apply continuous_finset_sum
      intro σs _
      apply Continuous.mul continuous_const
      apply continuous_finset_prod
      intro l _
      exact (SpinGlass.contDiff_gibbs_pmf (N := N) (σ := σs l)).continuous
    exact (hg.comp hHt).continuousAt

private lemma free_energy_siteEnergy_eq (N : ℕ) (a : Fin N → ℝ) :
    free_energy_density (N := N) (siteEnergy N a) =
      (1 / (N : ℝ)) * ∑ i : Fin N, (Real.log 2 + Real.log (Real.cosh (a i))) := by
  rw [free_energy_density, Z_siteEnergy]
  rw [Real.log_prod]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show (∑ b : Bool, Real.exp (-(a i * boolSpin b))) =
        2 * Real.cosh (a i) by
      simp [boolSpin, Real.cosh_eq]
      ring]
    rw [Real.log_mul]
    · norm_num
    · exact ne_of_gt (Real.cosh_pos _)
  · intro i _
    exact ne_of_gt (Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty)

private lemma integrable_log_cosh_affine (h a : ℝ) : Integrable
    (fun z => Real.log (Real.cosh (h + a * z))) (gaussianReal 0 1) := by
  have hplus : Integrable (fun z => Real.exp (h + a * z)) (gaussianReal 0 1) := by
    simpa [Real.exp_add] using
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a).const_mul
        (Real.exp h)
  have hminus : Integrable (fun z => Real.exp (-(h + a * z))) (gaussianReal 0 1) := by
    have hi :=
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-a)).const_mul
        (Real.exp (-h))
    simpa [Real.exp_add, mul_comm] using hi
  have hbound : Integrable
      (fun z => Real.exp (h + a * z) + Real.exp (-(h + a * z)))
      (gaussianReal 0 1) := hplus.add hminus
  apply hbound.mono'
  · have hc : Continuous (fun z => Real.cosh (h + a * z)) := by fun_prop
    exact (hc.log (fun z => ne_of_gt (Real.cosh_pos _))).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh _))]
    calc
      Real.log (Real.cosh (h + a * z))
          ≤ Real.cosh (h + a * z) - 1 :=
        Real.log_le_sub_one_of_pos (Real.cosh_pos _)
      _ ≤ Real.exp (h + a * z) + Real.exp (-(h + a * z)) := by
        rw [Real.cosh_eq]
        nlinarith [Real.exp_pos (h + a * z), Real.exp_pos (-(h + a * z))]

private lemma endpoint_pressure
    (hN : 0 < N) (hq0 : 0 ≤ q) :
    interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 =
      Real.log 2 + standardGaussianExpectation
        (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) := by
  letI : IsProbabilityMeasure (gaussianProduct N) := by
    rw [gaussianProduct]
    infer_instance
  let F : EnergySpace N → ℝ := fun H =>
    free_energy_density (N := N) (H + H_field (N := N) (h := h))
  have hFcont : Continuous F :=
    (SpinGlass.contDiff_free_energy_density (N := N)).continuous.comp
      (continuous_id.add continuous_const)
  have hHt0 (ω : Ω) :
      H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 ω =
        sim.V ω + H_field (N := N) (h := h) := by
    simp [H_t, H_gauss]
  have hrefLaw := referenceField_hasGaussianLaw N β q
  calc
    interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 0 =
        ∫ ω, F (sim.V ω) ∂ℙ := by
          rw [interpolatedPressure]
          apply integral_congr_ae
          filter_upwards with ω
          rw [hHt0]
    _ = ∫ H, F H ∂Measure.map sim.V ℙ := by
          rw [integral_map sim.hV.repr_measurable.aemeasurable
            hFcont.aestronglyMeasurable]
    _ = ∫ H, F H ∂Measure.map (referenceField N β q) (gaussianProduct N) := by
          rw [simpleDisorder_law_eq_reference N β q sim hN hq0]
    _ = ∫ z, F (referenceField N β q z) ∂gaussianProduct N := by
          rw [integral_map hrefLaw.aemeasurable hFcont.aestronglyMeasurable]
    _ = Real.log 2 + standardGaussianExpectation
        (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) := by
      let g : ℝ → ℝ := fun z =>
        Real.log (Real.cosh (h + β * Real.sqrt q * z))
      have hg : Integrable g (gaussianReal 0 1) :=
        integrable_log_cosh_affine h (β * Real.sqrt q)
      have hcoord (i : Fin N) : Integrable (fun z : Fin N → ℝ => g (z i))
          (gaussianProduct N) := by
        exact ((measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).integrable_comp
          hg.aestronglyMeasurable).2 hg
      rw [show (∫ z, F (referenceField N β q z) ∂gaussianProduct N) =
          ∫ z, (1 / (N : ℝ)) * ∑ i : Fin N, (Real.log 2 + g (z i))
            ∂gaussianProduct N by
        apply integral_congr_ae
        filter_upwards with z
        simp only [F]
        change free_energy_density (N := N)
          (referenceField N β q z + magnetic_field_vector (N := N) h) = _
        rw [reference_add_field_eq_siteEnergy, free_energy_siteEnergy_eq]]
      rw [integral_const_mul]
      rw [show (∫ z : Fin N → ℝ, ∑ i : Fin N, (Real.log 2 + g (z i))
            ∂gaussianProduct N) =
          ∫ z : Fin N → ℝ, ((N : ℝ) * Real.log 2 + ∑ i : Fin N, g (z i))
            ∂gaussianProduct N by
        apply integral_congr_ae
        filter_upwards with z
        simp [Finset.sum_add_distrib]]
      rw [integral_add (integrable_const _)
        (integrable_finset_sum Finset.univ (fun i _ => hcoord i))]
      rw [integral_finset_sum Finset.univ (fun i _ => hcoord i)]
      simp only [integral_const, probReal_univ, one_smul]
      have hcoord_integral (i : Fin N) :
          (∫ z : Fin N → ℝ, g (z i) ∂gaussianProduct N) =
            ∫ z, g z ∂gaussianReal 0 1 :=
        integral_comp_eval hg.aestronglyMeasurable
      simp_rw [hcoord_integral]
      simp only [standardGaussianExpectation, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp
      ring

private lemma interpolatedPressure_continuousOn :
    ContinuousOn
      (interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
      (Set.Icc (0 : ℝ) 1) := by
  let C : ℝ := (SpinGlass.hasModerateGrowth_free_energy_density N).C
  let B : Ω → ℝ := fun w => C *
    (1 + ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖)
  apply MeasureTheory.continuousOn_of_dominated
  · intro t _
    have hHt_meas : Measurable
        (H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) := by
      have hU := sk.hU.repr_measurable.const_smul (Real.sqrt t)
      have hV := sim.hV.repr_measurable.const_smul (Real.sqrt (1 - t))
      simpa [H_t, H_gauss] using (hU.add hV).add measurable_const
    exact ((SpinGlass.contDiff_free_energy_density (N := N)).continuous.measurable.comp
      hHt_meas).aestronglyMeasurable
  · intro t ht
    filter_upwards with w
    have hsqrtt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
    have hsqrtt1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht.2
    have hsqrt1t0 : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
    have hsqrt1t1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [ht.1])
    have hnorm : ‖H_t
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w‖ ≤
        ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
      calc
        ‖H_t (N := N) (β := β) (h := h) (q := q)
            (sk := sk) (sim := sim) t w‖
            ≤ ‖(Real.sqrt t) • sk.U w‖ + ‖(Real.sqrt (1 - t)) • sim.V w‖ +
                ‖H_field (N := N) (h := h)‖ := by
              simp only [H_t, H_gauss]
              exact (norm_add_le
                ((Real.sqrt t) • sk.U w + (Real.sqrt (1 - t)) • sim.V w)
                (H_field (N := N) (h := h))).trans
                (by
                  gcongr
                  exact norm_add_le ((Real.sqrt t) • sk.U w)
                    ((Real.sqrt (1 - t)) • sim.V w))
        _ ≤ ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg hsqrtt0, abs_of_nonneg hsqrt1t0]
              gcongr
              · exact mul_le_of_le_one_left (norm_nonneg _) hsqrtt1
              · exact mul_le_of_le_one_left (norm_nonneg _) hsqrt1t1
    have hgrowth :=
      (SpinGlass.hasModerateGrowth_free_energy_density N).F_bound
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w)
    have hm : (SpinGlass.hasModerateGrowth_free_energy_density N).m = 1 := by rfl
    rw [hm, pow_one] at hgrowth
    change |free_energy_density (N := N)
        (H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w)| ≤
      C * (1 + ‖H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w‖) at hgrowth
    have hinside :
        1 + ‖H_t (N := N) (β := β) (h := h) (q := q)
          (sk := sk) (sim := sim) t w‖ ≤
        1 + ‖sk.U w‖ + ‖sim.V w‖ + ‖H_field (N := N) (h := h)‖ := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hinside
      (le_of_lt (SpinGlass.hasModerateGrowth_free_energy_density N).Cpos)
    rw [Real.norm_eq_abs]
    exact hgrowth.trans (by simpa only [C] using hmul)
  · dsimp only [B]
    apply Integrable.const_mul
    exact (((integrable_const (1 : ℝ)).add
      (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sk.U) sk.hU)).add
      (PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian (g := sim.V) sim.hV)).add
        (integrable_const _)
  · filter_upwards with w
    have hHt : Continuous (fun t =>
        H_t (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t w) := by
      simp only [H_t, H_gauss]
      fun_prop
    exact ((SpinGlass.contDiff_free_energy_density (N := N)).continuous.comp hHt).continuousOn

/-- Integrated Guerra sum rule, including evaluation of the independent endpoint. -/
lemma replica_symmetric_sum_rule
    (hN : 0 < N) (hq0 : 0 ≤ q)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) :
    MeasureTheory.IntegrableOn
        (overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim))
        (Set.Icc (0 : ℝ) 1) (MeasureTheory.volume : Measure ℝ) ∧
      rsPressure β h q -
          interpolatedPressure
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1
        = (β ^ 2 / 4) *
            ∫ t in Set.Icc (0 : ℝ) 1,
              overlapVariance
                (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t := by
  let P : ℝ → ℝ := interpolatedPressure
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  let v : ℝ → ℝ := overlapVariance
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  let g : ℝ → ℝ := fun t => (β ^ 2 / 4) * ((1 - q) ^ 2 - v t)
  have hvcont : Continuous v := overlapVariance_continuous
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hvint : IntegrableOn v (Set.Icc (0 : ℝ) 1) := hvcont.integrableOn_Icc
  have hgcont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hPcont : ContinuousOn P (Set.Icc (0 : ℝ) 1) :=
    interpolatedPressure_continuousOn
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt P (g t) t := by
    intro t ht
    exact pressure_derivative
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hIndep ht
  have hFTC : (∫ t in (0 : ℝ)..1, g t) = P 1 - P 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hPcont
      hderiv (hgcont.intervalIntegrable 0 1)
  have hinterval :
      (∫ t in (0 : ℝ)..1, g t) =
        (β ^ 2 / 4) * ((1 - q) ^ 2 - ∫ t in (0 : ℝ)..1, v t) := by
    simp only [g]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 - q) ^ 2) volume 0 1)
      (hvcont.intervalIntegrable 0 1)]
    norm_num
  have hset :
      (∫ t in Set.Icc (0 : ℝ) 1, v t) = ∫ t in (0 : ℝ)..1, v t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le zero_le_one]
  have hP0 : P 0 = Real.log 2 + standardGaussianExpectation
      (fun z => Real.log (Real.cosh (h + β * Real.sqrt q * z))) :=
    endpoint_pressure
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) hN hq0
  have hrel : P 1 - P 0 =
      (β ^ 2 / 4) * ((1 - q) ^ 2 - ∫ t in (0 : ℝ)..1, v t) :=
    hFTC.symm.trans hinterval
  refine ⟨hvint, ?_⟩
  rw [rsPressure, show interpolatedPressure
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1 = P 1 by rfl,
    hset, ← hP0]
  linear_combination -hrel

/-- Generalized Latała bound for the finite-volume SK model.

At `t = 1`, `H_t` is the SK disorder plus the external-field vector.  The theorem gives both
the `O(1/N)` centered-overlap estimate and the corresponding replica-symmetric pressure error.
-/
theorem generalized_latala
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q)
    (hρ : rho β q < 1)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) :
    overlapVariance
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1
        ≤ quadraticConstant β q / (lambdaStar β q * (N : ℝ)) ∧
      0 ≤ rsPressure β h q -
        interpolatedPressure
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1 ∧
      rsPressure β h q -
        interpolatedPressure
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1
        ≤ (β ^ 2 * quadraticConstant β q) /
            (4 * lambdaStar β q * (N : ℝ)) := by
  let C : ℝ := quadraticConstant β q / (lambdaStar β q * (N : ℝ))
  have hoverlap :=
    overlap_concentration_uniform
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hq0 hq1 hfp hρ hIndep (t := (1 : ℝ)) (by simp)
  have hsum :=
    replica_symmetric_sum_rule
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
      hN hq0 hIndep
  have hvar0 : ∀ t : ℝ, 0 ≤ overlapVariance
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t :=
    fun t => overlapVariance_nonneg
      (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
  have hint0 : 0 ≤ ∫ t in Set.Icc (0 : ℝ) 1,
      overlapVariance
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t :=
    integral_nonneg hvar0
  have hpressure0 : 0 ≤ rsPressure β h q -
      interpolatedPressure
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1 := by
    rw [hsum.2]
    exact mul_nonneg (div_nonneg (sq_nonneg β) (by norm_num)) hint0
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      overlapVariance
          (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t ≤ C := by
    intro t ht
    simpa [C] using
      overlap_concentration_uniform
        (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
        hN hq0 hq1 hfp hρ hIndep ht
  have hconstInt : MeasureTheory.IntegrableOn
      (fun _ : ℝ => C) (Set.Icc (0 : ℝ) 1) (MeasureTheory.volume : Measure ℝ) :=
    MeasureTheory.integrableOn_const (hs := by
      rw [Real.volume_Icc]
      finiteness)
  have hint_le :
      (∫ t in Set.Icc (0 : ℝ) 1,
          overlapVariance
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t) ≤ C := by
    calc
      (∫ t in Set.Icc (0 : ℝ) 1,
          overlapVariance
            (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t)
          ≤ ∫ _t in Set.Icc (0 : ℝ) 1, C := by
              exact integral_mono_ae hsum.1 hconstInt
                (ae_restrict_of_forall_mem measurableSet_Icc hbound)
      _ = C := by
        norm_num [MeasureTheory.integral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  refine ⟨hoverlap, hpressure0, ?_⟩
  rw [hsum.2]
  calc
    (β ^ 2 / 4) *
          ∫ t in Set.Icc (0 : ℝ) 1,
            overlapVariance
              (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) t
        ≤ (β ^ 2 / 4) * C :=
          mul_le_mul_of_nonneg_left hint_le (div_nonneg (sq_nonneg β) (by norm_num))
    _ = (β ^ 2 * quadraticConstant β q) /
          (4 * lambdaStar β q * (N : ℝ)) := by
      simp only [C]
      ring

end GeneralizedLatala
end SpinGlass
