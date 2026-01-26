
import Mathlib

/-!
Blueprint

We work with the standard Gaussian density on `ℝ`.

Definitions:
* `phi u`   : density `φ(u) = exp(-u^2/2) / sqrt(2π)`.
* `PhiC u`  : upper tail `Φc(u) = ∫_{t ≥ u} φ(t) dt`.
* `millsInv u` : inverse Mills ratio `E(u) = φ(u) / Φc(u)`.

Target inequalities:
* For `u > 0`, a two-sided Mills inequality
    `u ≤ E(u)` and `E(u) ≤ u + 1/u`.
* A global growth bound with an explicit constant `C`:
    `0 < E(u)` and `E(u) ≤ max u 0 + C` for all `u`.

Notes:
* The measure-theoretic and integration-by-parts steps use Mathlib's
  `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` from `IntegralEqImproper`.
* The constant is chosen as `max (1 / PhiC 1) 1` for convenience.
-/

open scoped BigOperators
open scoped Topology
open MeasureTheory

namespace Mills

noncomputable section

/-- Standard Gaussian density. -/
def phi (u : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(u ^ 2) / 2)

/-- Upper tail of the standard Gaussian, `Φc u = ∫_{u}^{∞} φ(t) dt`.

We implement this as a set integral over `[u,∞)`.
-/
def PhiC (u : ℝ) : ℝ :=
  ∫ t in Set.Ici u, phi t

/-- Inverse Mills ratio `E u = φ(u) / Φc(u)`. -/
def millsInv (u : ℝ) : ℝ :=
  phi u / PhiC u

/-- A convenient constant for the global growth bound. -/
def C : ℝ := max (1 / PhiC 1) 1

lemma C_pos : 0 < C := by
  have h1 : (1 : ℝ) ≤ C := by
    simp [C]
  linarith

private lemma PhiC_eq_integral_Ioi (u : ℝ) : PhiC u = ∫ t in Set.Ioi u, phi t := by
  simpa [PhiC] using
    (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := (volume : Measure ℝ))
      (f := phi) (x := u))

/-
Auxiliary facts about `phi`.
-/

private lemma integrable_phi : Integrable phi := by
  have h : Integrable (fun x : ℝ => Real.exp (-((1 / 2 : ℝ) * x ^ 2))) := by
    simpa using (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num))
  have h' : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
    have :
        (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) =
          (fun x : ℝ => Real.exp (-((1 / 2 : ℝ) * x ^ 2))) := by
      funext x
      ring_nf
    simpa [this] using h
  change Integrable (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2))
  exact h'.const_mul (1 / Real.sqrt (2 * Real.pi))

private lemma continuous_phi : Continuous phi := by
  change Continuous (fun u : ℝ => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(u ^ 2) / 2))
  have h_inner : Continuous (fun u : ℝ => -(u ^ 2) / (2 : ℝ)) := by
    have h_pow : Continuous (fun u : ℝ => u ^ 2) := by
      simpa using (continuous_pow 2 : Continuous fun u : ℝ => u ^ 2)
    simpa [div_eq_mul_inv, mul_assoc] using (h_pow.neg.div_const (2 : ℝ))
  have h_exp : Continuous (fun u : ℝ => Real.exp (-(u ^ 2) / (2 : ℝ))) := Real.continuous_exp.comp h_inner
  have h_const : Continuous (fun _u : ℝ => (1 / Real.sqrt (2 * Real.pi))) := continuous_const
  simpa [div_eq_mul_inv, mul_assoc] using h_const.mul h_exp

lemma phi_pos (u : ℝ) : 0 < phi u := by
  have hconst : 0 < (1 / Real.sqrt (2 * Real.pi) : ℝ) := by
    have hpi : (0 : ℝ) < Real.pi := by simpa using Real.pi_pos
    have h2pi : (0 : ℝ) < (2 * Real.pi : ℝ) := by nlinarith
    have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 h2pi
    simpa [one_div] using inv_pos.2 hsqrt
  have hexp : 0 < Real.exp (-(u ^ 2) / 2) := Real.exp_pos _
  have : 0 < (1 / Real.sqrt (2 * Real.pi) : ℝ) * Real.exp (-(u ^ 2) / 2) := by
    exact mul_pos hconst hexp
  simpa [phi] using this

lemma phi_nonneg (u : ℝ) : 0 ≤ phi u := (le_of_lt (phi_pos u))

/-
Auxiliary facts about the tail integral `PhiC`.
-/

/-- Positivity of the Gaussian upper tail. -/
lemma PhiC_pos (u : ℝ) : 0 < PhiC u := by
  have hab : u < u + 1 := by linarith
  have hfi : IntervalIntegrable phi volume u (u + 1) := by
    simpa using (integrable_phi.intervalIntegrable)
  have hpos_interval :
      0 < ∫ x : ℝ in u..(u + 1), phi x := by
    exact
      intervalIntegral.intervalIntegral_pos_of_pos
        (f := phi) (a := u) (b := u + 1) hfi (fun x => phi_pos x) hab
  have hIoc :
      (∫ x in Set.Ioc u (u + 1), phi x) = ∫ x : ℝ in u..(u + 1), phi x := by
    simpa using
      (intervalIntegral.integral_of_le (μ := volume) (f := phi) (a := u) (b := u + 1) hab.le).symm
  have hpos_Ioc : 0 < ∫ x in Set.Ioc u (u + 1), phi x := by
    simpa [hIoc] using hpos_interval
  have hmono : (∫ x in Set.Ioc u (u + 1), phi x) ≤ ∫ x in Set.Ici u, phi x := by
    have hfi_on : IntegrableOn phi (Set.Ici u) (volume : Measure ℝ) := integrable_phi.integrableOn
    have h_nonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ici u)] phi := by
      refine ae_of_all _ (fun x => (phi_pos x).le)
    have hst : (Set.Ioc u (u + 1) : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Ici u := by
      refine ae_of_all _ (fun x hx => le_of_lt hx.1)
    exact setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := phi)
      (s := Set.Ioc u (u + 1)) (t := Set.Ici u) hfi_on h_nonneg hst
  simpa [PhiC] using lt_of_lt_of_le hpos_Ioc hmono

lemma millsInv_pos (u : ℝ) : 0 < millsInv u := by
  have h1 : 0 < phi u := phi_pos u
  have h2 : 0 < PhiC u := PhiC_pos u
  exact div_pos h1 h2

/-- Monotonicity of the tail: `PhiC` is antitone. -/
lemma PhiC_antitone : Antitone PhiC := by
  intro u v huv
  simp only [PhiC]
  have hfi : IntegrableOn phi (Set.Ici u) (volume : Measure ℝ) := integrable_phi.integrableOn
  have h_nonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ici u)] phi := by
    refine ae_of_all _ (fun x => (phi_pos x).le)
  have hst : (Set.Ici v : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Ici u := by
    refine ae_of_all _ (fun x hx => le_trans huv hx)
  exact setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := phi)
    (s := Set.Ici v) (t := Set.Ici u) hfi h_nonneg hst

/-- A coarse bound `phi u ≤ 1` used for `u ≤ 1`. -/
lemma phi_le_one (u : ℝ) : phi u ≤ 1 := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    simpa using (Real.one_le_sqrt.2 h2pi)
  have hconst : (1 / Real.sqrt (2 * Real.pi) : ℝ) ≤ 1 := by
    have : (1 : ℝ) / Real.sqrt (2 * Real.pi) ≤ (1 : ℝ) / (1 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hsqrt
    simpa using this
  have hexp : Real.exp (-(u ^ 2) / 2) ≤ 1 := by
    have : (-(u ^ 2) / 2 : ℝ) ≤ 0 := by nlinarith [sq_nonneg u]
    simpa [Real.exp_le_one_iff] using this
  unfold phi
  have hnonneg : 0 ≤ (Real.exp (-(u ^ 2) / 2) : ℝ) := Real.exp_nonneg _
  have hmul := mul_le_mul hconst hexp hnonneg (by linarith)
  simpa [one_mul] using hmul

/-
Local bounds for `millsInv`.
-/

/-- For `u ≤ 1`, we can bound `E(u)` by `1 / Φc(1)`. -/
lemma millsInv_le_one_div_PhiC_one {u : ℝ} (hu : u ≤ 1) :
    millsInv u ≤ 1 / PhiC 1 := by
  have hphi : phi u ≤ 1 := phi_le_one u
  have hPhiC : PhiC 1 ≤ PhiC u := PhiC_antitone hu
  have hPhiC_pos : 0 < PhiC u := PhiC_pos u
  have hPhiC1_pos : 0 < PhiC 1 := PhiC_pos 1
  calc
    millsInv u = phi u / PhiC u := rfl
    _ ≤ 1 / PhiC u := by
        exact div_le_div_of_nonneg_right hphi hPhiC_pos.le
    _ ≤ 1 / PhiC 1 := by
        exact one_div_le_one_div_of_le hPhiC1_pos hPhiC

/-- Convenience estimate: `1 / Φc(1) ≤ C` for the chosen constant `C`. -/
lemma one_div_PhiC_one_le_C : 1 / PhiC 1 ≤ C := by
  simpa [C] using (le_max_left (1 / PhiC 1) 1)

/-- For `u ≤ 1`, the inverse Mills ratio is bounded by `C`. -/
lemma millsInv_le_C_of_le_one {u : ℝ} (hu : u ≤ 1) : millsInv u ≤ C := by
  have h1 : millsInv u ≤ 1 / PhiC 1 := millsInv_le_one_div_PhiC_one (u := u) hu
  exact le_trans h1 one_div_PhiC_one_le_C

/-
Integration by parts for Mills ratio estimate using Mathlib's `integral_Ioi_mul_deriv_eq_deriv_mul`.
-/

private lemma deriv_phi (u : ℝ) : deriv phi u = -u * phi u := by
  have h_inner : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-u) u := by
    have h_pow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
      simpa using (hasDerivAt_pow (n := 2) (x := u))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (h_pow.neg.div_const (2 : ℝ))
  have h_exp :
      HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2))
        (-(u * Real.exp (-(u ^ 2) / 2))) u := by
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (x := (-(u ^ 2) / 2))).comp u h_inner
  have h_mul :
      HasDerivAt
        (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2))
        ((1 / Real.sqrt (2 * Real.pi)) * (-(u * Real.exp (-(u ^ 2) / 2)))) u :=
    h_exp.const_mul (1 / Real.sqrt (2 * Real.pi))
  change
      deriv (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2)) u =
        -u * ((1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(u ^ 2) / 2))
  have hderiv :
      deriv (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2)) u =
        (1 / Real.sqrt (2 * Real.pi)) * (-(u * Real.exp (-(u ^ 2) / 2))) := h_mul.deriv
  rw [hderiv]
  ring_nf

private lemma hasDerivAt_phi (u : ℝ) : HasDerivAt phi (-u * phi u) u := by
  have hd := deriv_phi u
  have hdiff : DifferentiableAt ℝ phi u := by
    change DifferentiableAt ℝ
        (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2)) u
    fun_prop
  rw [← hd]
  exact hdiff.hasDerivAt

private lemma tendsto_phi_atTop_zero :
    Filter.Tendsto (fun x : ℝ => phi x) Filter.atTop (nhds (0 : ℝ)) := by
  have hsq : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)
  have hneg : Filter.Tendsto (fun x : ℝ => -(x ^ 2)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hsq
  have hdiv : Filter.Tendsto (fun x : ℝ => -(x ^ 2) / 2) Filter.atTop Filter.atBot := by
    simpa using hneg.atBot_div_const (by norm_num : (0 : ℝ) < 2)
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) Filter.atTop (nhds (0 : ℝ)) := by
    exact Real.tendsto_exp_atBot.comp hdiv
  have hconst :
      Filter.Tendsto (fun _x : ℝ => (1 / Real.sqrt (2 * Real.pi))) Filter.atTop
        (nhds (1 / Real.sqrt (2 * Real.pi))) :=
    tendsto_const_nhds
  have hprod := hconst.mul hexp
  simpa [phi] using hprod

/-- Integration by parts identity used in the Mills ratio estimate.

For `u > 0`:
`Φc(u) = φ(u)/u - ∫_{t ≥ u} φ(t)/t^2 dt`.

This uses Mathlib's `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`.
-/
lemma PhiC_eq_phi_div_sub_integral (u : ℝ) (hu : 0 < u) :
    PhiC u = phi u / u - ∫ t in Set.Ici u, phi t / (t ^ 2) := by
  -- We use integration by parts: ∫ u' v = [u v]_u^∞ - ∫ u v'
  -- With u(x) = -φ(x), v(x) = 1/x
  -- u'(x) = x φ(x), v'(x) = -1/x²
  have hφderiv : ∀ x, HasDerivAt phi (-x * phi x) x := hasDerivAt_phi
  have hu_deriv :
      ∀ x ∈ Set.Ioi u, HasDerivAt (fun y : ℝ => -phi y) (x * phi x) x := by
    intro x hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hφderiv x).neg
  have hv_deriv :
      ∀ x ∈ Set.Ioi u, HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := by
    intro x hx
    have hxpos : 0 < x := lt_trans hu (by simpa [Set.mem_Ioi] using hx)
    simpa using hasDerivAt_inv (ne_of_gt hxpos)

  have hφ_int : Integrable (fun x : ℝ => phi x) (volume.restrict (Set.Ioi u)) := by
    simpa [IntegrableOn] using (integrable_phi.integrableOn (s := Set.Ioi u))

  have hu'v_int : IntegrableOn (fun x : ℝ => (x * phi x) * x⁻¹) (Set.Ioi u) := by
    have hEq :
        (fun x : ℝ => (x * phi x) * x⁻¹) =ᵐ[volume.restrict (Set.Ioi u)]
          fun x => phi x := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 ?_
      refine ae_of_all _ (fun x hx => ?_)
      have hxpos : 0 < x := lt_trans hu (by simpa [Set.mem_Ioi] using hx)
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      simp [mul_assoc, mul_left_comm, mul_comm, hx0]
    exact hφ_int.congr hEq.symm

  have huv'_int : IntegrableOn (fun x : ℝ => (-phi x) * (-(x ^ 2)⁻¹)) (Set.Ioi u) := by
    have hdom :
        Integrable (fun x : ℝ => (1 / u ^ 2) * phi x) (volume.restrict (Set.Ioi u)) := by
      exact hφ_int.const_mul (1 / u ^ 2)
    have hmeas :
        AEStronglyMeasurable (fun x : ℝ => (-phi x) * (-(x ^ 2)⁻¹))
          (volume.restrict (Set.Ioi u)) := by
      have : Measurable (fun x : ℝ => (-phi x) * (-(x ^ 2)⁻¹)) := by
        have hφm : Measurable (fun x : ℝ => phi x) := continuous_phi.measurable
        have hx2 : Measurable (fun x : ℝ => x ^ 2) := (measurable_id.pow_const (2 : ℕ))
        exact hφm.neg.mul (hx2.inv.neg)
      exact this.aestronglyMeasurable
    have hbound :
        ∀ᵐ x ∂(volume.restrict (Set.Ioi u)),
          ‖(-phi x) * (-(x ^ 2)⁻¹)‖ ≤ ‖(1 / u ^ 2) * phi x‖ := by
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
      have : |phi x| * (x ^ 2)⁻¹ ≤ (u ^ 2)⁻¹ * |phi x| := by
        calc
          |phi x| * (x ^ 2)⁻¹ ≤ |phi x| * (u ^ 2)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv (abs_nonneg (phi x))
          _ = (u ^ 2)⁻¹ * |phi x| := by
            simpa [mul_comm]
      simpa [Real.norm_eq_abs, abs_mul, one_div, mul_assoc, mul_left_comm, mul_comm] using this
    exact hdom.mono hmeas hbound

  have h_zero :
      Filter.Tendsto (fun x : ℝ => (-phi x) * x⁻¹)
        (nhdsWithin u (Set.Ioi u)) (nhds ((-phi u) * u⁻¹)) := by
    have hcont : ContinuousAt (fun x : ℝ => (-phi x) * x⁻¹) u := by
      have hφc : ContinuousAt (fun x : ℝ => -phi x) u := continuous_phi.continuousAt.neg
      have hinv : ContinuousAt (fun x : ℝ => x⁻¹) u :=
        ContinuousInv₀.continuousAt_inv₀ (ne_of_gt hu)
      simpa [mul_assoc] using hφc.mul hinv
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

  have h_infty :
      Filter.Tendsto (fun x : ℝ => (-phi x) * x⁻¹) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_phi_atTop_zero.neg.mul tendsto_inv_atTop_zero)

  have hibp :=
    MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := u)
      (u := fun x : ℝ => -phi x) (u' := fun x : ℝ => x * phi x)
      (v := fun x : ℝ => x⁻¹) (v' := fun x : ℝ => -(x ^ 2)⁻¹)
      (a' := (-phi u) * u⁻¹) (b' := (0 : ℝ))
      hu_deriv hv_deriv huv'_int hu'v_int h_zero h_infty

  have hu'v_simp :
      (∫ x in Set.Ioi u, (x * phi x) * x⁻¹) = ∫ x in Set.Ioi u, phi x := by
    have hEq :
        (fun x : ℝ => (x * phi x) * x⁻¹) =ᵐ[volume.restrict (Set.Ioi u)]
          fun x => phi x := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 ?_
      refine ae_of_all _ (fun x hx => ?_)
      have hxpos : 0 < x := lt_trans hu (by simpa [Set.mem_Ioi] using hx)
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      simp [mul_assoc, mul_left_comm, mul_comm, hx0]
    simpa using (MeasureTheory.integral_congr_ae hEq)

  have hibp' :
      (∫ x in Set.Ioi u, phi x / x ^ 2) = (phi u / u) - ∫ x in Set.Ioi u, phi x := by
    have hEq :
        (fun x : ℝ => (-phi x) * (-(x ^ 2)⁻¹)) = fun x => phi x / x ^ 2 := by
      funext x
      ring_nf
    calc
      (∫ x in Set.Ioi u, phi x / x ^ 2) =
          ∫ x in Set.Ioi u, (-phi x) * (-(x ^ 2)⁻¹) := by
            simpa [hEq, div_eq_mul_inv]
      _ = (0 : ℝ) - ((-phi u) * u⁻¹) - ∫ x in Set.Ioi u, (x * phi x) * x⁻¹ := by
            simpa using hibp
      _ = (phi u / u) - ∫ x in Set.Ioi u, phi x := by
            rw [hu'v_simp]
            simp [div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]

  have hPhiC : PhiC u = ∫ x in Set.Ioi u, phi x := PhiC_eq_integral_Ioi u

  have hIci_eq_Ioi : ∫ t in Set.Ici u, phi t / (t ^ 2) = ∫ t in Set.Ioi u, phi t / (t ^ 2) := by
    simpa using
      (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := (volume : Measure ℝ))
        (f := fun t => phi t / (t ^ 2)) (x := u))

  calc
    PhiC u = ∫ x in Set.Ioi u, phi x := hPhiC
    _ = phi u / u - ∫ x in Set.Ioi u, phi x / x ^ 2 := by linarith [hibp']
    _ = phi u / u - ∫ t in Set.Ici u, phi t / (t ^ 2) := by rw [hIci_eq_Ioi]

/-- Upper bound Mills inequality: for `u > 0`, `E(u) ≤ u + 1/u`. -/
lemma millsInv_le_add_inv (u : ℝ) (hu : 0 < u) : millsInv u ≤ u + 1 / u := by
  have hPhi := PhiC_eq_phi_div_sub_integral u hu
  have hnonneg : 0 ≤ ∫ t in Set.Ici u, phi t / (t ^ 2) := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    have hphi : 0 ≤ phi t := phi_nonneg t
    have ht2 : 0 ≤ (t ^ 2 : ℝ) := by nlinarith
    exact div_nonneg hphi ht2
  have hPhiC_pos : 0 < PhiC u := PhiC_pos u
  have hphi_pos : 0 < phi u := phi_pos u
  have hInt_bound' : ∫ t in Set.Ici u, phi t / (t ^ 2) ≤ PhiC u / u ^ 2 := by
    have hu2_pos : 0 < u ^ 2 := by nlinarith
    have hG : IntegrableOn (fun t => phi t / u ^ 2) (Set.Ici u) := by
      have hphi : Integrable (fun t => phi t) (volume.restrict (Set.Ici u)) :=
        integrable_phi.integrableOn
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hphi.const_mul ((u ^ 2)⁻¹)
    have hF : IntegrableOn (fun t => phi t / t ^ 2) (Set.Ici u) := by
      have hG' : Integrable (fun t => phi t / u ^ 2) (volume.restrict (Set.Ici u)) := hG
      have hF_meas :
          AEStronglyMeasurable (fun t => phi t / t ^ 2) (volume.restrict (Set.Ici u)) := by
        have hphi_meas : Measurable (fun t : ℝ => phi t) := continuous_phi.measurable
        have ht2_meas : Measurable (fun t : ℝ => t ^ 2) := (measurable_id.pow_const (2 : ℕ))
        exact (hphi_meas.div ht2_meas).aestronglyMeasurable
      have hbound :
          ∀ᵐ t ∂(volume.restrict (Set.Ici u)), ‖phi t / t ^ 2‖ ≤ ‖phi t / u ^ 2‖ := by
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Ici).2 ?_
        refine ae_of_all _ (fun t ht => ?_)
        have ht0 : 0 ≤ t := le_trans (le_of_lt hu) ht
        have hu0 : 0 ≤ u := le_of_lt hu
        have ht2_ge : u ^ 2 ≤ t ^ 2 := by
          have habs : |u| ≤ |t| := by
            simpa [abs_of_nonneg hu0, abs_of_nonneg ht0] using ht
          exact (sq_le_sq).2 habs
        have ht2_nonneg : 0 ≤ (t ^ 2 : ℝ) := by nlinarith
        have hu2_nonneg : 0 ≤ (u ^ 2 : ℝ) := by nlinarith
        calc
          ‖phi t / t ^ 2‖ = |phi t| / t ^ 2 := by
            simp [Real.norm_eq_abs, abs_div, abs_of_nonneg ht2_nonneg]
          _ ≤ |phi t| / u ^ 2 := by
            exact div_le_div_of_nonneg_left (abs_nonneg _) hu2_pos ht2_ge
          _ = ‖phi t / u ^ 2‖ := by
            simp [Real.norm_eq_abs, abs_div, abs_of_nonneg hu2_nonneg]
      exact Integrable.mono hG' hF_meas hbound
    have hBound : ∀ t ∈ Set.Ici u, phi t / t ^ 2 ≤ phi t / u ^ 2 := by
      intro t ht
      have ht0 : 0 ≤ t := le_trans (le_of_lt hu) ht
      have hu0 : 0 ≤ u := le_of_lt hu
      have ht2_ge : u ^ 2 ≤ t ^ 2 := by
        have habs : |u| ≤ |t| := by
          simpa [abs_of_nonneg hu0, abs_of_nonneg ht0] using ht
        exact (sq_le_sq).2 habs
      exact div_le_div_of_nonneg_left (phi_nonneg t) hu2_pos ht2_ge
    have hInt : ∫ t in Set.Ici u, phi t / (t ^ 2) ≤ ∫ t in Set.Ici u, phi t / u ^ 2 := by
      exact MeasureTheory.setIntegral_mono_on hF hG measurableSet_Ici hBound
    have hConst : ∫ t in Set.Ici u, phi t / u ^ 2 = PhiC u / u ^ 2 := by
      calc
        ∫ t in Set.Ici u, phi t / u ^ 2 = ∫ t in Set.Ici u, phi t * (u ^ 2)⁻¹ := by
          simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        _ = (∫ t in Set.Ici u, phi t) * (u ^ 2)⁻¹ := by
          simpa using
            (MeasureTheory.integral_mul_const (μ := (volume : Measure ℝ).restrict (Set.Ici u))
              (r := (u ^ 2)⁻¹) (f := phi))
        _ = PhiC u / u ^ 2 := by
          simp [PhiC, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    linarith [hInt, hConst]
  have hPhiC_lower : phi u * u / (u ^ 2 + 1) ≤ PhiC u := by
    have h3 : phi u / u ≤ PhiC u + PhiC u / u ^ 2 := by
      have h2 : PhiC u ≥ phi u / u - PhiC u / u ^ 2 := by
        linarith [hPhi, hInt_bound']
      linarith
    have h4 : phi u / u ≤ PhiC u * (1 + 1 / u ^ 2) := by
      simpa [div_eq_mul_inv, mul_add, mul_assoc, mul_left_comm, mul_comm] using h3
    have hPos : 0 < 1 + 1 / u ^ 2 := by
      have : 0 < (1 / u ^ 2 : ℝ) := by positivity
      linarith
    have h5 : (phi u / u) / (1 + 1 / u ^ 2) ≤ PhiC u :=
      (div_le_iff₀ hPos).2 h4
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have hSimp : (phi u / u) / (1 + 1 / u ^ 2) = phi u * u / (u ^ 2 + 1) := by
      field_simp [hu_ne]
    have : phi u * u / (u ^ 2 + 1) ≤ PhiC u := by
      calc
        phi u * u / (u ^ 2 + 1) = (phi u / u) / (1 + 1 / u ^ 2) := by
          symm
          exact hSimp
        _ ≤ PhiC u := h5
    exact this
  calc
    millsInv u = phi u / PhiC u := rfl
    _ ≤ phi u / (phi u * u / (u ^ 2 + 1)) := by
        have hPos : 0 < phi u * u / (u ^ 2 + 1) := by
          have : 0 < u ^ 2 + 1 := by nlinarith
          positivity
        exact div_le_div_of_nonneg_left (phi_nonneg u) hPos hPhiC_lower
    _ = (u ^ 2 + 1) / u := by
        have hphi_ne : phi u ≠ 0 := ne_of_gt hphi_pos
        have hu_ne : u ≠ 0 := ne_of_gt hu
        have hu2_1 : u ^ 2 + 1 ≠ 0 := by nlinarith
        field_simp
    _ = u + 1 / u := by
        field_simp

/-- Lower bound Mills inequality: for `u > 0`, `u ≤ E(u)`. -/
lemma le_millsInv (u : ℝ) (hu : 0 < u) : u ≤ millsInv u := by
  have hPhi := PhiC_eq_phi_div_sub_integral u hu
  have hnonneg : 0 ≤ ∫ t in Set.Ici u, phi t / (t ^ 2) := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    have hphi : 0 ≤ phi t := phi_nonneg t
    have ht2 : 0 ≤ (t ^ 2 : ℝ) := by nlinarith
    exact div_nonneg hphi ht2
  have hle : PhiC u ≤ phi u / u := by
    linarith [hPhi, hnonneg]
  have hu_nonneg : 0 ≤ u := le_of_lt hu
  have hmul : u * PhiC u ≤ phi u := by
    have hmul' := mul_le_mul_of_nonneg_left hle hu_nonneg
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have hmul'' : u * (phi u / u) = phi u := by
      field_simp [hu_ne]
    simpa [hmul''] using hmul'
  have hposPhi : 0 < PhiC u := PhiC_pos u
  have hres : u ≤ phi u / PhiC u := (le_div_iff₀ hposPhi).2 hmul
  simpa [millsInv] using hres

/-- Two-sided Mills bound for `u > 0`. -/
theorem mills_two_sided (u : ℝ) (hu : 0 < u) :
    u ≤ millsInv u ∧ millsInv u ≤ u + 1 / u := by
  exact ⟨le_millsInv u hu, millsInv_le_add_inv u hu⟩

/-
Global bound.
-/

/-- Global growth bound:

`0 < E(u)` and `E(u) ≤ max u 0 + C` for all `u`.
-/
theorem millsInv_pos_and_le_max_add_C (u : ℝ) :
    0 < millsInv u ∧ millsInv u ≤ max u 0 + C := by
  refine ⟨millsInv_pos u, ?_⟩
  by_cases hu1 : u ≤ 1
  · -- small values
    have h : millsInv u ≤ C := millsInv_le_C_of_le_one (u := u) hu1
    have h' : C ≤ max u 0 + C := by
      have : 0 ≤ max u 0 := le_max_right _ _
      linarith
    exact le_trans h h'
  · -- large values: `1 < u`
    have hu_ge1 : 1 ≤ u := le_of_not_ge hu1
    have hu_pos : 0 < u := lt_of_lt_of_le (by norm_num) hu_ge1
    have hM : millsInv u ≤ u + 1 / u := millsInv_le_add_inv u hu_pos
    have hOneDiv : (1 / u : ℝ) ≤ 1 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hu_ge1
      simpa using h
    have h' : millsInv u ≤ u + 1 := by
      nlinarith
    have hC : (1 : ℝ) ≤ C := by
      simpa [C] using (le_max_right (1 / PhiC 1) 1)
    have : millsInv u ≤ u + C := by
      nlinarith
    have hmax : max u 0 = u := by
      exact max_eq_left (le_of_lt hu_pos)
    simpa [hmax, add_assoc, add_comm, add_left_comm] using this

/-- Convenience corollary, dropping the positivity part. -/
lemma millsInv_le_max_add_C (u : ℝ) : millsInv u ≤ max u 0 + C :=
  (millsInv_pos_and_le_max_add_C u).2

end

end Mills

















