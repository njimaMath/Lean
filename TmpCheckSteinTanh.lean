import Mathlib
import perceptronFixed.derivative_of_B.derivative_B
import perceptronFixed.Prop_A_P.Prop_A_P

open scoped BigOperators Topology NNReal Real ENNReal Interval
open MeasureTheory Filter

namespace Scratch

noncomputable section

abbrev γ : Measure ℝ := ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))

abbrev Expect (f : ℝ → ℝ) : ℝ := ∫ z, f z ∂γ

def sech (x : ℝ) : ℝ := 1 / Real.cosh x

-- pointwise inequality
lemma log_cosh_le_mul_tanh (x : ℝ) : Real.log (Real.cosh x) ≤ x * Real.tanh x := by
  let f : ℝ → ℝ := fun x => x * Real.tanh x - Real.log (Real.cosh x)
  have hf0 : f 0 = 0 := by
    simp [f]
  have hf_differentiable : Differentiable ℝ f := by
    intro x
    have hg : DifferentiableAt ℝ (fun x => x * Real.tanh x) x := by
      exact ((hasDerivAt_id x).mul (PropAP.hasDerivAt_tanh x)).differentiableAt
    have hh : DifferentiableAt ℝ (fun x => Real.log (Real.cosh x)) x := by
      have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
      exact ((Real.hasDerivAt_log hcosh).comp x (Real.hasDerivAt_cosh x)).differentiableAt
    exact hg.sub hh
  have hderiv : ∀ x : ℝ, deriv f x = x * (sech x) ^ 2 := by
    intro x
    have hmul :
        HasDerivAt (fun x => x * Real.tanh x)
          (Real.tanh x + x * (1 / (Real.cosh x) ^ 2)) x := by
      simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using
        (hasDerivAt_id x).mul (PropAP.hasDerivAt_tanh x)
    have hlog :
        HasDerivAt (fun x => Real.log (Real.cosh x)) (Real.tanh x) x := by
      have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
      have h := (Real.hasDerivAt_log hcosh).comp x (Real.hasDerivAt_cosh x)
      simpa [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
    have hf : HasDerivAt f (x * (sech x) ^ 2) x := by
      have h := hmul.sub hlog
      simpa [f, sech] using h
    simpa using hf.deriv
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (D := Set.Ici 0) (convex_Ici 0)
      (hf_differentiable.continuous.continuousOn) ?_ ?_
    · simpa [interior_Ici] using (hf_differentiable.differentiableOn : DifferentiableOn ℝ f (Set.Ioi 0))
    · intro x hx
      have hx' : (0 : ℝ) < x := by
        simpa [interior_Ici] using hx
      have hx0 : 0 ≤ x := le_of_lt hx'
      have hsech : 0 ≤ (sech x) ^ 2 := by nlinarith
      simpa [hderiv x] using mul_nonneg hx0 hsech
  by_cases hx : 0 ≤ x
  · have h := hmono (a := 0) (b := x) (by simp) hx hx
    have hxnonneg : 0 ≤ f x := by
      simpa [hf0] using h
    exact (sub_nonneg).1 (by simpa [f] using hxnonneg)
  · have hxpos : 0 ≤ -x := by linarith
    have h := hmono (a := 0) (b := -x) (by simp) hxpos hxpos
    have hxnonneg : 0 ≤ f (-x) := by
      simpa [hf0] using h
    have hxnonneg' : 0 ≤ f x := by
      simpa [f, Real.tanh_neg, Real.cosh_neg] using hxnonneg
    exact (sub_nonneg).1 (by simpa [f] using hxnonneg')

private lemma mills_phi_eq_gaussianPDFReal : MillsBlueprint.Proof.φ = ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) := by
  funext x
  simp [MillsBlueprint.Proof.φ, ProbabilityTheory.gaussianPDFReal]

-- Gaussian IBP for standard normal
private lemma gaussianIBP_gaussianReal
    (ψ : ℝ → ℝ)
    (hψ : Differentiable ℝ ψ)
    (hψ_int : Integrable ψ γ)
    (hψ'_int : Integrable (fun x => deriv ψ x) γ)
    (hxψ_int : Integrable (fun x => x * ψ x) γ) :
    (∫ x, x * ψ x ∂γ) = (∫ x, deriv ψ x ∂γ) := by
  have hv : (1 : ℝ≥0) ≠ 0 := by simp
  have hf : Measurable (ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0)) :=
    ProbabilityTheory.measurable_gaussianPDF _ _
  have hflt :
      (∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0) x < ∞) := by
    exact ae_of_all _ (fun _ => ProbabilityTheory.gaussianPDF_lt_top)

  have hψ_int' :
      Integrable ψ (volume.withDensity (ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0))) := by
    simpa [γ, ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv] using hψ_int
  have hψ'_int' :
      Integrable (fun x => deriv ψ x)
        (volume.withDensity (ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0))) := by
    simpa [γ, ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv] using hψ'_int
  have hxψ_int' :
      Integrable (fun x => x * ψ x)
        (volume.withDensity (ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0))) := by
    simpa [γ, ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv] using hxψ_int

  have hψφ : Integrable (fun x : ℝ => ψ x * MillsBlueprint.Proof.φ x) (volume : Measure ℝ) := by
    have h :=
      (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
            (f := ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0)) hf hflt (g := ψ)).1 hψ_int'
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, mills_phi_eq_gaussianPDFReal] using h
  have hψ'φ : Integrable (fun x : ℝ => deriv ψ x * MillsBlueprint.Proof.φ x) (volume : Measure ℝ) := by
    have h :=
      (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
            (f := ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0)) hf hflt (g := fun x => deriv ψ x)).1 hψ'_int'
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, mills_phi_eq_gaussianPDFReal] using h
  have hxψφ : Integrable (fun x : ℝ => (x * ψ x) * MillsBlueprint.Proof.φ x) (volume : Measure ℝ) := by
    have h :=
      (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
            (f := ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : ℝ≥0)) hf hflt (g := fun x => x * ψ x)).1 hxψ_int'
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, mills_phi_eq_gaussianPDFReal] using h

  have hu : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x => (hψ x).hasDerivAt
  have hvφ : ∀ x, HasDerivAt MillsBlueprint.Proof.φ (-x * MillsBlueprint.Proof.φ x) x := by
    intro x
    have hdiff : DifferentiableAt ℝ MillsBlueprint.Proof.φ x := by
      change DifferentiableAt ℝ (fun u : ℝ => (1 / Real.sqrt (2 * Real.pi)) * rexp (-(u ^ 2) / 2)) x
      fun_prop
    simpa [MillsBlueprint.Proof.deriv_φ (u := x)] using hdiff.hasDerivAt

  have huv' : Integrable (fun x : ℝ => ψ x * (-x * MillsBlueprint.Proof.φ x)) (volume : Measure ℝ) := by
    have hneg : Integrable (fun x : ℝ => -(x * (ψ x * MillsBlueprint.Proof.φ x))) (volume : Measure ℝ) := by
      simpa [mul_assoc] using (hxψφ.const_mul (-1 : ℝ))
    have hpoint :
        (fun x : ℝ => ψ x * (-x * MillsBlueprint.Proof.φ x)) = fun x => -(x * (ψ x * MillsBlueprint.Proof.φ x)) := by
      funext x
      ring_nf
    rw [hpoint]
    exact hneg

  have hu'v : Integrable (fun x : ℝ => deriv ψ x * MillsBlueprint.Proof.φ x) (volume : Measure ℝ) := hψ'φ
  have huv : Integrable (fun x : ℝ => ψ x * MillsBlueprint.Proof.φ x) (volume : Measure ℝ) := hψφ

  have hibp_vol :
      (∫ x : ℝ, ψ x * (-x * MillsBlueprint.Proof.φ x)) =
        -∫ x : ℝ, (deriv ψ x) * MillsBlueprint.Proof.φ x := by
    simpa using
      (MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
        (u := ψ) (v := MillsBlueprint.Proof.φ) (u' := fun x => deriv ψ x) (v' := fun x => -x * MillsBlueprint.Proof.φ x)
        hu hvφ huv' hu'v huv)

  have hibp_vol' :
      (∫ x : ℝ, (x * ψ x) * MillsBlueprint.Proof.φ x) =
        ∫ x : ℝ, (deriv ψ x) * MillsBlueprint.Proof.φ x := by
    have hneg :
        (∫ x : ℝ, (x * ψ x) * MillsBlueprint.Proof.φ x) =
          -∫ x : ℝ, ψ x * (-x * MillsBlueprint.Proof.φ x) := by
      have :
          (fun x : ℝ => (x * ψ x) * MillsBlueprint.Proof.φ x) =
            fun x => -(ψ x * (-x * MillsBlueprint.Proof.φ x)) := by
        funext x
        ring_nf
      simp [this, MeasureTheory.integral_neg]
    have hneg' :
        -∫ x : ℝ, ψ x * (-x * MillsBlueprint.Proof.φ x) =
          ∫ x : ℝ, (deriv ψ x) * MillsBlueprint.Proof.φ x := by
      simpa using congrArg Neg.neg hibp_vol
    simpa [hneg] using hneg'

  have hL :
      (∫ x, x * ψ x ∂γ) = ∫ x : ℝ, (x * ψ x) * MillsBlueprint.Proof.φ x := by
    have hμ :
        (∫ x, x * ψ x ∂γ) =
          ∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x * (x * ψ x) := by
      simpa [γ, ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv,
        smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    simpa [mills_phi_eq_gaussianPDFReal, mul_assoc, mul_left_comm, mul_comm] using hμ

  have hR :
      (∫ x, deriv ψ x ∂γ) = ∫ x : ℝ, (deriv ψ x) * MillsBlueprint.Proof.φ x := by
    have hμ :
        (∫ x, deriv ψ x ∂γ) =
          ∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x * (deriv ψ x) := by
      simpa [γ, ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv,
        smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    simpa [mills_phi_eq_gaussianPDFReal, mul_assoc, mul_left_comm, mul_comm] using hμ

  calc
    (∫ x, x * ψ x ∂γ) = ∫ x : ℝ, (x * ψ x) * MillsBlueprint.Proof.φ x := hL
    _ = ∫ x : ℝ, (deriv ψ x) * MillsBlueprint.Proof.φ x := hibp_vol'
    _ = (∫ x, deriv ψ x ∂γ) := by simpa [hR]

-- Stein identity for tanh
lemma stein_tanh (r : ℝ) :
    Expect (fun z : ℝ => z * Real.tanh (Real.sqrt r * z)) =
      Real.sqrt r * Expect (fun z : ℝ => (sech (Real.sqrt r * z)) ^ 2) := by
  let ψ : ℝ → ℝ := fun z => Real.tanh (Real.sqrt r * z)
  have hψ : Differentiable ℝ ψ := by
    intro z
    have hlin : HasDerivAt (fun z : ℝ => Real.sqrt r * z) (Real.sqrt r) z := by
      simpa using (hasDerivAt_const_mul (c := Real.sqrt r) (x := z))
    exact ((PropAP.hasDerivAt_tanh (Real.sqrt r * z)).comp z hlin).differentiableAt
  have hψ_deriv : ∀ z : ℝ, deriv ψ z = Real.sqrt r * (sech (Real.sqrt r * z)) ^ 2 := by
    intro z
    have hlin : HasDerivAt (fun z : ℝ => Real.sqrt r * z) (Real.sqrt r) z := by
      simpa using (hasDerivAt_const_mul (c := Real.sqrt r) (x := z))
    have hcomp := (PropAP.hasDerivAt_tanh (Real.sqrt r * z)).comp z hlin
    -- hcomp.deriv gives `deriv ψ z = (1 / cosh(..)^2) * √r`
    have : deriv ψ z = (1 / (Real.cosh (Real.sqrt r * z)) ^ 2) * Real.sqrt r := by
      simpa [ψ] using hcomp.deriv
    -- rewrite
    simpa [sech, mul_assoc, mul_left_comm, mul_comm] using this.trans ?_ 
  -- TODO: finish
  sorry

end

end Scratch
