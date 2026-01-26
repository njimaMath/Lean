/-
Gaussian integration by parts (Stein lemma), coordinate form.

Target statement (centered case):
  E[X_i * f(X)] = ∑ j, Cov(X_i, X_j) * E[∂_j f(X)]

Blueprint structure:
  1) 1D Stein lemma for gaussianReal on ℝ
  2) nD identity-covariance case for product measure (iid standard normals)
  3) general covariance via linear pushforward by a matrix A
  4) optional corollary for random vectors using HasLaw
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped BigOperators MeasureTheory
open MeasureTheory

namespace ProbabilityTheory

noncomputable section

/-! Basic ambient types and notations -/

abbrev E (n : ℕ) := Fin n → ℝ

abbrev e (n : ℕ) (i : Fin n) : E n :=
  Pi.single i 1

/-- Coordinate directional derivative, implemented via `fderiv`. -/
def partialDeriv (n : ℕ) (i : Fin n) (f : E n → ℝ) (x : E n) : ℝ :=
  (fderiv ℝ f x) (e n i)

/-- Coordinate covariance entry (scalar covariance). -/
def covCoord (n : ℕ) (μ : Measure (E n)) (i j : Fin n) : ℝ :=
  covariance (fun x : E n => x i) (fun x : E n => x j) μ


/-! 1) One-dimensional Stein lemma for `gaussianReal` -/

/-
Core analytic ingredients:

(A) rewrite integrals against gaussianReal using the pdf:
    `integral_gaussianReal_eq_integral_smul` (in Gaussian.Real)

(B) compute derivative of the pdf:
    d/dx gaussianPDFReal μ v x = -(x-μ)/(v) * gaussianPDFReal μ v x   (v ≠ 0)

(C) apply integration by parts for compactly supported functions with respect to volume.
    Import `MeasureTheory.Integral.CompactlySupported` and
    `IntervalIntegral.IntegrationByParts` and search for lemmas named like
      `integral_mul_deriv_eq_neg_integral_deriv_mul`
    or intervalIntegral variants.
-/

/-- Derivative of the real Gaussian pdf (for `v ≠ 0`). -/
lemma hasDerivAt_gaussianPDFReal
    (μ : ℝ) {v : NNReal} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v)
      (-(x - μ) / (v : ℝ) * gaussianPDFReal μ v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by
    intro hv0
    apply hv
    exact NNReal.coe_eq_zero.mp hv0

  have hsub : HasDerivAt (fun x : ℝ => x - μ) 1 x := by
    simpa using (hasDerivAt_id x).sub_const μ
  have hpow : HasDerivAt (fun x : ℝ => (x - μ) ^ 2) (2 * (x - μ)) x := by
    simpa [pow_two, mul_assoc] using (hsub.pow 2)
  have hexpArg :
      HasDerivAt (fun x : ℝ => -((x - μ) ^ 2) / (2 * (v : ℝ)))
        (-(x - μ) / (v : ℝ)) x := by
    have hneg : HasDerivAt (fun x : ℝ => -((x - μ) ^ 2)) (-(2 * (x - μ))) x := by
      simpa using hpow.neg
    have hdiv :
        HasDerivAt (fun x : ℝ => -((x - μ) ^ 2) / (2 * (v : ℝ)))
          (-(2 * (x - μ)) / (2 * (v : ℝ))) x := by
      simpa [div_eq_mul_inv] using hneg.div_const (2 * (v : ℝ))
    have hsim :
        (-(2 * (x - μ)) / (2 * (v : ℝ))) = (-(x - μ) / (v : ℝ)) := by
      field_simp [hv']
    simpa [hsim] using hdiv

  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-((x - μ) ^ 2) / (2 * (v : ℝ))))
        (Real.exp (-((x - μ) ^ 2) / (2 * (v : ℝ))) * (-(x - μ) / (v : ℝ))) x := by
    simpa using (Real.hasDerivAt_exp _).comp x hexpArg

  simpa [ProbabilityTheory.gaussianPDFReal_def, mul_assoc, mul_left_comm, mul_comm] using
    (hexp.const_mul ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹))

lemma deriv_gaussianPDFReal
    (μ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    deriv (gaussianPDFReal μ v)
      = fun x => (-(x - μ) / (v : ℝ)) * gaussianPDFReal μ v x := by
  funext x
  simpa using (hasDerivAt_gaussianPDFReal μ hv x).deriv

/-- Stein lemma on `ℝ` for compactly supported `f`. -/
theorem gaussianReal_ibp
    (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) :
    (∫ x, (x - μ) * f x ∂gaussianReal μ v)
      = (v : ℝ) * ∫ x, (deriv f x) ∂gaussianReal μ v := by
  have hv' : (v : ℝ) ≠ 0 := by
    intro hv0
    apply hv
    exact NNReal.coe_eq_zero.mp hv0

  -- Rewrite integrals w.r.t. `gaussianReal` as Lebesgue integrals with the density.
  have hL :
      (∫ x, (x - μ) * f x ∂gaussianReal μ v)
        = ∫ x : ℝ, gaussianPDFReal μ v x * ((x - μ) * f x) := by
    simpa [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := μ) (v := v) hv,
      smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  have hR :
      (∫ x, (deriv f x) ∂gaussianReal μ v)
        = ∫ x : ℝ, gaussianPDFReal μ v x * (deriv f x) := by
    simpa [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := μ) (v := v) hv,
      smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

  -- Integration by parts for `u = f` and `v = gaussianPDFReal μ v` on Lebesgue measure.
  set pdf : ℝ → ℝ := gaussianPDFReal μ v
  set pdf' : ℝ → ℝ := fun x => (-(x - μ) / (v : ℝ)) * pdf x

  have hu : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    (hf.differentiable le_rfl x).hasDerivAt
  have hvPDF : ∀ x, HasDerivAt pdf (pdf' x) x := by
    intro x
    simpa [pdf, pdf', mul_assoc, mul_left_comm, mul_comm] using (hasDerivAt_gaussianPDFReal μ hv x)

  have hcont_f : Continuous f := hf.continuous
  have hcont_df : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hcont_pdf : Continuous pdf := by
    -- Unfold the definition of `gaussianPDFReal`.
    dsimp [pdf]
    simp [ProbabilityTheory.gaussianPDFReal_def]
    fun_prop
  have hcont_pdf' : Continuous pdf' := by
    have hscale : Continuous fun x : ℝ => (-(x - μ) / (v : ℝ)) := by
      fun_prop
    simpa [pdf', Pi.mul_def] using hscale.mul hcont_pdf

  have huv' : Integrable (fun x : ℝ => f x * pdf' x) := by
    refine (hcont_f.mul hcont_pdf').integrable_of_hasCompactSupport ?_
    simpa [Pi.mul_def] using (hsupp.mul_right (f' := pdf'))
  have hu'v : Integrable (fun x : ℝ => deriv f x * pdf x) := by
    refine (hcont_df.mul hcont_pdf).integrable_of_hasCompactSupport ?_
    simpa [Pi.mul_def] using (hsupp.deriv.mul_right (f' := pdf))
  have huv : Integrable (fun x : ℝ => f x * pdf x) := by
    refine (hcont_f.mul hcont_pdf).integrable_of_hasCompactSupport ?_
    simpa [Pi.mul_def] using (hsupp.mul_right (f' := pdf))

  have hibp :
      (∫ x : ℝ, f x * pdf' x) = -∫ x : ℝ, (deriv f x) * pdf x := by
    simpa [Pi.mul_def] using
      (MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
        (u := f) (v := pdf) (u' := fun x => deriv f x) (v' := pdf')
        hu hvPDF huv' hu'v huv)

  have hpdf : ∀ x : ℝ, (x - μ) * pdf x = - (v : ℝ) * pdf' x := by
    intro x
    simp [pdf', hv', pdf, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] <;>
      field_simp [hv'] <;> ring

  calc
    (∫ x, (x - μ) * f x ∂gaussianReal μ v)
        = ∫ x : ℝ, pdf x * ((x - μ) * f x) := by
            simpa [hL, pdf]
    _ = ∫ x : ℝ, f x * ((x - μ) * pdf x) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ = ∫ x : ℝ, f x * (-(v : ℝ) * pdf' x) := by
            refine integral_congr_ae (ae_of_all _ (fun x => ?_))
            simp [hpdf x, mul_assoc, mul_left_comm, mul_comm]
    _ = -(v : ℝ) * ∫ x : ℝ, f x * pdf' x := by
            calc
              ∫ x : ℝ, f x * (-(v : ℝ) * pdf' x) = ∫ x : ℝ, (-(v : ℝ)) * (f x * pdf' x) := by
                refine integral_congr_ae (ae_of_all _ (fun x => ?_))
                ring
              _ = -(v : ℝ) * ∫ x : ℝ, f x * pdf' x := by
                simpa using
                  (MeasureTheory.integral_const_mul (-(v : ℝ)) (fun x : ℝ => f x * pdf' x))
    _ = (v : ℝ) * ∫ x : ℝ, (deriv f x) * pdf x := by
            simp [hibp, mul_assoc]
    _ = (v : ℝ) * ∫ x, (deriv f x) ∂gaussianReal μ v := by
            have : (∫ x : ℝ, (deriv f x) * pdf x) = ∫ x : ℝ, pdf x * (deriv f x) := by
              simp [mul_comm]
            simpa [hR, pdf, this]



/-! ### Integrable version (no compact support) -/

/-- Stein lemma on `ℝ` for (globally) differentiable `f` under integrability hypotheses. -/
theorem gaussianReal_ibp_integrable
    (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    {f : ℝ → ℝ}
    (hf : Differentiable ℝ f)
    (hf_int : Integrable f (gaussianReal μ v))
    (hf'_int : Integrable (fun x => deriv f x) (gaussianReal μ v))
    (hx_f_int : Integrable (fun x => (x - μ) * f x) (gaussianReal μ v)) :
    (∫ x, (x - μ) * f x ∂gaussianReal μ v)
      = (v : ℝ) * ∫ x, (deriv f x) ∂gaussianReal μ v := by
  have hv' : (v : ℝ) ≠ 0 := by
    intro hv0
    apply hv
    exact NNReal.coe_eq_zero.mp hv0

  -- Rewrite integrability under `gaussianReal` to integrability under Lebesgue with the density.
  have hf_pdf_meas : Measurable (gaussianPDF μ v) :=
    ProbabilityTheory.measurable_gaussianPDF _ _
  have hf_pdf_lt_top :
      (∀ᵐ x ∂(volume : Measure ℝ), gaussianPDF μ v x < ⊤) := by
    refine ae_of_all _ (fun x => ?_)
    simpa using (ProbabilityTheory.gaussianPDF_lt_top (μ := μ) (v := v) (x := x))

  have hf_int' :
      Integrable f (volume.withDensity (gaussianPDF μ v)) := by
    simpa [ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := μ) (v := v) hv] using hf_int
  have hf'_int' :
      Integrable (fun x => deriv f x) (volume.withDensity (gaussianPDF μ v)) := by
    simpa [ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := μ) (v := v) hv] using hf'_int
  have hx_f_int' :
      Integrable (fun x => (x - μ) * f x) (volume.withDensity (gaussianPDF μ v)) := by
    simpa [ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := μ) (v := v) hv] using hx_f_int

  have hf_pdf :
      Integrable (fun x : ℝ => f x * gaussianPDFReal μ v x) (volume : Measure ℝ) := by
    have h :=
      (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
            (f := gaussianPDF μ v) hf_pdf_meas hf_pdf_lt_top (g := f)).1 hf_int'
    simpa [smul_eq_mul, ProbabilityTheory.toReal_gaussianPDF, mul_assoc, mul_left_comm, mul_comm] using h

  have hf'_pdf :
      Integrable (fun x : ℝ => deriv f x * gaussianPDFReal μ v x) (volume : Measure ℝ) := by
    have h :=
      (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
            (f := gaussianPDF μ v) hf_pdf_meas hf_pdf_lt_top (g := fun x => deriv f x)).1 hf'_int'
    simpa [smul_eq_mul, ProbabilityTheory.toReal_gaussianPDF, mul_assoc, mul_left_comm, mul_comm] using h

  have hx_f_pdf :
      Integrable (fun x : ℝ => (x - μ) * f x * gaussianPDFReal μ v x) (volume : Measure ℝ) := by
    have h :=
      (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
            (f := gaussianPDF μ v) hf_pdf_meas hf_pdf_lt_top (g := fun x => (x - μ) * f x)).1 hx_f_int'
    simpa [smul_eq_mul, ProbabilityTheory.toReal_gaussianPDF, mul_assoc, mul_left_comm, mul_comm] using h

  -- Integration by parts for `u = f` and `v = gaussianPDFReal μ v` on Lebesgue measure.
  set pdf : ℝ → ℝ := gaussianPDFReal μ v
  set pdf' : ℝ → ℝ := fun x => (-(x - μ) / (v : ℝ)) * pdf x

  have hu : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    (hf x).hasDerivAt
  have hvPDF : ∀ x, HasDerivAt pdf (pdf' x) x := by
    intro x
    simpa [pdf, pdf', mul_assoc, mul_left_comm, mul_comm] using (hasDerivAt_gaussianPDFReal μ hv x)

  have huv : Integrable (fun x : ℝ => f x * pdf x) := by
    simpa [pdf, mul_assoc, mul_left_comm, mul_comm] using hf_pdf
  have hu'v : Integrable (fun x : ℝ => deriv f x * pdf x) := by
    simpa [pdf, mul_assoc, mul_left_comm, mul_comm] using hf'_pdf
  have huv' : Integrable (fun x : ℝ => f x * pdf' x) := by
    have : (fun x : ℝ => f x * pdf' x) =
        fun x => (-(1 / (v : ℝ))) * ((x - μ) * f x * pdf x) := by
      funext x
      simp [pdf', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      ring
    simpa [this] using hx_f_pdf.const_mul (-(1 / (v : ℝ)))

  have hibp :
      (∫ x : ℝ, f x * pdf' x) = -∫ x : ℝ, (deriv f x) * pdf x := by
    simpa [Pi.mul_def] using
      (MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
        (u := f) (v := pdf) (u' := fun x => deriv f x) (v' := pdf')
        hu hvPDF huv' hu'v huv)

  have hpdf : ∀ x : ℝ, (x - μ) * pdf x = - (v : ℝ) * pdf' x := by
    intro x
    simp [pdf', hv', pdf, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] <;>
      field_simp [hv'] <;> ring

  -- Go back to `gaussianReal` via `integral_gaussianReal_eq_integral_smul`.
  have hL :
      (∫ x, (x - μ) * f x ∂gaussianReal μ v)
        = ∫ x : ℝ, pdf x * ((x - μ) * f x) := by
    simpa [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := μ) (v := v) hv,
      pdf, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  have hR :
      (∫ x, (deriv f x) ∂gaussianReal μ v)
        = ∫ x : ℝ, pdf x * (deriv f x) := by
    simpa [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := μ) (v := v) hv,
      pdf, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

  calc
    (∫ x, (x - μ) * f x ∂gaussianReal μ v)
        = ∫ x : ℝ, pdf x * ((x - μ) * f x) := hL
    _ = ∫ x : ℝ, f x * ((x - μ) * pdf x) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = ∫ x : ℝ, f x * (-(v : ℝ) * pdf' x) := by
          refine integral_congr_ae (ae_of_all _ (fun x => ?_))
          simp [hpdf x, mul_assoc, mul_left_comm, mul_comm]
    _ = -(v : ℝ) * ∫ x : ℝ, f x * pdf' x := by
          calc
            ∫ x : ℝ, f x * (-(v : ℝ) * pdf' x) = ∫ x : ℝ, (-(v : ℝ)) * (f x * pdf' x) := by
              refine integral_congr_ae (ae_of_all _ (fun x => ?_))
              ring
            _ = -(v : ℝ) * ∫ x : ℝ, f x * pdf' x := by
              simpa using
                (MeasureTheory.integral_const_mul (-(v : ℝ)) (fun x : ℝ => f x * pdf' x))
    _ = (v : ℝ) * ∫ x : ℝ, (deriv f x) * pdf x := by
          simp [hibp, mul_assoc]
    _ = (v : ℝ) * ∫ x, (deriv f x) ∂gaussianReal μ v := by
          have : (∫ x : ℝ, (deriv f x) * pdf x) = ∫ x : ℝ, pdf x * (deriv f x) := by
            simp [mul_comm]
          simpa [hR, pdf, this]

/-- Stein lemma for a random variable with Gaussian law, in integrable form. -/
theorem gaussianReal_ibp_integrable_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {Z : Ω → ℝ} {μ : ℝ} {v : NNReal} (hv : v ≠ 0)
    (hZ : Measure.map Z P = gaussianReal μ v)
    {f : ℝ → ℝ}
    (hf : Differentiable ℝ f)
    (hfZ_int : Integrable (fun ω => f (Z ω)) P)
    (hf'Z_int : Integrable (fun ω => deriv f (Z ω)) P)
    (hx_fZ_int : Integrable (fun ω => (Z ω - μ) * f (Z ω)) P) :
    (∫ ω, (Z ω - μ) * f (Z ω) ∂P)
      = (v : ℝ) * ∫ ω, deriv f (Z ω) ∂P := by
  have hZ_meas : AEMeasurable Z P := by
    refine AEMeasurable.of_map_ne_zero ?_
    have hgauss_ne : gaussianReal μ v ≠ 0 := by
      simpa using (MeasureTheory.IsProbabilityMeasure.ne_zero (μ := gaussianReal μ v))
    simpa [hZ] using hgauss_ne

  have hf_aesm : AEStronglyMeasurable f (Measure.map Z P) :=
    hf.continuous.measurable.aestronglyMeasurable
  have hf'_aesm :
      AEStronglyMeasurable (fun x : ℝ => deriv f x) (Measure.map Z P) := by
    simpa using aestronglyMeasurable_deriv f (Measure.map Z P)
  have hx_f_aesm :
      AEStronglyMeasurable (fun x : ℝ => (x - μ) * f x) (Measure.map Z P) := by
    have hmeas : Measurable (fun x : ℝ => (x - μ) * f x) := by
      simpa using (measurable_id.sub_const μ).mul hf.continuous.measurable
    exact hmeas.aestronglyMeasurable

  have hf_int_map : Integrable f (Measure.map Z P) :=
    (integrable_map_measure hf_aesm hZ_meas).2 hfZ_int
  have hf'_int_map : Integrable (fun x : ℝ => deriv f x) (Measure.map Z P) :=
    (integrable_map_measure hf'_aesm hZ_meas).2 hf'Z_int
  have hx_f_int_map : Integrable (fun x : ℝ => (x - μ) * f x) (Measure.map Z P) :=
    (integrable_map_measure hx_f_aesm hZ_meas).2 hx_fZ_int

  have hf_int_gauss : Integrable f (gaussianReal μ v) := by
    simpa [hZ] using hf_int_map
  have hf'_int_gauss : Integrable (fun x : ℝ => deriv f x) (gaussianReal μ v) := by
    simpa [hZ] using hf'_int_map
  have hx_f_int_gauss : Integrable (fun x : ℝ => (x - μ) * f x) (gaussianReal μ v) := by
    simpa [hZ] using hx_f_int_map

  have hibp_gauss :
      (∫ x, (x - μ) * f x ∂gaussianReal μ v)
        = (v : ℝ) * ∫ x, (deriv f x) ∂gaussianReal μ v :=
    gaussianReal_ibp_integrable (μ := μ) hv hf hf_int_gauss hf'_int_gauss hx_f_int_gauss

  have hibp_map :
      (∫ x, (x - μ) * f x ∂Measure.map Z P)
        = (v : ℝ) * ∫ x, (deriv f x) ∂Measure.map Z P := by
    simpa [hZ] using hibp_gauss

  have hL :
      (∫ x, (x - μ) * f x ∂Measure.map Z P)
        = ∫ ω, (Z ω - μ) * f (Z ω) ∂P := by
    simpa [Function.comp, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.integral_map (μ := P) (φ := Z) hZ_meas
        (f := fun x : ℝ => (x - μ) * f x) hx_f_int_map.aestronglyMeasurable)

  have hR :
      (∫ x, (deriv f x) ∂Measure.map Z P)
        = ∫ ω, deriv f (Z ω) ∂P := by
    simpa [Function.comp] using
      (MeasureTheory.integral_map (μ := P) (φ := Z) hZ_meas
        (f := fun x : ℝ => deriv f x) hf'_int_map.aestronglyMeasurable)

  calc
    (∫ ω, (Z ω - μ) * f (Z ω) ∂P)
        = (∫ x, (x - μ) * f x ∂Measure.map Z P) := by
            simpa using hL.symm
    _ = (v : ℝ) * ∫ x, (deriv f x) ∂Measure.map Z P := hibp_map
    _ = (v : ℝ) * ∫ ω, deriv f (Z ω) ∂P := by
            simp [hR]
/-! 2) nD identity-covariance case: product of standard Gaussians -/

/-- Standard iid Gaussian measure on `Fin n → ℝ`. -/
def gaussianStd (n : ℕ) : Measure (E n) :=
  Measure.pi (fun _ : Fin n => gaussianReal (0 : ℝ) (1 : NNReal))

/-
Goal for the product measure:
  ∫ x, x i * f x ∂gaussianStd n = ∫ x, partialDeriv n i f x ∂gaussianStd n

Proof method:
  Use Fubini on the `i`-th coordinate.
  For a fixed "other coordinates" vector `x`, define the 1D slice
    g(t) := f (Function.update x i t)
  then apply `gaussianReal_ibp 0 (v=1)` to `g`.

You will need lemmas for:
  * rewriting `Measure.pi` integral as an iterated integral with the i-th coordinate separated
  * measurability/integrability of the slice function
  * identifying `deriv g` with the directional derivative `partialDeriv n i f` evaluated at the updated point

In practice you search in:
  `Mathlib/MeasureTheory/Integral/Pi` and `.../Integral/Prod`
for lemmas named like `integral_pi`, `integral_update`, `integral_pi_split`, etc.
-/

/-- Product-measure Stein lemma (identity covariance). -/
theorem gaussianStd_ibp_coord
    {n : ℕ} (i : Fin n)
    {f : E n → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) :
    (∫ x, x i * f x ∂gaussianStd n)
      = ∫ x, partialDeriv n i f x ∂gaussianStd n := by
  classical
  cases n with
  | zero =>
      cases i with
      | mk val isLt =>
        cases isLt
  | succ n =>
      let γ : Measure ℝ := gaussianReal (0 : ℝ) (1 : NNReal)
      let μrest : Measure (Fin n → ℝ) := gaussianStd n
      let split : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
      have hmp :
          MeasurePreserving split (gaussianStd (n + 1)) (γ.prod μrest) := by
        simpa [split, γ, μrest, gaussianStd] using
          (measurePreserving_piFinSuccAbove
            (α := fun _ : Fin (n + 1) => ℝ)
            (μ := fun _ : Fin (n + 1) => gaussianReal (0 : ℝ) (1 : NNReal)) i)

      haveI : IsProbabilityMeasure (gaussianStd (n + 1)) := by
        dsimp [gaussianStd]
        infer_instance
      haveI : IsFiniteMeasure (gaussianStd (n + 1)) :=
        ⟨by
          simpa using (ENNReal.one_lt_top)⟩
      haveI : IsFiniteMeasureOnCompacts (gaussianStd (n + 1)) := by
        refine ⟨fun K _ => measure_lt_top (gaussianStd (n + 1)) K⟩

      haveI : IsProbabilityMeasure μrest := by
        dsimp [μrest, gaussianStd]
        infer_instance
      haveI : IsFiniteMeasure μrest :=
        ⟨by
          simpa using (ENNReal.one_lt_top)⟩
      haveI : SFinite μrest := by
        infer_instance

      haveI : IsProbabilityMeasure γ := by
        dsimp [γ]
        infer_instance
      haveI : IsFiniteMeasure γ :=
        ⟨by
          simpa using (ENNReal.one_lt_top)⟩
      haveI : SFinite γ := by
        infer_instance

      let gL : (Fin (n + 1) → ℝ) → ℝ := fun x => x i * f x
      let gR : (Fin (n + 1) → ℝ) → ℝ := fun x => partialDeriv (n + 1) i f x

      have hcont_f : Continuous f := hf.continuous
      have hcont_gL : Continuous gL := by
        have hcoord : Continuous fun x : (Fin (n + 1) → ℝ) => x i := by fun_prop
        simpa [gL] using hcoord.mul hcont_f
      have hsupp_gL : HasCompactSupport gL := by
        have : HasCompactSupport (fun x : (Fin (n + 1) → ℝ) => f x * x i) :=
          hsupp.mul_right (f' := fun x : (Fin (n + 1) → ℝ) => x i)
        simpa [gL, mul_comm] using this
      have hgL_int : Integrable gL (gaussianStd (n + 1)) :=
        hcont_gL.integrable_of_hasCompactSupport hsupp_gL

      have hcont_gR : Continuous gR := by
        have h := hf.continuous_fderiv_apply (hn := le_rfl)
        have hx : Continuous (fun x : (Fin (n + 1) → ℝ) => (x, e (n + 1) i)) := by fun_prop
        simpa [gR, partialDeriv] using h.comp hx
      have hsupp_gR : HasCompactSupport gR := by
        simpa [gR, partialDeriv] using
          (hsupp.fderiv_apply (𝕜 := ℝ) (f := f) (v := e (n + 1) i))
      have hgR_int : Integrable gR (gaussianStd (n + 1)) :=
        hcont_gR.integrable_of_hasCompactSupport hsupp_gR

      let hLpair : (ℝ × (Fin n → ℝ)) → ℝ := gL ∘ split.symm
      let hRpair : (ℝ × (Fin n → ℝ)) → ℝ := gR ∘ split.symm

      have hLpair_int : Integrable hLpair (γ.prod μrest) := by
        simpa [hLpair] using
          (hmp.symm.integrable_comp_of_integrable (g := gL) hgL_int)

      have hRpair_int : Integrable hRpair (γ.prod μrest) := by
        simpa [hRpair] using
          (hmp.symm.integrable_comp_of_integrable (g := gR) hgR_int)

      have hL_rewrite :
          (∫ x, x i * f x ∂gaussianStd (n + 1)) =
            ∫ p, hLpair p ∂(γ.prod μrest) := by
        simpa [hLpair, gL] using
          (hmp.symm.integral_comp' (g := gL)).symm

      have hR_rewrite :
          (∫ x, partialDeriv (n + 1) i f x ∂gaussianStd (n + 1)) =
            ∫ p, hRpair p ∂(γ.prod μrest) := by
        simpa [hRpair, gR] using
          (hmp.symm.integral_comp' (g := gR)).symm

      rw [hL_rewrite, hR_rewrite]
      rw [MeasureTheory.integral_prod_symm (μ := γ) (ν := μrest) (f := hLpair) hLpair_int,
        MeasureTheory.integral_prod_symm (μ := γ) (ν := μrest) (f := hRpair) hRpair_int]
      refine integral_congr_ae (ae_of_all _ (fun y => ?_))

      have hv1 : (1 : NNReal) ≠ 0 := by simp
      let x0 : (Fin (n + 1) → ℝ) :=
        i.insertNth (α := fun _ : Fin (n + 1) => ℝ) (0 : ℝ) y
      let g : ℝ → ℝ := fun t => f (Function.update x0 i t)

      have hg_contdiff : ContDiff ℝ 1 g := by
        have hu : ContDiff ℝ 1 (Function.update x0 i) := by
          simpa using
            (contDiff_update (𝕜 := ℝ) (k := (1 : WithTop ℕ∞)) x0 i)
        simpa [g, Function.comp] using hf.comp hu

      have hg_supp : HasCompactSupport g := by
        have : HasCompactSupport (f ∘ Function.update x0 i) :=
          hsupp.comp_isClosedEmbedding (g := Function.update x0 i)
            (isClosedEmbedding_update x0 i)
        simpa [g, Function.comp] using this

      have hderiv :
          ∀ t, deriv g t = partialDeriv (n + 1) i f (Function.update x0 i t) := by
        intro t
        have hfderiv :
            HasFDerivAt f (fderiv ℝ f (Function.update x0 i t)) (Function.update x0 i t) :=
          (hf.differentiable le_rfl (Function.update x0 i t)).hasFDerivAt
        have hupd : HasDerivAt (Function.update x0 i) (Pi.single i (1 : ℝ)) t := by
          simpa using (hasDerivAt_update x0 i t)
        have hcomp :
            HasDerivAt (fun s : ℝ => f (Function.update x0 i s))
              ((fderiv ℝ f (Function.update x0 i t)) (Pi.single i (1 : ℝ))) t :=
          hfderiv.comp_hasDerivAt t hupd
        simpa [g, partialDeriv, e] using hcomp.deriv

      have hibp :
          (∫ t, t * f (i.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) ∂γ)
            = ∫ t, partialDeriv (n + 1) i f
                (i.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) ∂γ := by
        have hibp0 :=
          gaussianReal_ibp (μ := (0 : ℝ)) (v := (1 : NNReal)) hv1 (f := g) hg_contdiff hg_supp
        have hibp1 :
            (∫ t, t * f (i.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) ∂γ)
              = ∫ t, deriv g t ∂γ := by
          simpa [γ, g, x0, sub_zero, one_mul] using hibp0
        have hibp2 :
            (∫ t, deriv g t ∂γ)
              = ∫ t, partialDeriv (n + 1) i f (Function.update x0 i t) ∂γ := by
          refine integral_congr_ae (ae_of_all _ (fun t => ?_))
          simp [hderiv t]
        have hibp3 :
            (∫ t, partialDeriv (n + 1) i f (Function.update x0 i t) ∂γ)
              = ∫ t, partialDeriv (n + 1) i f
                  (i.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) ∂γ := by
          refine integral_congr_ae (ae_of_all _ (fun t => ?_))
          simp [x0]
        exact hibp1.trans (hibp2.trans hibp3)

      simpa [hLpair, hRpair, gL, gR, split, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv] using hibp



/-! 3) General covariance: pushforward by a matrix A -/

/-- Correlated Gaussian as the pushforward of the standard product Gaussian by `A`. -/
def gaussianLin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Measure (E n) :=
  Measure.map (fun z : E n => A.mulVec z) (gaussianStd n)

/-
Two key helper lemmas:

(1) Chain rule for the partials of `f ∘ (A.mulVec)`:
    ∂_k (f(Az)) = ∑ j, A j k * (∂_j f)(Az)

This is most convenient via `fderiv`:
  fderiv (fun z => f (A.mulVec z)) z
    = (fderiv f (A.mulVec z)).comp (A-as-continuous-linear-map)
then apply to basis vector `e k`.

(2) Covariance of coordinates under gaussianLin:
    Cov( (A z)_i, (A z)_j ) = ∑ k, A i k * A j k
This can be shown either:
  * directly from covariance bilinearity + `gaussianStd` independence,
  * or using `covarianceBilin_map` (Hilbert-space covariance bilinear form)
    and then specializing to basis vectors. The statement `covarianceBilin_map`
    is in `ProbabilityTheory.covarianceBilin_map`.
-/

/-- Chain rule for coordinate partialDeriv derivatives under a linear map given by a matrix. -/
lemma partial_comp_mulVec
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {f : E n → ℝ} (hf : ContDiff ℝ 1 f)
    (k : Fin n) (z : E n) :
    partialDeriv n k (fun z : E n => f (A.mulVec z)) z
      = ∑ j : Fin n, A j k * partialDeriv n j f (A.mulVec z) := by
  classical
  -- Continuous linear map representing `A.mulVec`.
  let L : E n →L[ℝ] E n := (A.mulVecLin).toContinuousLinearMap
  have hL : HasFDerivAt (fun x : E n => A.mulVec x) L z := by
    -- `L` has derivative itself, and its coercion is `A.mulVec`.
    simpa [L, Matrix.coe_mulVecLin] using (L.hasFDerivAt)

  have hfAt : HasFDerivAt f (fderiv ℝ f (A.mulVec z)) (A.mulVec z) :=
    (hf.differentiable le_rfl (A.mulVec z)).hasFDerivAt

  have hcomp :
      HasFDerivAt (fun x : E n => f (A.mulVec x))
        ((fderiv ℝ f (A.mulVec z)).comp L) z :=
    hfAt.comp z hL

  have hfd :
      fderiv ℝ (fun x : E n => f (A.mulVec x)) z
        = ((fderiv ℝ f (A.mulVec z)).comp L) :=
    hcomp.fderiv

  have hAk : A.mulVec (e n k) = A.col k := by
    simpa [e] using (Matrix.mulVec_single_one (M := A) k)

  have hcol : A.col k = ∑ j : Fin n, A j k • Pi.single (M := fun _ => ℝ) j 1 := by
    simpa [Matrix.col_apply] using (pi_eq_sum_univ' (x := A.col k))

  -- Evaluate the derivative in the direction `e n k` and expand.
  simp [partialDeriv, hfd, L, Matrix.coe_mulVecLin, hAk, hcol, smul_eq_mul, mul_assoc,
    mul_left_comm, mul_comm]

/-- Covariance entries of `gaussianLin A` in coordinates. -/
lemma covCoord_gaussianLin
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    covCoord n (gaussianLin A) i j
      = ∑ k : Fin n, A i k * A j k := by
  -- Skeleton options:
  --   Option 1: use `covarianceBilin_map` + orthonormal basis facts.
  --   Option 2: compute directly from `covariance` definition + linearity + iid covariances of gaussianStd.
  -- For Option 1, you will likely use:
  --   * `ProbabilityTheory.covarianceBilin_map` (in CovarianceBilin)
  --   * `ProbabilityTheory.covarianceBilin_apply_eq_cov` and evaluate at basis vectors
  --   * simp lemmas for `inner` with `EuclideanSpace.basisFun` and `Matrix.mulVec`
  classical
  unfold covCoord gaussianLin
  change
      cov[fun x : E n => x i, fun x : E n => x j;
          (gaussianStd n).map (fun z : E n => A.mulVec z)] =
        ∑ k : Fin n, A i k * A j k

  have hX :
      AEStronglyMeasurable (fun x : E n => x i) ((gaussianStd n).map (fun z : E n => A.mulVec z)) := by
    exact (measurable_pi_apply i).aestronglyMeasurable
  have hY :
      AEStronglyMeasurable (fun x : E n => x j) ((gaussianStd n).map (fun z : E n => A.mulVec z))
        := by
    exact (measurable_pi_apply j).aestronglyMeasurable
  have hZ : AEMeasurable (fun z : E n => A.mulVec z) (gaussianStd n) := by
    let L : E n →L[ℝ] E n := (A.mulVecLin).toContinuousLinearMap
    have : AEMeasurable (fun z : E n => L z) (gaussianStd n) := L.measurable.aemeasurable
    simpa [L, Matrix.coe_mulVecLin] using this
  rw [covariance_map (μ := gaussianStd n) (Z := fun z : E n => A.mulVec z)
    (X := fun x : E n => x i) (Y := fun x : E n => x j) hX hY hZ]

  -- Rewrite the pulled-back coordinate functions explicitly.
  change
      cov[fun z : E n => (A.mulVec z) i, fun z : E n => (A.mulVec z) j; gaussianStd n] =
        ∑ k : Fin n, A i k * A j k

  have hmp_eval : ∀ k : Fin n,
      MeasurePreserving (Function.eval k) (gaussianStd n) (gaussianReal (0 : ℝ) (1 : NNReal)) := by
    intro k
    simpa [gaussianStd] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin n => gaussianReal (0 : ℝ) (1 : NNReal)) k)

  have hmem_coord : ∀ k : Fin n, MemLp (fun z : E n => z k) 2 (gaussianStd n) := by
    intro k
    have hid : MemLp (id : ℝ → ℝ) 2 (gaussianReal (0 : ℝ) (1 : NNReal)) := by
      simpa using
        (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : NNReal)) (p := (2 : ENNReal))
          (by simp))
    have hid' : MemLp (id : ℝ → ℝ) 2 ((gaussianStd n).map (Function.eval k)) := by
      simpa [(hmp_eval k).map_eq] using hid
    have hcomp : MemLp ((id : ℝ → ℝ) ∘ Function.eval k) 2 (gaussianStd n) :=
      (memLp_map_measure_iff (μ := gaussianStd n) (f := Function.eval k) (g := (id : ℝ → ℝ))
        (p := (2 : ENNReal))
        (hg :=
          (aestronglyMeasurable_id :
            AEStronglyMeasurable (id : ℝ → ℝ) ((gaussianStd n).map (Function.eval k))))
        (hf := (measurable_pi_apply k).aemeasurable)).1 hid'
    simpa using hcomp

  have hcov_coord :
      ∀ k l : Fin n,
        cov[fun z : E n => z k, fun z : E n => z l; gaussianStd n] =
          (if k = l then (1 : ℝ) else 0) := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      have hmeas : AEMeasurable (fun z : E n => z k) (gaussianStd n) :=
        (measurable_pi_apply k).aemeasurable
      have hcov :
          cov[fun z : E n => z k, fun z : E n => z k; gaussianStd n] =
            Var[fun z : E n => z k; gaussianStd n] := by
        simpa using (covariance_self (μ := gaussianStd n) (X := fun z : E n => z k) hmeas)
      have hvar : Var[fun z : E n => z k; gaussianStd n] = (1 : NNReal) := by
        have h :=
          MeasureTheory.MeasurePreserving.variance_fun_comp (μ := gaussianStd n)
            (ν := gaussianReal (0 : ℝ) (1 : NNReal)) (X := Function.eval k) (hmp_eval k)
            (f := (id : ℝ → ℝ)) (hf := measurable_id.aemeasurable)
        exact (by simpa using (h.trans (by simp)))
      simpa [hcov, hvar]
    · have hindep_family :
            iIndepFun (fun k : Fin n => fun z : E n => z k) (gaussianStd n) := by
          have mid :
              ∀ k : Fin n, AEMeasurable (id : ℝ → ℝ) (gaussianReal (0 : ℝ) (1 : NNReal)) := by
            intro k
            simpa using (measurable_id.aemeasurable)
          simpa [gaussianStd] using
            (iIndepFun_pi (μ := fun _ : Fin n => gaussianReal (0 : ℝ) (1 : NNReal))
              (X := fun _ : Fin n => (id : ℝ → ℝ)) mid)
      have hindep : (fun z : E n => z k) ⟂ᵢ[gaussianStd n] (fun z : E n => z l) :=
        hindep_family.indepFun hkl
      have hzero :
          cov[fun z : E n => z k, fun z : E n => z l; gaussianStd n] = 0 := by
        exact hindep.covariance_eq_zero (hmem_coord k) (hmem_coord l)
      simpa [hkl, hzero]

  have hmul_i : (fun z : E n => (A.mulVec z) i) = fun z : E n => ∑ k : Fin n, A i k * z k := by
    funext z
    simp [Matrix.mulVec, dotProduct]
  have hmul_j : (fun z : E n => (A.mulVec z) j) = fun z : E n => ∑ k : Fin n, A j k * z k := by
    funext z
    simp [Matrix.mulVec, dotProduct]
  rw [hmul_i, hmul_j]

  haveI : IsFiniteMeasure (gaussianStd n) := by
    dsimp [gaussianStd]
    infer_instance

  have hsum :=
    covariance_fun_sum_fun_sum (μ := gaussianStd n)
      (X := fun k : Fin n => fun z : E n => A i k * z k)
      (Y := fun l : Fin n => fun z : E n => A j l * z l)
      (fun k => (hmem_coord k).const_mul (A i k))
      (fun l => (hmem_coord l).const_mul (A j l))
  rw [hsum]
  simp [covariance_const_mul_left, covariance_const_mul_right, hcov_coord, mul_assoc, mul_left_comm,
    mul_comm, eq_comm]

/-- Full coordinate Stein identity for the correlated Gaussian `gaussianLin A`. -/
theorem gaussianLin_ibp_coord
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    {f : E n → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) :
    (∫ x, x i * f x ∂gaussianLin A)
      = ∑ j : Fin n,
          (covCoord n (gaussianLin A) i j) * (∫ x, partialDeriv n j f x ∂gaussianLin A) := by
  classical
  cases n with
  | zero =>
      cases i with
      | mk val isLt =>
          cases isLt
  | succ n =>
      haveI : IsProbabilityMeasure (gaussianStd (n + 1)) := by
        dsimp [gaussianStd]
        infer_instance
      haveI : IsFiniteMeasure (gaussianStd (n + 1)) := ⟨by
        simpa using (ENNReal.one_lt_top)⟩

      let γ : Measure ℝ := gaussianReal (0 : ℝ) (1 : NNReal)

      have hA_meas :
          AEMeasurable (fun z : E (n + 1) => A.mulVec z) (gaussianStd (n + 1)) := by
        let L : E (n + 1) →L[ℝ] E (n + 1) := (A.mulVecLin).toContinuousLinearMap
        have : AEMeasurable (fun z : E (n + 1) => L z) (gaussianStd (n + 1)) :=
          L.measurable.aemeasurable
        simpa [L, Matrix.coe_mulVecLin] using this

      have hmeasA : Measurable (fun z : E (n + 1) => A.mulVec z) := by
        let L : E (n + 1) →L[ℝ] E (n + 1) := (A.mulVecLin).toContinuousLinearMap
        simpa [L, Matrix.coe_mulVecLin] using L.measurable

      have hcont_partial :
          ∀ j : Fin (n + 1), Continuous fun x : E (n + 1) => partialDeriv (n + 1) j f x := by
        intro j
        have h := hf.continuous_fderiv_apply (hn := le_rfl)
        have hx : Continuous (fun x : E (n + 1) => (x, e (n + 1) j)) := by fun_prop
        simpa [partialDeriv] using h.comp hx

      have hbound_f : ∃ C : ℝ, ∀ x : E (n + 1), ‖f x‖ ≤ C := by
        have hcont_norm : Continuous fun x : E (n + 1) => ‖f x‖ :=
          continuous_norm.comp hf.continuous
        obtain ⟨x0, hx0⟩ := hcont_norm.exists_forall_ge_of_hasCompactSupport hsupp.norm
        refine ⟨‖f x0‖, ?_⟩
        intro x
        simpa using hx0 x

      have hbound_partial :
          ∀ j : Fin (n + 1), ∃ C : ℝ, ∀ x : E (n + 1), ‖partialDeriv (n + 1) j f x‖ ≤ C := by
        intro j
        have hsupp' : HasCompactSupport (fun x : E (n + 1) => partialDeriv (n + 1) j f x) := by
          simpa [partialDeriv] using
            (hsupp.fderiv_apply (𝕜 := ℝ) (f := f) (v := e (n + 1) j))
        have hcont_norm : Continuous fun x : E (n + 1) => ‖partialDeriv (n + 1) j f x‖ :=
          continuous_norm.comp (hcont_partial j)
        obtain ⟨x0, hx0⟩ := hcont_norm.exists_forall_ge_of_hasCompactSupport hsupp'.norm
        refine ⟨‖partialDeriv (n + 1) j f x0‖, ?_⟩
        intro x
        simpa using hx0 x

      have hmp_eval :
          ∀ k : Fin (n + 1),
            MeasurePreserving (Function.eval k) (gaussianStd (n + 1)) γ := by
        intro k
        simpa [gaussianStd, γ] using
          (MeasureTheory.measurePreserving_eval
            (μ := fun _ : Fin (n + 1) => gaussianReal (0 : ℝ) (1 : NNReal)) k)

      have hid_int : Integrable (id : ℝ → ℝ) γ := by
        haveI : IsProbabilityMeasure γ := by
          dsimp [γ]
          infer_instance
        haveI : IsFiniteMeasure γ := ⟨by
          simpa using (ENNReal.one_lt_top)⟩
        have hid_mem : MemLp (id : ℝ → ℝ) 2 γ := by
          simpa [γ] using
            (memLp_id_gaussianReal'
              (μ := (0 : ℝ)) (v := (1 : NNReal)) (p := (2 : ENNReal)) (by simp))
        have hq1 : (1 : ENNReal) ≤ (2 : ENNReal) := by simp
        exact (hid_mem.integrable (μ := γ) (hq1 := hq1))

      have hcoord_int :
          ∀ k : Fin (n + 1), Integrable (fun z : E (n + 1) => z k) (gaussianStd (n + 1)) := by
        intro k
        have := (hmp_eval k).integrable_comp_of_integrable (g := (id : ℝ → ℝ)) hid_int
        simpa [Function.comp] using this

      have hL_rewrite :
          (∫ x, x i * f x ∂gaussianLin A) =
            ∫ z, (A.mulVec z) i * f (A.mulVec z) ∂gaussianStd (n + 1) := by
        dsimp [gaussianLin]
        have hmeas : Measurable (fun x : E (n + 1) => x i * f x) := by
          have hcoord : Measurable fun x : E (n + 1) => x i := measurable_pi_apply i
          have hfmeas : Measurable f := hf.continuous.measurable
          simpa using hcoord.mul hfmeas
        have hfm :
            AEStronglyMeasurable (fun x : E (n + 1) => x i * f x)
              ((gaussianStd (n + 1)).map (fun z : E (n + 1) => A.mulVec z)) :=
          (hmeas.aemeasurable).aestronglyMeasurable
        simpa using
          (MeasureTheory.integral_map (μ := gaussianStd (n + 1))
            (φ := fun z : E (n + 1) => A.mulVec z) hA_meas
            (f := fun x : E (n + 1) => x i * f x) hfm)

      have hR_rewrite :
          ∀ j : Fin (n + 1),
            (∫ x, partialDeriv (n + 1) j f x ∂gaussianLin A) =
              ∫ z, partialDeriv (n + 1) j f (A.mulVec z) ∂gaussianStd (n + 1) := by
        intro j
        dsimp [gaussianLin]
        have hmeas : Measurable (fun x : E (n + 1) => partialDeriv (n + 1) j f x) :=
          (hcont_partial j).measurable
        have hfm :
            AEStronglyMeasurable (fun x : E (n + 1) => partialDeriv (n + 1) j f x)
              ((gaussianStd (n + 1)).map (fun z : E (n + 1) => A.mulVec z)) :=
          (hmeas.aemeasurable).aestronglyMeasurable
        simpa using
          (MeasureTheory.integral_map (μ := gaussianStd (n + 1))
            (φ := fun z : E (n + 1) => A.mulVec z) hA_meas
            (f := fun x : E (n + 1) => partialDeriv (n + 1) j f x) hfm)

      have hibp_comp :
          ∀ k : Fin (n + 1),
            (∫ z, z k * f (A.mulVec z) ∂gaussianStd (n + 1)) =
              ∫ z, partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z)) z
                ∂gaussianStd (n + 1) := by
        intro k
        let μrest : Measure (Fin n → ℝ) := gaussianStd n
        let split : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
          MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
        have hmp :
            MeasurePreserving split (gaussianStd (n + 1)) (γ.prod μrest) := by
          simpa [split, γ, μrest, gaussianStd] using
            (measurePreserving_piFinSuccAbove
              (α := fun _ : Fin (n + 1) => ℝ)
              (μ := fun _ : Fin (n + 1) => gaussianReal (0 : ℝ) (1 : NNReal)) k)

        haveI : IsProbabilityMeasure μrest := by
          dsimp [μrest, gaussianStd]
          infer_instance
        haveI : IsFiniteMeasure μrest := ⟨by
          simpa using (ENNReal.one_lt_top)⟩
        haveI : SFinite μrest := by
          infer_instance
        haveI : IsProbabilityMeasure γ := by
          dsimp [γ]
          infer_instance
        haveI : IsFiniteMeasure γ := ⟨by
          simpa using (ENNReal.one_lt_top)⟩
        haveI : SFinite γ := by
          infer_instance

        let gL : E (n + 1) → ℝ := fun x => x k * f (A.mulVec x)
        let gR : E (n + 1) → ℝ := fun x => partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z)) x

        obtain ⟨Cf, hCf⟩ := hbound_f
        have hg_as : AEStronglyMeasurable (fun x : E (n + 1) => f (A.mulVec x)) (gaussianStd (n + 1)) := by
          have hmeas : Measurable (fun x : E (n + 1) => f (A.mulVec x)) :=
            hf.continuous.measurable.comp hmeasA
          exact (hmeas.aemeasurable).aestronglyMeasurable
        have hg_bound : ∀ᵐ x ∂gaussianStd (n + 1), ‖f (A.mulVec x)‖ ≤ Cf :=
          ae_of_all _ (fun x => hCf (A.mulVec x))

        have hgL_int : Integrable gL (gaussianStd (n + 1)) := by
          have hz_int : Integrable (fun x : E (n + 1) => x k) (gaussianStd (n + 1)) := hcoord_int k
          simpa [gL] using
            (Integrable.mul_bdd (μ := gaussianStd (n + 1))
              (f := fun x : E (n + 1) => x k) (g := fun x : E (n + 1) => f (A.mulVec x))
              hz_int hg_as hg_bound)

        have hgR_int : Integrable gR (gaussianStd (n + 1)) := by
          have hchain :
              gR = fun x : E (n + 1) => ∑ j : Fin (n + 1), A j k * partialDeriv (n + 1) j f (A.mulVec x) := by
            funext x
            simpa [gR] using (partial_comp_mulVec A hf k x)
          have hterm_int :
              ∀ j : Fin (n + 1),
                Integrable (fun x : E (n + 1) => A j k * partialDeriv (n + 1) j f (A.mulVec x))
                  (gaussianStd (n + 1)) := by
            intro j
            obtain ⟨Cj, hCj⟩ := hbound_partial j
            have hmeas : Measurable (fun x : E (n + 1) => partialDeriv (n + 1) j f (A.mulVec x)) :=
              (hcont_partial j).measurable.comp hmeasA
            have hassm : AEStronglyMeasurable (fun x : E (n + 1) => partialDeriv (n + 1) j f (A.mulVec x))
                (gaussianStd (n + 1)) := (hmeas.aemeasurable).aestronglyMeasurable
            have hbd : ∀ᵐ x ∂gaussianStd (n + 1), ‖partialDeriv (n + 1) j f (A.mulVec x)‖ ≤ Cj :=
              ae_of_all _ (fun x => hCj (A.mulVec x))
            have hint : Integrable (fun x : E (n + 1) => partialDeriv (n + 1) j f (A.mulVec x))
                (gaussianStd (n + 1)) :=
              Integrable.of_bound (μ := gaussianStd (n + 1)) hassm Cj hbd
            simpa [mul_assoc] using (hint.const_mul (A j k))

          have hsum_int :
              Integrable (fun x : E (n + 1) => ∑ j : Fin (n + 1), A j k * partialDeriv (n + 1) j f (A.mulVec x))
                (gaussianStd (n + 1)) := by
            classical
            have hsum_int' :
                Integrable
                  (fun x : E (n + 1) =>
                    (Finset.univ : Finset (Fin (n + 1))).sum
                      (fun j : Fin (n + 1) => A j k * partialDeriv (n + 1) j f (A.mulVec x)))
                  (gaussianStd (n + 1)) := by
              refine integrable_finset_sum (μ := gaussianStd (n + 1))
                (s := (Finset.univ : Finset (Fin (n + 1))))
                (f := fun j x => A j k * partialDeriv (n + 1) j f (A.mulVec x)) ?_
              intro j _
              simpa using hterm_int j
            simpa using hsum_int'
          -- convert using the chain rule
          rw [hchain]
          exact hsum_int
        let hLpair : (ℝ × (Fin n → ℝ)) → ℝ := gL ∘ split.symm
        let hRpair : (ℝ × (Fin n → ℝ)) → ℝ := gR ∘ split.symm

        have hLpair_int : Integrable hLpair (γ.prod μrest) := by
          simpa [hLpair] using
            (hmp.symm.integrable_comp_of_integrable (g := gL) hgL_int)
        have hRpair_int : Integrable hRpair (γ.prod μrest) := by
          simpa [hRpair] using
            (hmp.symm.integrable_comp_of_integrable (g := gR) hgR_int)

        have hL_rewrite' :
            (∫ x, x k * f (A.mulVec x) ∂gaussianStd (n + 1)) =
              ∫ p, hLpair p ∂(γ.prod μrest) := by
          simpa [hLpair, gL] using
            (hmp.symm.integral_comp' (g := gL)).symm

        have hR_rewrite' :
            (∫ x, partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z)) x ∂gaussianStd (n + 1)) =
              ∫ p, hRpair p ∂(γ.prod μrest) := by
          simpa [hRpair, gR] using
            (hmp.symm.integral_comp' (g := gR)).symm

        rw [hL_rewrite', hR_rewrite']
        rw [MeasureTheory.integral_prod_symm (μ := γ) (ν := μrest) (f := hLpair) hLpair_int,
          MeasureTheory.integral_prod_symm (μ := γ) (ν := μrest) (f := hRpair) hRpair_int]
        refine integral_congr_ae (ae_of_all _ (fun y => ?_))

        have hv1 : (1 : NNReal) ≠ 0 := by simp
        let x0 : E (n + 1) :=
          k.insertNth (α := fun _ : Fin (n + 1) => ℝ) (0 : ℝ) y
        let g : ℝ → ℝ := fun t => f (A.mulVec (Function.update x0 k t))

        have hg_contdiff : ContDiff ℝ 1 g := by
          have hu : ContDiff ℝ 1 (Function.update x0 k) := by
            simpa using
              (contDiff_update (𝕜 := ℝ) (k := (1 : WithTop ℕ∞)) x0 k)
          let L : E (n + 1) →L[ℝ] E (n + 1) := (A.mulVecLin).toContinuousLinearMap
          have hA : ContDiff ℝ 1 (fun z : E (n + 1) => A.mulVec z) := by
            simpa [L, Matrix.coe_mulVecLin] using (L.contDiff : ContDiff ℝ 1 L)
          have hcomp : ContDiff ℝ 1 (fun t : ℝ => A.mulVec (Function.update x0 k t)) := by
            simpa [Function.comp] using hA.comp hu
          simpa [g, Function.comp] using hf.comp hcomp

        have hx0k : x0 k = 0 := by
          simp [x0]

        have hupdate_eq : ∀ t : ℝ, Function.update x0 k t = x0 + t • e (n + 1) k := by
          intro t
          ext j
          by_cases hj : j = k
          · subst hj
            simp [Function.update, e, hx0k]
          · simp [Function.update, e, hj]

        have hmul_update : ∀ t : ℝ, A.mulVec (Function.update x0 k t) = A.mulVec x0 + t • A.col k := by
          intro t
          have ht : Function.update x0 k t = x0 + t • e (n + 1) k := hupdate_eq t
          calc
            A.mulVec (Function.update x0 k t)
                = A.mulVec (x0 + t • e (n + 1) k) := by simpa [ht]
            _ = A.mulVec x0 + A.mulVec (t • e (n + 1) k) := by
                simpa using (Matrix.mulVec_add (A := A) x0 (t • e (n + 1) k))
            _ = A.mulVec x0 + t • A.mulVec (e (n + 1) k) := by
                simp [Matrix.mulVec_smul]
            _ = A.mulVec x0 + t • A.col k := by
                simpa [e] using congrArg (fun v => A.mulVec x0 + t • v)
                  (Matrix.mulVec_single_one (M := A) k)

        have hderiv :
            ∀ t, deriv g t =
              partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z)) (Function.update x0 k t) := by
          intro t
          let F : E (n + 1) → ℝ := fun z => f (A.mulVec z)
          let L : E (n + 1) →L[ℝ] E (n + 1) := (A.mulVecLin).toContinuousLinearMap
          have hA : ContDiff ℝ 1 (fun z : E (n + 1) => A.mulVec z) := by
            simpa [L, Matrix.coe_mulVecLin] using (L.contDiff : ContDiff ℝ 1 L)
          have hFcd : ContDiff ℝ 1 F := by
            simpa [F, Function.comp] using hf.comp hA
          have hFderiv :
              HasFDerivAt F (fderiv ℝ F (Function.update x0 k t)) (Function.update x0 k t) :=
            (hFcd.differentiable le_rfl (Function.update x0 k t)).hasFDerivAt
          have hupd : HasDerivAt (Function.update x0 k) (Pi.single k (1 : ℝ)) t := by
            simpa using (hasDerivAt_update x0 k t)
          have hcomp :
              HasDerivAt (fun s : ℝ => F (Function.update x0 k s))
                ((fderiv ℝ F (Function.update x0 k t)) (Pi.single k (1 : ℝ))) t :=
            hFderiv.comp_hasDerivAt t hupd
          simpa [g, F, partialDeriv, e] using hcomp.deriv

        by_cases hk0 : A.col k = 0
        · have hAk : ∀ j : Fin (n + 1), A j k = 0 := by
            intro j
            have := congrArg (fun v : Fin (n + 1) → ℝ => v j) hk0
            simpa [Matrix.col_apply] using this
          have hibp :
              (∫ t, t * f (A.mulVec (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y)) ∂γ)
                =
                ∫ t,
                  partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z))
                    (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) ∂γ := by
            have hmean : (∫ t : ℝ, t ∂γ) = 0 := by
              simp [γ]
            have hconst : ∀ t : ℝ, A.mulVec (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) = A.mulVec x0 := by
              intro t
              -- use the update representation and `hmul_update`
              have : A.mulVec (Function.update x0 k t) = A.mulVec x0 := by
                simpa [hmul_update t, hk0] using (hmul_update t)
              simpa [x0] using this
            have hderiv0 : ∀ t : ℝ,
                partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z))
                  (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) = 0 := by
              intro t
              simpa [x0, hAk] using (partial_comp_mulVec A hf k (Function.update x0 k t))
            -- both sides are zero
            have hL0 : (∫ t, t * f (A.mulVec (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y)) ∂γ) = 0 := by
              calc
                (∫ t, t * f (A.mulVec (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y)) ∂γ)
                    = (∫ t : ℝ, t * f (A.mulVec x0) ∂γ) := by
                        refine integral_congr_ae (ae_of_all _ (fun t => ?_))
                        simp [hconst t]
                _ = (∫ t : ℝ, t ∂γ) * f (A.mulVec x0) := by
                        simpa using
                          (MeasureTheory.integral_mul_const (μ := γ) (r := f (A.mulVec x0)) (f := fun t : ℝ => t))
                _ = 0 := by simp [hmean]
            have hR0 : (∫ t, partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z))
                    (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) ∂γ) = 0 := by
              have hR0' :
                  (∫ t, partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z))
                      (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) ∂γ)
                    = ∫ t, (0 : ℝ) ∂γ := by
                refine MeasureTheory.integral_congr_ae (ae_of_all _ (fun t => ?_))
                simp [hderiv0 t]
              simpa using hR0'.trans (by simp)
            simpa [hL0, hR0]

          simpa [hLpair, hRpair, gL, gR, split, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv] using hibp

        · have hg_supp : HasCompactSupport g := by
            have hsmul : Topology.IsClosedEmbedding (fun t : ℝ => t • A.col k) :=
              isClosedEmbedding_smul_left (hc := hk0)
            have hadd : Topology.IsClosedEmbedding (fun x : E (n + 1) => A.mulVec x0 + x) :=
              (Homeomorph.addLeft (A.mulVec x0)).isClosedEmbedding
            have hline : Topology.IsClosedEmbedding (fun t : ℝ => A.mulVec x0 + t • A.col k) := by
              simpa [Function.comp] using
                (Topology.IsClosedEmbedding.comp (g := fun x : E (n + 1) => A.mulVec x0 + x)
                  (f := fun t : ℝ => t • A.col k) hadd hsmul)
            have : HasCompactSupport (f ∘ fun t : ℝ => A.mulVec x0 + t • A.col k) :=
              hsupp.comp_isClosedEmbedding (g := fun t : ℝ => A.mulVec x0 + t • A.col k) hline
            simpa [g, Function.comp, hmul_update] using this

          have hibp0 :=
            gaussianReal_ibp (μ := (0 : ℝ)) (v := (1 : NNReal)) hv1 (f := g) hg_contdiff hg_supp

          have hibp1 :
              (∫ t, t * f (A.mulVec (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y)) ∂γ)
                = ∫ t, deriv g t ∂γ := by
            simpa [γ, g, x0, sub_zero, one_mul] using hibp0

          have hibp2 :
              (∫ t, deriv g t ∂γ)
                =
                  ∫ t,
                    partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z))
                      (Function.update x0 k t) ∂γ := by
            refine integral_congr_ae (ae_of_all _ (fun t => ?_))
            simp [hderiv t]

          have hibp3 :
              (∫ t,
                    partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z))
                      (Function.update x0 k t) ∂γ)
                =
                  ∫ t,
                    partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z))
                      (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) ∂γ := by
            refine integral_congr_ae (ae_of_all _ (fun t => ?_))
            simp [x0]

          have hibp :
              (∫ t, t * f (A.mulVec (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y)) ∂γ)
                =
                  ∫ t,
                    partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z))
                      (k.insertNth (α := fun _ : Fin (n + 1) => ℝ) t y) ∂γ :=
            hibp1.trans (hibp2.trans hibp3)

          simpa [hLpair, hRpair, gL, gR, split, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv] using hibp

      rw [hL_rewrite]
      simp [hR_rewrite, covCoord_gaussianLin]

      have hmul_i : (fun z : E (n + 1) => (A.mulVec z) i) = fun z : E (n + 1) => ∑ k : Fin (n + 1), A i k * z k := by
        funext z
        simp [Matrix.mulVec, dotProduct]

      have hmul_i_val :
          ∀ z : E (n + 1), (A.mulVec z) i = ∑ k : Fin (n + 1), A i k * z k := by
        intro z
        simpa using congrArg (fun g => g z) hmul_i

      have hL_mul :
          (∫ z, (A.mulVec z) i * f (A.mulVec z) ∂gaussianStd (n + 1))
            = ∫ z, (∑ k : Fin (n + 1), A i k * z k) * f (A.mulVec z) ∂gaussianStd (n + 1) := by
        refine integral_congr_ae (ae_of_all _ (fun z => ?_))
        simp [hmul_i_val z]

      rw [hL_mul]
      let μ : Measure (E (n + 1)) := gaussianStd (n + 1)

      haveI : IsFiniteMeasure μ := by
        dsimp [μ]
        infer_instance

      obtain ⟨Cf, hCf⟩ := hbound_f
      have hf_as : AEStronglyMeasurable (fun z : E (n + 1) => f (A.mulVec z)) μ := by
        have hmeas : Measurable (fun z : E (n + 1) => f (A.mulVec z)) :=
          hf.continuous.measurable.comp hmeasA
        exact (hmeas.aemeasurable).aestronglyMeasurable
      have hf_bd : ∀ᵐ z ∂μ, ‖f (A.mulVec z)‖ ≤ Cf :=
        ae_of_all _ (fun z => hCf (A.mulVec z))

      have hzk_int :
          ∀ k : Fin (n + 1), Integrable (fun z : E (n + 1) => z k * f (A.mulVec z)) μ := by
        intro k
        have hz_int : Integrable (fun z : E (n + 1) => z k) μ := by
          simpa [μ] using hcoord_int k
        simpa [μ] using
          (Integrable.mul_bdd (μ := μ) (f := fun z : E (n + 1) => z k)
            (g := fun z : E (n + 1) => f (A.mulVec z)) hz_int hf_as hf_bd)

      have hterm_int :
          ∀ k : Fin (n + 1), Integrable (fun z : E (n + 1) => (A i k * z k) * f (A.mulVec z)) μ := by
        intro k
        have hk : Integrable (fun z : E (n + 1) => z k * f (A.mulVec z)) μ := hzk_int k
        simpa [mul_assoc] using hk.const_mul (A i k)

      have hL_sum :
          (∫ z, (∑ k : Fin (n + 1), A i k * z k) * f (A.mulVec z) ∂μ)
            = ∑ k : Fin (n + 1), A i k * (∫ z, z k * f (A.mulVec z) ∂μ) := by
        classical
        calc
          (∫ z, (∑ k : Fin (n + 1), A i k * z k) * f (A.mulVec z) ∂μ)
              = ∫ z, ∑ k : Fin (n + 1), (A i k * z k) * f (A.mulVec z) ∂μ := by
                  refine integral_congr_ae (ae_of_all _ (fun z => ?_))
                  simp [ Finset.sum_mul, mul_assoc]
          _ = ∑ k : Fin (n + 1), ∫ z, (A i k * z k) * f (A.mulVec z) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_finset_sum (μ := μ) (s := (Finset.univ : Finset (Fin (n + 1))))
                      (f := fun k z => (A i k * z k) * f (A.mulVec z)) (by
                        intro k _
                        simpa using hterm_int k))
          _ = ∑ k : Fin (n + 1), A i k * (∫ z, z k * f (A.mulVec z) ∂μ) := by
                  -- rewrite each term
                  classical
                  -- turn into a finset sum
                  simp [ mul_assoc, MeasureTheory.integral_const_mul]

      have hL_ibp :
          ∑ k : Fin (n + 1), A i k * (∫ z, z k * f (A.mulVec z) ∂μ)
            = ∑ k : Fin (n + 1), A i k * (∫ z,
                partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z)) z ∂μ) := by
        classical
        simp [μ, hibp_comp]

      have hchain_int :
          ∀ k : Fin (n + 1),
            (∫ z,
                partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z)) z ∂μ)
              =
                ∑ j : Fin (n + 1),
                  A j k * (∫ z, partialDeriv (n + 1) j f (A.mulVec z) ∂μ) := by
        intro k
        have hchain :
            (fun z : E (n + 1) => partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z)) z)
              = fun z : E (n + 1) => ∑ j : Fin (n + 1), A j k * partialDeriv (n + 1) j f (A.mulVec z) := by
            funext z
            simpa using (partial_comp_mulVec A hf k z)

        have hterm_int' : ∀ j : Fin (n + 1),
            Integrable (fun z : E (n + 1) => A j k * partialDeriv (n + 1) j f (A.mulVec z)) μ := by
          intro j
          obtain ⟨Cj, hCj⟩ := hbound_partial j
          have hmeas : Measurable (fun z : E (n + 1) => partialDeriv (n + 1) j f (A.mulVec z)) :=
            (hcont_partial j).measurable.comp hmeasA
          have hassm : AEStronglyMeasurable (fun z : E (n + 1) => partialDeriv (n + 1) j f (A.mulVec z)) μ :=
            (hmeas.aemeasurable).aestronglyMeasurable
          have hbd : ∀ᵐ z ∂μ, ‖partialDeriv (n + 1) j f (A.mulVec z)‖ ≤ Cj :=
            ae_of_all _ (fun z => hCj (A.mulVec z))
          have hint : Integrable (fun z : E (n + 1) => partialDeriv (n + 1) j f (A.mulVec z)) μ :=
            Integrable.of_bound (μ := μ) hassm Cj hbd
          simpa [mul_assoc] using (hint.const_mul (A j k))

        calc
          (∫ z,
              partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z)) z ∂μ)
              = ∫ z, ∑ j : Fin (n + 1), A j k * partialDeriv (n + 1) j f (A.mulVec z) ∂μ := by
                  rw [hchain]
          _ = ∑ j : Fin (n + 1), ∫ z, A j k * partialDeriv (n + 1) j f (A.mulVec z) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_finset_sum (μ := μ) (s := (Finset.univ : Finset (Fin (n + 1))))
                      (f := fun j z => A j k * partialDeriv (n + 1) j f (A.mulVec z)) (by
                        intro j _
                        simpa using hterm_int' j))
          _ = ∑ j : Fin (n + 1), A j k * (∫ z, partialDeriv (n + 1) j f (A.mulVec z) ∂μ) := by
                  classical
                  simp [ MeasureTheory.integral_const_mul]

      calc
        (∫ z, (∑ k : Fin (n + 1), A i k * z k) * f (A.mulVec z) ∂μ)
            = ∑ k : Fin (n + 1), A i k * (∫ z, z k * f (A.mulVec z) ∂μ) := hL_sum
        _ = ∑ k : Fin (n + 1), A i k * (∫ z,
                partialDeriv (n + 1) k (fun z : E (n + 1) => f (A.mulVec z)) z ∂μ) := hL_ibp
        _ = ∑ k : Fin (n + 1), A i k * (∑ j : Fin (n + 1),
                A j k * (∫ z, partialDeriv (n + 1) j f (A.mulVec z) ∂μ)) := by
              classical
              simp [hchain_int]
        _ = ∑ j : Fin (n + 1), (∑ k : Fin (n + 1), A i k * A j k) * (∫ z, partialDeriv (n + 1) j f (A.mulVec z) ∂μ) := by
              classical
              simp [Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
              calc
                (∑ x : Fin (n + 1), ∑ i_1 : Fin (n + 1),
                    A i x *
                      (A i_1 x * (∫ (z : E (n + 1)), partialDeriv (n + 1) i_1 f (A.mulVec z) ∂μ)))
                    = ∑ i_1 : Fin (n + 1), ∑ x : Fin (n + 1),
                        A i x *
                          (A i_1 x * (∫ (z : E (n + 1)), partialDeriv (n + 1) i_1 f (A.mulVec z) ∂μ)) := by
                    simpa using (Finset.sum_comm :
                      (∑ x ∈ (Finset.univ : Finset (Fin (n + 1))),
                        ∑ i_1 ∈ (Finset.univ : Finset (Fin (n + 1))),
                          A i x *
                            (A i_1 x * (∫ (z : E (n + 1)), partialDeriv (n + 1) i_1 f (A.mulVec z) ∂μ)))
                        =
                      ∑ i_1 ∈ (Finset.univ : Finset (Fin (n + 1))),
                        ∑ x ∈ (Finset.univ : Finset (Fin (n + 1))),
                          A i x *
                            (A i_1 x * (∫ (z : E (n + 1)), partialDeriv (n + 1) i_1 f (A.mulVec z) ∂μ)))
                _ = ∑ x : Fin (n + 1), ∑ x_1 : Fin (n + 1),
                      A i x_1 *
                        (A x x_1 * (∫ (z : E (n + 1)), partialDeriv (n + 1) x f (A.mulVec z) ∂μ)) := by
                    simpa [mul_assoc, mul_left_comm, mul_comm]



end

end ProbabilityTheory
