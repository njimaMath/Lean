import Mathlib
import perceptronFixed.GIP.GIP

open scoped NNReal

namespace Scratch

noncomputable section

def φ (x : ℝ) : ℝ := Real.exp (-(x^2)/2) / Real.sqrt (2 * Real.pi)

lemma φ_eq_gaussianPDFReal : φ = ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) := by
  funext x
  simp [φ, ProbabilityTheory.gaussianPDFReal_def, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

lemma deriv_φ (x : ℝ) : deriv φ x = -x * φ x := by
  have hv : (1 : ℝ≥0) ≠ 0 := by simp
  -- rewrite `φ` as the Gaussian pdf
  rw [φ_eq_gaussianPDFReal]
  have h := congrArg (fun f => f x)
    (ProbabilityTheory.deriv_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) hv)
  -- simplify
  simpa using h

end

end Scratch