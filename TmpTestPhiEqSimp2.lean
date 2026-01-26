import Mathlib

open scoped NNReal

namespace Scratch

noncomputable section

def φ (x : ℝ) : ℝ := Real.exp (-(x^2)/2) / Real.sqrt (2 * Real.pi)

lemma φ_eq_gaussianPDFReal : φ = ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) := by
  funext x
  simp [φ, ProbabilityTheory.gaussianPDFReal_def, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end

end Scratch