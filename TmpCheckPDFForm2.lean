import Mathlib

open scoped BigOperators NNReal

namespace Scratch

open ProbabilityTheory

example (x : ℝ) :
    gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x = (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  simp [gaussianPDFReal_def]
  ring_nf
  simp

end Scratch
