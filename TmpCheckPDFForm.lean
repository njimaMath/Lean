import Mathlib

open scoped BigOperators NNReal

namespace Scratch

open ProbabilityTheory

example (x : ℝ) :
    gaussianPDFReal (0 : ℝ) (1 : ℝ≥0) x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  -- unfold and simplify manually
  simp [gaussianPDFReal_def]
  ring

end Scratch
