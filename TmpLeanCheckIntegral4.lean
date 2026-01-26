import Mathlib

open scoped BigOperators NNReal
open MeasureTheory

namespace Scratch

noncomputable section

abbrev γ : Measure ℝ := ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))

example : Integrable (fun z : ℝ => z ^ 2) γ := by
  have h : MemLp (fun z : ℝ => z) 2 γ := by
    simpa [γ] using (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0)))
  simpa using h.integrable_sq

end

end Scratch
