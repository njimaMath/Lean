import Mathlib

open scoped BigOperators
open MeasureTheory

namespace Scratch

abbrev γ : Measure ℝ := ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))

#check ProbabilityTheory.memLp_id_gaussianReal
#check (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0)))
#check (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))) |>.integrable

example : Integrable (fun z : ℝ => z ^ 2) γ := by
  -- placeholder
  admit

end Scratch
