import Mathlib

open scoped BigOperators NNReal
open MeasureTheory

namespace Scratch

noncomputable section

abbrev γ : Measure ℝ := ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))

example : Integrable (fun z : ℝ => z ^ 2) γ := by
  -- Use that `id` is in L², hence `∫ |z|^2 < ∞`.
  have h : MemLp (fun z : ℝ => z) (2 : ℝ≥0∞) γ := by
    simpa [γ] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0)))
  -- `Integrable (fun z => z^2)` because `‖z^2‖ = |z|^2`.
  -- Try rewriting and using `h`.
  have h2 : Integrable (fun z : ℝ => ‖z‖ ^ (2 : ℝ)) γ := by
    -- `MemLp` provides `Integrable (fun z => ‖z‖ ^ p)`? not sure.
    admit
  admit

end Scratch
