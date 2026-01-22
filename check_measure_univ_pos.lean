import Mathlib
open MeasureTheory
open scoped ENNReal
namespace Test
noncomputable section
abbrev γ : Measure ℝ := ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
example : (0 : ℝ≥0∞) < γ Set.univ := by
  simp [γ]
end
end Test
