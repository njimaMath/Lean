import Mathlib
open MeasureTheory
open scoped ENNReal
namespace Test
noncomputable section
abbrev γ : Measure ℝ := ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
example (κ : ℝ) : True := by
  let f : ℝ → ℝ := fun z => (max (κ - z) 0) ^ 2
  have hf_nonneg : 0 ≤ᵐ[γ] f := by
    refine ae_of_all _ (fun z => ?_)
    exact sq_nonneg (max (κ - z) 0)
  have h_support_pos : (0 : ℝ≥0∞) < γ (Function.support f) := by
    admit
  trivial
end
end Test
