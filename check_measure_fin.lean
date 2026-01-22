import Mathlib
open MeasureTheory
open scoped ENNReal
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
#check (by
  have : μ ({0} : Set ℝ) ≠ (⊤ : ℝ≥0∞) := by
    -- using measure_mono
    have : μ ({0} : Set ℝ) ≤ μ Set.univ := by
      exact measure_mono (by intro x hx; trivial)
    exact (ne_of_lt (lt_of_le_of_lt this (by simp))).symm )
