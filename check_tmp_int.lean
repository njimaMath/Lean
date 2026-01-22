import Mathlib
open MeasureTheory
open scoped NNReal
#check (by
  have h : (∫ y : ℝ, (1:ℝ)) = (0:ℝ) := by
    -- dummy
    simp
  exact h)
