import Mathlib
open MeasureTheory

example (u w : ℝ → ℝ) (hu : Integrable u) (hw : Integrable w) :
    (∫ x, -(u x) ) = - ∫ x, u x := by
  simp
