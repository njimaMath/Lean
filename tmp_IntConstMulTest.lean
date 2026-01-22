import Mathlib
open MeasureTheory

example (μ : Measure ℝ) (c : ℝ) (f : ℝ → ℝ) :
    (∫ x, c * f x ∂μ) = c * (∫ x, f x ∂μ) := by
  simpa using (MeasureTheory.integral_const_mul c f)
