import Mathlib
open MeasureTheory

example {α} [MeasurableSpace α] {μ : Measure α} (f g : α → ℝ)
    (h : (∫ x, -f x ∂μ) = - ∫ x, g x ∂μ) : (∫ x, f x ∂μ) = (∫ x, g x ∂μ) := by
  -- try using integral_neg
  have : -(∫ x, f x ∂μ) = -∫ x, g x ∂μ := by
    -- rewrite left using integral_neg
    simpa [integral_neg] using h
  -- cancel neg
  exact (neg_inj).1 this
