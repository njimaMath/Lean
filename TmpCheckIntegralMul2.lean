import Mathlib
open MeasureTheory
open scoped BigOperators
variable {μ : Measure ℝ}
variable (q : ℝ) (f : ℝ → ℝ)
example : (1 - q) * (∫ z, f z ∂μ) = ∫ z, (1 - q) * f z ∂μ := by
  simpa [mul_assoc] using (integral_mul_left (μ := μ) (1 - q) f).symm
