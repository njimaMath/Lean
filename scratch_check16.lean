import Mathlib

open MeasureTheory

example {α : Type} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℝ}
    (h : IntegrableOn f s μ) : Integrable f (μ.restrict s) := by
  simpa [IntegrableOn] using h

