import Mathlib
open MeasureTheory

noncomputable section

variable {μ : Measure ℝ} (a : ℝ) (pdf : ℝ → ℝ)

example : (fun x : ℝ => (a * x) * pdf x) = fun x => a * (x * pdf x) := by
  funext x
  ring

end
