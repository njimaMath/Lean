import Mathlib
open MeasureTheory

noncomputable section

variable (a : ℝ) (pdf : ℝ → ℝ)

example : (fun x : ℝ => Real.tanh (a * x) * (-x * pdf x)) =
    fun x : ℝ => -(Real.tanh (a * x) * (x * pdf x)) := by
  funext x
  ring

end
