import Mathlib
open MeasureTheory

noncomputable section

example (μ : Measure ℝ) (g : ℝ → ℝ) (hg : Integrable g μ) (a : ℝ)
    (hf_bound : ∀ x : ℝ, ‖Real.tanh (a * x)‖ ≤ (1 : ℝ)) :
    Integrable (fun x : ℝ => Real.tanh (a * x) * g x) μ := by
  refine Integrable.bdd_mul hg (by
    have : Continuous (fun x : ℝ => Real.tanh (a * x)) := by fun_prop
    exact this.aestronglyMeasurable) ?_
  refine ae_of_all _ (fun x => ?_)
  simpa using hf_bound x

end
