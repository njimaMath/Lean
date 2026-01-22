import Mathlib
open Filter
open scoped Topology
#check Real.tendsto_exp_atBot
#check Function.comp
example : Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (𝓝 (0 : ℝ)) := by
  have hlin : Tendsto (fun x : ℝ => -2 * x) atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro a
    have h : ∀ᶠ x in atTop, (-a / 2 : ℝ) ≤ x := Filter.eventually_ge_atTop (-a / 2)
    refine h.mono (fun x hx => ?_)
    nlinarith
  simpa [Function.comp] using (Real.tendsto_exp_atBot.comp hlin)
