import Mathlib
open Filter
open scoped Topology
example (h : Tendsto Real.tanh atTop (𝓝 (1:ℝ))) : Tendsto (fun x : ℝ => Real.tanh (-x)) atBot (𝓝 (1:ℝ)) := by
  -- avoid `simp` rewriting `tanh (-x)`
  have : Tendsto (Real.tanh ∘ fun x : ℝ => -x) atBot (𝓝 (1:ℝ)) := h.comp Filter.tendsto_neg_atBot_atTop
  simpa [Function.comp] using this
