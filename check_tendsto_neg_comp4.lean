import Mathlib
open Filter
open scoped Topology
example (h : Tendsto Real.tanh atTop (𝓝 (1:ℝ))) : Tendsto (fun x : ℝ => Real.tanh (-x)) atBot (𝓝 (1:ℝ)) := by
  have this : Tendsto (Real.tanh ∘ Neg.neg) atBot (𝓝 (1:ℝ)) := h.comp Filter.tendsto_neg_atBot_atTop
  -- `rfl` should work after unfolding `Function.comp`
  simpa [Function.comp] using this
