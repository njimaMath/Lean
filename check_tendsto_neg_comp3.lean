import Mathlib
open Filter
open scoped Topology
example (h : Tendsto Real.tanh atTop (𝓝 (1:ℝ))) : Tendsto (fun x : ℝ => Real.tanh (-x)) atBot (𝓝 (1:ℝ)) := by
  -- avoid simp
  simpa [Function.comp] using (h.comp Filter.tendsto_neg_atBot_atTop)
