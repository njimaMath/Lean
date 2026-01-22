import Mathlib
open Filter
open scoped Topology
example (h : Tendsto Real.tanh atTop (𝓝 (1:ℝ))) : Tendsto (fun x : ℝ => Real.tanh (-x)) atBot (𝓝 (1:ℝ)) := by
  -- rewrite the goal to avoid simp rewriting `tanh (-x)`
  change Tendsto (Real.tanh ∘ Neg.neg) atBot (𝓝 (1:ℝ))
  exact h.comp Filter.tendsto_neg_atBot_atTop
