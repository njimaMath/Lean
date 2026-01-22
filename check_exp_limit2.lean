import Mathlib
open Filter
open scoped Topology
#check (by
  have hlin : Tendsto (fun x : ℝ => (-2 : ℝ) * x) atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro a
    have h : ∀ᶠ x in atTop, (-a / 2 : ℝ) ≤ x := Filter.eventually_ge_atTop (-a / 2)
    refine h.mono (fun x hx => ?_)
    nlinarith
  have h := Real.tendsto_exp_atBot.comp hlin
  -- show goal
  exact h
  )
