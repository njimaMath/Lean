import Mathlib

open scoped Real

example (x : ℝ) : deriv (fun x => Real.log (Real.cosh x)) x = Real.tanh x := by
  simp

