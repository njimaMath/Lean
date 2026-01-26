import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

open scoped Real

variable (mu : Real) (v : Real) (x : Real)

example : (-(2 * (x - mu)) / (2 * v)) = (-(x - mu) / v) := by
  by_cases hv : v = 0
  · simp [hv]
  · field_simp [hv]
    ring
