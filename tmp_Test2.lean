import Mathlib

def sech (x:ℝ) : ℝ := 1 / Real.cosh x

example : Continuous sech := by
  -- try fun_prop
  fun_prop
