import Mathlib
example : (1 / Real.sqrt (2 * Real.pi)) / Real.sqrt (2 / Real.pi)
    = (1 : ℝ) / (Real.sqrt (2 * Real.pi) * Real.sqrt (2 / Real.pi)) := by
  simpa using (div_div (1 : ℝ) (Real.sqrt (2 * Real.pi)) (Real.sqrt (2 / Real.pi)))
