import Mathlib.Data.Real.Basic
import Mathlib.Tactic

example (x y : ℝ) (h₁ : x + y ≤ 1) (h₂ : x - y ≤ 1) : x ≤ 1 := by
  linarith

theorem abs_le_one_of_sq_add_sq_le_one (x y : ℝ) (h : x ^ 2 + y ^ 2 ≤ 1) : |x| ≤ 1 ∧ |y| ≤ 1 := by
  have hx2 : x ^ 2 ≤ 1 := le_trans (le_add_of_nonneg_right (sq_nonneg y)) h
  have hy2 : y ^ 2 ≤ 1 := le_trans (le_add_of_nonneg_left (sq_nonneg x)) h
  constructor
  · exact (sq_le_one_iff_abs_le_one x).1 hx2
  · exact (sq_le_one_iff_abs_le_one y).1 hy2
