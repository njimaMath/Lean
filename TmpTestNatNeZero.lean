import Mathlib

example {k : ℕ} (hk : 1 ≤ k) : k ≠ 0 := by
  exact Nat.ne_of_gt (Nat.pos_of_ne_zero (by decide))