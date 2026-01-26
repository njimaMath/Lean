import Mathlib

example {k : ℕ} (hk : 1 ≤ k) : k ≠ 0 := by
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 1) hk)