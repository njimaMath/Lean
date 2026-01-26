import Mathlib
open Filter
open scoped Topology
example (p q : Prop) : (¬(p ∧ q)) → False := by
  intro h
  -- simp_all does not change h? 
  simp_all
