import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped Real

#check (by
  have : Continuous (fun x : Real => Real.exp x) := by fun_prop
  exact this)
