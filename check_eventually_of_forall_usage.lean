import Mathlib
open Filter
#check Filter.Eventually.of_forall
#check (by
  refine (Filter.Eventually.of_forall (f := atTop) (fun x : ℝ => True)) )
