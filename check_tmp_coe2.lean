import Mathlib
open Filter
open scoped Topology NNReal
#check (tendsto_id : Tendsto (fun x : ℝ≥0 => x) atTop atTop)
#check (show Tendsto (fun x : ℝ≥0 => (x:ℝ)) atTop atTop from ?_)
