import Mathlib
open Filter
open scoped Topology
#check (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝 (0:ℝ)) (𝓝 (1:ℝ)))
