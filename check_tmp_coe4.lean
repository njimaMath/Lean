import Mathlib
open Filter
open scoped Topology NNReal
#check (by
  have : Tendsto (fun r : ℝ≥0 => (r:ℝ)) atTop atTop := by
    -- use NNReal.tendsto_coe_atTop with m := id
    have : Tendsto (fun r : ℝ≥0 => r) (atTop : Filter ℝ≥0) atTop := tendsto_id
    -- rewrite
    exact (NNReal.tendsto_coe_atTop (f := (atTop : Filter ℝ≥0)) (m := fun r : ℝ≥0 => r)).2 this
  exact this
  )
