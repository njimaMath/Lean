import Mathlib
open Filter
open scoped Topology NNReal
#check (by
  have : Tendsto (fun r : ℝ≥0 => (r:ℝ)) atTop atTop := by
    -- use lemma tendsto_coe_atTop with m := id
    simpa using (tendsto_coe_atTop (f := (atTop : Filter ℝ≥0)) (m := fun r : ℝ≥0 => r)).2 (tendsto_id)
  exact this
  )
