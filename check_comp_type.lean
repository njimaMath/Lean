import Mathlib
open Filter
open scoped Topology
#check (by
  have hcont : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 0 := by
    have : (1 + (0 : ℝ)) ≠ 0 := by norm_num
    simpa using (continuousAt_const.sub continuousAt_id).div (continuousAt_const.add continuousAt_id) this
  have h_exp : Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (𝓝 (0 : ℝ)) := by
    -- dummy
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 0))
  have h := hcont.tendsto.comp h_exp
  -- show the type
  exact h
  )
