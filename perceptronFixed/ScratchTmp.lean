import Mathlib
open scoped Topology
open Filter

namespace Scratch

example : Tendsto (fun q : ℝ => Real.sqrt ((1 : ℝ) - q) / (1 + Real.sqrt q)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hsqrt1 : Tendsto (fun q : ℝ => Real.sqrt q) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hsqrt : ContinuousAt (fun q : ℝ => Real.sqrt q) (1 : ℝ) := Real.continuous_sqrt.continuousAt
    simpa using hsqrt.tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun q : ℝ => (1 : ℝ) - q) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hcont : ContinuousAt (fun q : ℝ => (1 : ℝ) - q) (1 : ℝ) :=
      (continuous_const.sub continuous_id).continuousAt
    have h : Tendsto (fun q : ℝ => (1 : ℝ) - q) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - (1 : ℝ))) := hcont.tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  have hden0 : Tendsto (fun q : ℝ => Real.sqrt ((1 : ℝ) - q)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hsqrt0 : ContinuousAt Real.sqrt (0 : ℝ) := Real.continuous_sqrt.continuousAt
    simpa using (hsqrt0.tendsto.comp hsub)
  have hden : Tendsto (fun q : ℝ => (1 : ℝ) + Real.sqrt q) (𝓝[<] (1 : ℝ)) (𝓝 (2 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hsqrt1)
  -- denominator tends to nonzero 2
  have hden_ne : (2 : ℝ) ≠ 0 := by norm_num
  simpa [div_eq_mul_inv] using (hden0.div hden hden_ne)
