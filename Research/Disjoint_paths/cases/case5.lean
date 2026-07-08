import cases.common

namespace DisjointPaths

lemma exists_disjoint_paths_case5_positive_neighbor_coordinate
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (hneigh : xnp1 = xn + Zd.e j)
    (hnot_axis : xn ≠ axisPoint (d := d) (n : Int) j)
    (hj_pos : 0 < xn j) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

/-- Case 5 stub: `xnp1 = xn + e_j`, excluding the axis-point subcase. -/
lemma exists_disjoint_paths_case5
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (hneigh : xnp1 = xn + Zd.e j)
    (hnot_axis : xn ≠ axisPoint (d := d) (n : Int) j) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  by_cases hj : 0 < xn j
  ·
    exact exists_disjoint_paths_case5_positive_neighbor_coordinate
      hd hδ_nonneg hδ hlarge hxn hxnp1 hnonneg_n hnonneg_np1 hneigh hnot_axis hj
  ·
    have hj_zero : xn j = 0 := by
      exact le_antisymm (le_of_not_gt hj) (hnonneg_n j)
    sorry

end DisjointPaths
