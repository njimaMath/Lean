import cases.common

namespace DisjointPaths

lemma exists_disjoint_paths_case2_large_j_coordinate
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (haxis : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hcard : 2 ≤ (positiveCoords xn).card)
    (hj_large : δ ^ 2 * (n + 1 : ℝ) ≤ (xn j : ℝ)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

lemma exists_disjoint_paths_case2_small_j_coordinate
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (haxis : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hcard : 2 ≤ (positiveCoords xn).card)
    (hj : 0 < xn j)
    (hj_small : δ ^ 2 * (n + 1 : ℝ) > (xn j : ℝ)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

/- Case 2 stub: `xnp1` is a positive axis point and `xn j > 0`. -/
lemma exists_disjoint_paths_case2
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (haxis : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hcard : 2 ≤ (positiveCoords xn).card)
    (hj : 0 < xn j) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  by_cases hj_large : δ ^ 2 * (n + 1 : ℝ) ≤ (xn j : ℝ)
  ·
    apply exists_disjoint_paths_case2_large_j_coordinate
      hd hδ_nonneg hδ hlarge hxn hxnp1 hnonneg_n hnonneg_np1 haxis hcard hj_large
  ·
    apply exists_disjoint_paths_case2_small_j_coordinate
      hd hδ_nonneg hδ hlarge hxn hxnp1 hnonneg_n hnonneg_np1 haxis hcard hj
    exact not_le.mp hj_large

end DisjointPaths
