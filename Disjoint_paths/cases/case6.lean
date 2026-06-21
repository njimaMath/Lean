import cases.common

namespace DisjointPaths

lemma exists_disjoint_paths_case6
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (hcard : 2 ≤ (positiveCoords xnp1).card)
    (hdist : 2 ≤ Zd.l1Norm (xn - xnp1)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry


end DisjointPaths
