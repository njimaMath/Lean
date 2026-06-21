import cases.common

namespace DisjointPaths

lemma exists_disjoint_paths_case3_core
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
    (hj0 : xn j = 0) :
    ∃ inner : PathBundle d n δ xn, ∃ outer : PathBundle d n δ xnp1,
      inner.paths.length = requiredInnerPathCount (d := d) n xn - 1 ∧
        outer.paths.length = requiredOuterPathCount (d := d) n xnp1 ∧
          (∀ gamma ∈ inner.paths, ∀ gamma' ∈ outer.paths,
            PathSpec.EdgeDisjoint gamma gamma') ∧
            inner.paths.Pairwise (fun gamma gamma' =>
              PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
                PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma) ∧
              outer.paths.Pairwise (fun gamma gamma' =>
                PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
                  PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma) ∧
                (∀ gamma ∈ inner.paths, ∀ gamma' ∈ outer.paths,
                  PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
                    PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma) := by
  sorry

/-
Because `xn` has an extra zero coordinate compared with Case 2, one additional
inner path is needed. It is `gamma_n^{(1,+)}`, obtained by alternating `+e_1`
and `-e_2` up to `δ^2 * (n + 1)` steps.
-/
/--
Case 3 stub: once the core family is in place, the remaining step is to add the
extra inner path `gamma_n^{(1,+)}` and recover the missing inner-path count.
-/
lemma exists_disjoint_paths_case3
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
    (hj0 : xn j = 0) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

end DisjointPaths
