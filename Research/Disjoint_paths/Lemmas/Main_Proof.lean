import Disjoint_paths.Lemmas.Reflection

/-!
# Edge-disjoint paths on two consecutive lattice spheres

This file states the path-existence lemma from the paper.  Its proof is left as
`sorry`.  Distances and the spheres are defined using the `ℓ¹` metric on
`Fin d → ℤ`.
-/

namespace DisjointPaths

noncomputable section

/--
Existence of the prescribed edge-disjoint paths on two consecutive `ℓ¹`
lattice spheres.
-/
theorem exists_edgeDisjoint_paths_on_consecutive_spheres_proof
    {d : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (xInner xOuter : LatticePoint d),
      xInner ∈ sphere d n →
      xOuter ∈ sphere d (n + 1) →
      ∃ paths : PathIndex n xInner xOuter → LatticePath d,
        (∀ i : Fin (pathCountAtInner n xInner),
          (paths (Sum.inl i)).start = xInner) ∧
        (∀ i : Fin (pathCountAtOuter n xOuter),
          (paths (Sum.inr i)).start = xOuter) ∧
        (∀ i j, i ≠ j →
          Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
        (∀ i, ∀ x ∈ (paths i).vertices,
          x ∈ sphere d n ∪ sphere d (n + 1)) ∧
        (∀ i,
          ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
          ((paths i).edgeLength : ℤ) ≤
            ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
        (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
          δ ^ 3 * (n + 1 : ℝ) ≤
            (l1Dist (paths i).finish x : ℝ)) := by
  sorry
end

end DisjointPaths
