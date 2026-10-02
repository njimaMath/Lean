import Disjoint_paths.Lemmas.Case2.Case2

namespace DisjointPaths

noncomputable section

theorem case3_axis_outer_large_gap
    {d n : ℕ} (hd : 3 ≤ d) (δ : ℝ)
    (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (houterAxis : IsAxisPoint (n + 1) xOuter)
    (_hinnerNonAxis : ¬ IsAxisPoint n xInner) (r : Fin d)
    (hcoordinate : 3 * (pathScale δ n : ℤ) ≤ xInner r - xOuter r) :
    ∃ paths : PathIndex n xInner xOuter → LatticePath d,
      (∀ i : Fin (pathCountAtInner n xInner), (paths (Sum.inl i)).start = xInner) ∧
      (∀ i : Fin (pathCountAtOuter n xOuter), (paths (Sum.inr i)).start = xOuter) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices, x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i, ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) := by
  exact case2_axis_outer_large_gap hd δ hδpos hδ hn hscale xInner xOuter
    hinner houter houterAxis r hcoordinate

end

end DisjointPaths
