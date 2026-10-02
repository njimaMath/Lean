import Disjoint_paths.Lemmas.Case2.Case2
import Disjoint_paths.Lemmas.Case4.SameAxis

/-!
# Case 4: both points are axis points

The large-gap subcase is inherited from the axis-outer construction.  The
additional inner-axis hypothesis is retained here so the final dispatcher can
select this case directly.
-/

namespace DisjointPaths

noncomputable section

theorem case4_both_axis_large_gap
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (_hinnerAxis : IsAxisPoint n xInner)
    (houterAxis : IsAxisPoint (n + 1) xOuter) (r : Fin d)
    (hcoordinate : 3 * (pathScale δ n : ℤ) ≤ xInner r - xOuter r) :
    ∃ paths : PathIndex n xInner xOuter → LatticePath d,
      (∀ i : Fin (pathCountAtInner n xInner),
        (paths (Sum.inl i)).start = xInner) ∧
      (∀ i : Fin (pathCountAtOuter n xOuter),
        (paths (Sum.inr i)).start = xOuter) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) := by
  exact case2_axis_outer_large_gap hd δ hδpos hδ hn hscale xInner xOuter
    hinner houter houterAxis r hcoordinate

theorem case4_both_axis
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (hinnerAxis : IsAxisPoint n xInner)
    (houterAxis : IsAxisPoint (n + 1) xOuter) :
    ∃ paths : PathIndex n xInner xOuter → LatticePath d,
      (∀ i : Fin (pathCountAtInner n xInner),
        (paths (Sum.inl i)).start = xInner) ∧
      (∀ i : Fin (pathCountAtOuter n xOuter),
        (paths (Sum.inr i)).start = xOuter) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) := by
  let m := pathScale δ n
  have hdm : d * m ≤ n := pathScale_reservoir_bound hd hn hδpos hδ
  have h3m : 3 * m ≤ n := by
    exact (Nat.mul_le_mul_right m hd).trans hdm
  rcases hinnerAxis with ⟨pi, hzi⟩
  rcases houterAxis with ⟨po, hyo⟩
  by_cases haxes : pi = po
  · subst po
    letI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨h, hhpi⟩ := exists_ne pi
    apply case4_same_axis hd δ hδpos hδ hn hscale xInner xOuter
      hinner houter ⟨pi, hzi⟩ ⟨pi, hyo⟩ pi h hhpi
    · intro r hr
      rcases hzi with hzi | hzi <;> rw [hzi] <;> simp [hr]
    · intro r hr
      rcases hyo with hyo | hyo <;> rw [hyo] <;> simp [hr]
    · rw [coordinateSign_mul_self]
      have hm : m ≤ n := by omega
      exact_mod_cast (show m ≤ Int.natAbs (xInner pi) by
        rcases hzi with hzi | hzi <;> rw [hzi] <;> simp [hm])
    · rw [coordinateSign_mul_self]
      have hm : m ≤ n + 1 := by omega
      exact_mod_cast (show m ≤ Int.natAbs (xOuter pi) by
        rcases hyo with hyo | hyo
        · rw [hyo]
          simp only [if_pos, Int.natAbs_natCast]
          exact hm
        · rw [hyo]
          simp only [if_pos, Int.natAbs_neg, Int.natAbs_natCast]
          exact hm)
  · have houterZero : xOuter pi = 0 := by
      rcases hyo with hyo | hyo <;> rw [hyo] <;> simp [haxes]
    rcases hzi with hzi | hzi
    · apply case2_axis_outer_large_gap hd δ hδpos hδ hn hscale
        xInner xOuter hinner houter ⟨po, hyo⟩ pi
      rw [hzi, houterZero]
      simp
      exact_mod_cast h3m
    · apply case2_axis_outer_reverse_large_gap hd δ hδpos hδ hn hscale
        xInner xOuter hinner houter ⟨po, hyo⟩ pi
      rw [hzi, houterZero]
      simp
      exact_mod_cast h3m

end

end DisjointPaths
