import Disjoint_paths.Lemmas.Case2.Case2
import Disjoint_paths.Lemmas.Case2.NearAxis
import Disjoint_paths.Lemmas.Case4.Case4

/-!
# Complete dispatch when the outer point is an axis point
-/

namespace DisjointPaths

noncomputable section

theorem exists_paths_of_outer_axis
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
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
  have hstrong : 16 * d ^ 2 * m ≤ n :=
    pathScale_strong_reservoir_bound hd hn hδpos hδ
  have hcoeff : 4 ≤ 16 * d ^ 2 := by nlinarith
  have h4m : 4 * m ≤ n := by
    exact (Nat.mul_le_mul_right m hcoeff).trans (by simpa [mul_assoc] using hstrong)
  rcases houterAxis with ⟨p, hyo⟩
  by_cases hinnerAxis : IsAxisPoint n xInner
  · exact case4_both_axis hd δ hδpos hδ hn hscale xInner xOuter
      hinner houter hinnerAxis ⟨p, hyo⟩
  · by_cases hforward :
        3 * (m : ℤ) ≤ xInner p - xOuter p
    · exact case2_axis_outer_large_gap hd δ hδpos hδ hn hscale
        xInner xOuter hinner houter ⟨p, hyo⟩ p hforward
    · by_cases hreverse :
          3 * (m : ℤ) ≤ xOuter p - xInner p
      · exact case2_axis_outer_reverse_large_gap hd δ hδpos hδ hn hscale
          xInner xOuter hinner houter ⟨p, hyo⟩ p hreverse
      · have h4mZ : (4 * m : ℕ) ≤ n := h4m
        rcases hyo with hyo | hyo
        · have hyP : xOuter p = (n + 1 : ℕ) := by
            rw [hyo]
            simp
          have hzpos : 0 < xInner p := by
            have h4mCast : ((4 * m : ℕ) : ℤ) ≤ n := by exact_mod_cast h4mZ
            omega
          have hzReservoir : (m : ℤ) ≤
              coordinateSign (xInner p) * xInner p := by
            simp [coordinateSign, hzpos.le]
            have h4mCast : ((4 * m : ℕ) : ℤ) ≤ n := by exact_mod_cast h4mZ
            omega
          have hyReservoir : (m : ℤ) ≤
              coordinateSign (xOuter p) * xOuter p := by
            rw [coordinateSign_mul_self, hyP]
            exact_mod_cast (show m ≤ n + 1 by omega)
          obtain ⟨h, hhp, hzh⟩ := exists_other_nonzero_of_not_axis
            (by omega) xInner hinner hinnerAxis p (ne_of_gt hzpos)
          apply case2_near_axis_nonAxis hd δ hδpos hδ hn hscale
            xInner xOuter hinner houter hinnerAxis ⟨p, Or.inl hyo⟩
            p h hhp hzh
          · intro r hr
            rw [hyo]
            simp [hr]
          · exact hzReservoir
          · exact hyReservoir
        · have hyP : xOuter p = -((n + 1 : ℕ) : ℤ) := by
            rw [hyo]
            simp
          have hzneg : xInner p < 0 := by
            have h4mCast : ((4 * m : ℕ) : ℤ) ≤ n := by exact_mod_cast h4mZ
            omega
          have hzReservoir : (m : ℤ) ≤
              coordinateSign (xInner p) * xInner p := by
            simp [coordinateSign, not_le.mpr hzneg]
            have h4mCast : ((4 * m : ℕ) : ℤ) ≤ n := by exact_mod_cast h4mZ
            omega
          have hyReservoir : (m : ℤ) ≤
              coordinateSign (xOuter p) * xOuter p := by
            rw [coordinateSign_mul_self, hyP, Int.natAbs_neg, Int.natAbs_natCast]
            exact_mod_cast (show m ≤ n + 1 by omega)
          obtain ⟨h, hhp, hzh⟩ := exists_other_nonzero_of_not_axis
            (by omega) xInner hinner hinnerAxis p (ne_of_lt hzneg)
          apply case2_near_axis_nonAxis hd δ hδpos hδ hn hscale
            xInner xOuter hinner houter hinnerAxis ⟨p, Or.inr hyo⟩
            p h hhp hzh
          · intro r hr
            rw [hyo]
            simp [hr]
          · exact hzReservoir
          · exact hyReservoir

end

end DisjointPaths
