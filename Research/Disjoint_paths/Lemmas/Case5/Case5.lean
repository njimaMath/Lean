import Disjoint_paths.Lemmas.Case5.Basic
import Disjoint_paths.Lemmas.Case5.Long

/-!
# Case 5: neighboring points, nonzero joining coordinate

The short and long branches are selected at `pathScale`.  In the short branch,
a different coordinate is obtained from the strong reservoir estimate.
-/

namespace DisjointPaths

noncomputable section

theorem case5_neighbor_nonzero
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z y : LatticePoint d) (hz : z ∈ sphere d n)
    (hy : y ∈ sphere d (n + 1))
    (hzNonAxis : ¬ IsAxisPoint n z)
    (hyNonAxis : ¬ IsAxisPoint (n + 1) y)
    (r : Fin d) (hzr : z r ≠ 0)
    (hrsign : coordinateSign (y r) = coordinateSign (z r))
    (hrstep : coordinateSign (z r) * y r =
      coordinateSign (z r) * z r + 1)
    (hother : ∀ k, k ≠ r → y k = z k) :
    ∃ paths : PathIndex n z y → LatticePath d,
      FamilyProperties (n := n) δ z y paths := by
  let m := pathScale δ n
  by_cases hshort : Int.natAbs (z r) < m
  · have hstrong : 16 * d ^ 2 * m ≤ n :=
      pathScale_strong_reservoir_bound hd hn hδpos hδ
    have hd3 : d * (3 * m) ≤ n := by
      have hcoeff : d * (3 * m) ≤ 16 * d ^ 2 * m := by
        calc
          d * (3 * m) = 3 * d * m := by ring
          _ ≤ (16 * d) * d * m := by
            gcongr
            omega
          _ = 16 * d ^ 2 * m := by ring
      exact hcoeff.trans hstrong
    obtain ⟨p, hp⟩ := exists_reservoir_coordinate
      (show 1 ≤ d by omega) z hz hd3
    have hpr : p ≠ r := by
      intro h
      subst p
      rw [coordinateSign_mul_self] at hp
      have hm : 0 < m := by
        have : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
        omega
      have hpNat : 3 * m ≤ Int.natAbs (z r) := by exact_mod_cast hp
      omega
    apply case5_short_nonzero hd δ hδpos hδ hscale z y hz hy
      hzNonAxis hyNonAxis r p hpr.symm hzr hshort hp
    · exact hother p hpr
    · exact hrstep
    · exact hrsign
  · apply case5_long_nonzero hd δ hδpos hδ hscale z y hz hy
      hzNonAxis hyNonAxis r hzr (by omega) hrsign hrstep hother

end

end DisjointPaths
