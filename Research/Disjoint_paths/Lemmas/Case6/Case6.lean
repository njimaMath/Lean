import Disjoint_paths.Lemmas.Case6.Long
import Disjoint_paths.Lemmas.SeparatedPrivateFamilies

/-!
# Case 6: same-orthant non-neighbor subcases

This module dispatches between the short and long constructions in a signed
coordinate where the outer point is strictly larger.  It also exposes the
large starting-gap branch used before the local constructions are selected.
-/

namespace DisjointPaths

noncomputable section

theorem case6_increasing_coordinate_nonzero
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z y : LatticePoint d) (hz : z ∈ sphere d n)
    (hy : y ∈ sphere d (n + 1))
    (hzNonAxis : ¬ IsAxisPoint n z)
    (hyNonAxis : ¬ IsAxisPoint (n + 1) y)
    (r p q : Fin d) (hrp : r ≠ p) (hqr : q ≠ r)
    (hzr : z r ≠ 0) (hyq : y q ≠ 0) (hyr : y r ≠ 0)
    (hzReservoir : ((3 * pathScale δ n : ℕ) : ℤ) ≤
      coordinateSign (z p) * z p)
    (hyReservoir : ((3 * pathScale δ n : ℕ) : ℤ) ≤
      coordinateSign (y q) * y q)
    (hrsign : coordinateSign (y r) = coordinateSign (z r))
    (hrgap : coordinateSign (z r) * z r + 1 ≤
      coordinateSign (z r) * y r) :
    ∃ paths : PathIndex n z y → LatticePath d,
      FamilyProperties (n := n) δ z y paths := by
  by_cases hshort : Int.natAbs (z r) < pathScale δ n
  · exact case6_short_increasing_coordinate hd δ hδpos hδ hscale z y hz hy
      hzNonAxis hyNonAxis r p q hrp hqr hzr hyq hyr hshort
      hzReservoir hyReservoir hrsign hrgap
  · exact case6_long_increasing_coordinate hd δ hδpos hδ hscale z y hz hy
      hzNonAxis hyNonAxis r q hqr hzr hyq hyr (by omega)
      hyReservoir hrsign hrgap

theorem case6_large_coordinate_gap
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z y : LatticePoint d) (hz : z ∈ sphere d n)
    (hy : y ∈ sphere d (n + 1))
    (hyNonAxis : ¬ IsAxisPoint (n + 1) y)
    (r : Fin d)
    (hgap : 3 * (pathScale δ n : ℤ) ≤ z r - y r ∨
      3 * (pathScale δ n : ℤ) ≤ y r - z r) :
    ∃ paths : PathIndex n z y → LatticePath d,
      FamilyProperties (n := n) δ z y paths := by
  rcases hgap with hgap | hgap
  · simpa only [FamilyProperties] using
      exists_nonAxis_paths_of_inner_coordinate_gap hd δ hδpos hδ hn hscale
        z y hz hy hyNonAxis r hgap
  · simpa only [FamilyProperties] using
      exists_nonAxis_paths_of_outer_coordinate_gap hd δ hδpos hδ hn hscale
        z y hz hy hyNonAxis r hgap

end

end DisjointPaths
