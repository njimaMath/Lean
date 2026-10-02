import Disjoint_paths.Lemmas.DownwardInnerFamily
import Disjoint_paths.Lemmas.SeparatedOuterFamily
import Disjoint_paths.Lemmas.Family

/-!
# Case 6: separated motion in an increasing coordinate

The reservoirs used by the two families may be different.  Every inner path
stays on the lower side of the separating coordinate and finishes one path
scale farther down; every outer path stays on the upper side and finishes one
path scale farther up.
-/

namespace DisjointPaths

noncomputable section

theorem case6_short_increasing_coordinate
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z y : LatticePoint d) (hz : z ∈ sphere d n)
    (hy : y ∈ sphere d (n + 1))
    (hzNonAxis : ¬ IsAxisPoint n z)
    (hyNonAxis : ¬ IsAxisPoint (n + 1) y)
    (r p q : Fin d) (hrp : r ≠ p) (hqr : q ≠ r)
    (hzr : z r ≠ 0) (hyq : y q ≠ 0) (hyr : y r ≠ 0)
    (hshort : Int.natAbs (z r) < pathScale δ n)
    (hzReservoir : ((3 * pathScale δ n : ℕ) : ℤ) ≤
      coordinateSign (z p) * z p)
    (hyReservoir : ((3 * pathScale δ n : ℕ) : ℤ) ≤
      coordinateSign (y q) * y q)
    (hrsign : coordinateSign (y r) = coordinateSign (z r))
    (hrgap : coordinateSign (z r) * z r + 1 ≤
      coordinateSign (z r) * y r) :
    ∃ paths : PathIndex n z y → LatticePath d,
      FamilyProperties (n := n) δ z y paths := by
  obtain ⟨inner, hiStart, hiEdges, hiSpheres, hiLength, hiFar,
      hiUpper, hiFinish⟩ :=
    exists_shortDownwardInnerFamily_nonAxis hd δ hδpos hδ hscale z hz
      hzNonAxis r p hrp hzr hshort hzReservoir
  obtain ⟨outer, hoStart, hoEdges, hoSpheres, hoLength, hoFar,
      hoLower, hoFinish⟩ :=
    exists_separated_outerFamily hd δ hδpos hδ hscale y hy hyNonAxis
      q r hqr hyq hyr hyReservoir
  let sr := coordinateSign (z r)
  have hsr : Int.natAbs sr = 1 := natAbs_coordinateSign _
  let paths : PathIndex n z y → LatticePath d := Sum.elim inner outer
  refine ⟨paths, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [paths] using hiStart i
  · intro i
    simpa [paths] using hoStart i
  · intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · apply hiEdges i j
      intro h
      apply hij
      cases h
      rfl
    · apply edgeDisjoint_of_vertices_disjoint
      rw [Set.disjoint_left]
      intro x hxi hxo
      have hle := hiUpper i x (by simpa [paths] using hxi)
      have hge := hoLower j x (by simpa [paths] using hxo)
      rw [hrsign] at hge
      omega
    · symm
      apply edgeDisjoint_of_vertices_disjoint
      rw [Set.disjoint_left]
      intro x hxo hxi
      have hle := hiUpper j x (by simpa [paths] using hxo)
      have hge := hoLower i x (by simpa [paths] using hxi)
      rw [hrsign] at hge
      omega
    · apply hoEdges i j
      intro h
      apply hij
      cases h
      rfl
  · intro i x hx
    rcases i with i | i
    · exact hiSpheres i x (by simpa [paths] using hx)
    · exact hoSpheres i x (by simpa [paths] using hx)
  · intro i
    rcases i with i | i
    · simpa [paths] using hiLength i
    · simpa [paths] using hoLength i
  · intro i j hij x hx
    rcases i with i | i <;> rcases j with j | j
    · apply hiFar i j
      · intro h
        apply hij
        cases h
        rfl
      · simpa [paths] using hx
    · apply endpoint_far_from_vertices_of_signed_coordinate_gap
        (inner i) (outer j) r (-sr) (by simpa using hsr)
        (δ ^ 3 * (n + 1 : ℝ)) (-sr * y r) (pathScale δ n)
        (separation_radius_le_pathScale hd hδpos hδ n hscale)
        (by positivity)
      · have hfinish := hiFinish i
        push_cast
        nlinarith [hrgap]
      · intro w hw
        have hlower := hoLower j w hw
        rw [hrsign] at hlower
        nlinarith
      · simpa [paths] using hx
    · apply endpoint_far_from_vertices_of_signed_coordinate_gap
        (outer i) (inner j) r sr hsr
        (δ ^ 3 * (n + 1 : ℝ)) (sr * z r) (pathScale δ n)
        (separation_radius_le_pathScale hd hδpos hδ n hscale)
        (by positivity)
      · have hfinish := hoFinish i
        rw [hrsign] at hfinish
        push_cast
        nlinarith [hrgap]
      · exact hiUpper j
      · simpa [paths] using hx
    · apply hoFar i j
      · intro h
        apply hij
        cases h
        rfl
      · simpa [paths] using hx

end

end DisjointPaths
