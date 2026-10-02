import Disjoint_paths.Lemmas.DownwardInnerFamily
import Disjoint_paths.Lemmas.SeparatedOuterFamily
import Disjoint_paths.Lemmas.Family

/-!
# Case 5: neighboring points with a short nonzero joining coordinate
-/

namespace DisjointPaths

noncomputable section

theorem case5_short_nonzero
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z y : LatticePoint d) (hz : z ∈ sphere d n)
    (hy : y ∈ sphere d (n + 1))
    (hzNonAxis : ¬ IsAxisPoint n z)
    (hyNonAxis : ¬ IsAxisPoint (n + 1) y)
    (r p : Fin d) (hrp : r ≠ p) (hzr : z r ≠ 0)
    (hshort : Int.natAbs (z r) < pathScale δ n)
    (hreservoir : ((3 * pathScale δ n : ℕ) : ℤ) ≤
      coordinateSign (z p) * z p)
    (hyp : y p = z p)
    (hrstep : coordinateSign (z r) * y r =
      coordinateSign (z r) * z r + 1)
    (hrsign : coordinateSign (y r) = coordinateSign (z r)) :
    ∃ paths : PathIndex n z y → LatticePath d,
      FamilyProperties (n := n) δ z y paths := by
  classical
  let sr := coordinateSign (z r)
  have hsr : Int.natAbs sr = 1 := natAbs_coordinateSign _
  have hypNonzero : y p ≠ 0 := by
    intro hypzero
    have hzp : z p = 0 := by omega
    rw [hzp] at hreservoir
    norm_num at hreservoir
    have hm : 12 ≤ pathScale δ n := by
      apply (Nat.le_floor_iff (by positivity)).mpr
      exact hscale
    omega
  have hyr : y r ≠ 0 := by
    intro hyrzero
    rw [hyrzero] at hrstep
    have hzsign : sr * z r = Int.natAbs (z r) := by
      dsimp [sr]
      rw [coordinateSign_mul_self]
    rw [hzsign] at hrstep
    omega
  have hyReservoir : ((3 * pathScale δ n : ℕ) : ℤ) ≤
      coordinateSign (y p) * y p := by
    rw [hyp]
    have hzp : z p ≠ 0 := by
      intro hzero
      rw [hzero] at hreservoir
      norm_num at hreservoir
      have hm : 12 ≤ pathScale δ n := by
        apply (Nat.le_floor_iff (by positivity)).mpr
        exact hscale
      omega
    simpa [hyp] using hreservoir
  obtain ⟨inner, hiStart, hiEdges, hiSpheres, hiLength, hiFar,
      hiUpper, hiFinish⟩ :=
    exists_shortDownwardInnerFamily_nonAxis hd δ hδpos hδ hscale z hz
      hzNonAxis r p hrp hzr hshort hreservoir
  obtain ⟨outer, hoStart, hoEdges, hoSpheres, hoLength, hoFar,
      hoLower, hoFinish⟩ :=
    exists_separated_outerFamily hd δ hδpos hδ hscale y hy hyNonAxis
      p r (Ne.symm hrp) hypNonzero hyr hyReservoir
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
        nlinarith
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
        nlinarith
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
