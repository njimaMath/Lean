import Disjoint_paths.Lemmas.Case6.Basic
import Disjoint_paths.Lemmas.FanCount

/-!
# Case 6: a long increasing coordinate

The inner family uses the separating coordinate as its reservoir.  Hence all
inner vertices remain below their starting signed coordinate, while the outer
family moves monotonically above its starting signed coordinate.
-/

namespace DisjointPaths

noncomputable section

open LatticePath

theorem case6_long_increasing_coordinate
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z y : LatticePoint d) (hz : z ∈ sphere d n)
    (hy : y ∈ sphere d (n + 1))
    (hzNonAxis : ¬ IsAxisPoint n z)
    (hyNonAxis : ¬ IsAxisPoint (n + 1) y)
    (r q : Fin d) (hqr : q ≠ r) (hzr : z r ≠ 0)
    (hyq : y q ≠ 0) (hyr : y r ≠ 0)
    (hlong : pathScale δ n ≤ Int.natAbs (z r))
    (hyReservoir : ((3 * pathScale δ n : ℕ) : ℤ) ≤
      coordinateSign (y q) * y q)
    (hrsign : coordinateSign (y r) = coordinateSign (z r))
    (hrgap : coordinateSign (z r) * z r + 1 ≤
      coordinateSign (z r) * y r) :
    ∃ paths : PathIndex n z y → LatticePath d,
      FamilyProperties (n := n) δ z y paths := by
  classical
  let m := pathScale δ n
  let sr := coordinateSign (z r)
  have hsr : Int.natAbs sr = 1 := natAbs_coordinateSign _
  change sr * z r + 1 ≤ sr * y r at hrgap
  have hzReservoir : (m : ℤ) ≤ sr * z r := by
    dsimp [sr]
    rw [coordinateSign_mul_self]
    exact_mod_cast hlong
  have hcard : Fintype.card (InnerFanIndex z r) = pathCountAtInner n z := by
    rw [card_innerFanIndex z r hzr]
    simp [pathCountAtInner, hzNonAxis]
  let innerEquiv : Fin (pathCountAtInner n z) ≃ InnerFanIndex z r :=
    (Fintype.equivFinOfCardEq hcard).symm
  let inner : Fin (pathCountAtInner n z) → LatticePath d := fun i =>
    innerFanPath z r sr hsr m (innerEquiv i)
  have hiStart : ∀ i, (inner i).start = z := by
    intro i
    simp [inner]
  have hiEdges : ∀ i j, i ≠ j →
      Disjoint (inner i).edgeSet (inner j).edgeSet := by
    intro i j hij
    exact innerFanPath_edgeDisjoint z r sr hsr m (innerEquiv.injective.ne hij)
  have hiSpheres : ∀ i x, x ∈ (inner i).vertices →
      x ∈ sphere d n ∪ sphere d (n + 1) := by
    intro i x hx
    exact innerFanPath_vertices_on_two_spheres z r sr hsr m hz
      hzReservoir (innerEquiv i) x (by simpa [inner] using hx)
  have hiLength : ∀ i,
      ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((inner i).edgeLength : ℤ) ∧
      ((inner i).edgeLength : ℤ) ≤ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋ := by
    intro i
    constructor
    · simpa [inner, m] using pathScale_length_lower (δ := δ) n
    · simpa [inner, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
  have hiFar : ∀ i j, i ≠ j → ∀ x ∈ (inner j).vertices,
      δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (inner i).finish x : ℝ) := by
    intro i j hij x hx
    apply innerFanPath_endpoint_far z r sr hsr m
      (δ ^ 3 * (n + 1 : ℝ))
      (separation_radius_le_pathScale hd hδpos hδ n hscale)
      (innerEquiv.injective.ne hij) x
    simpa [inner] using hx
  have hiUpper : ∀ i x, x ∈ (inner i).vertices → sr * x r ≤ sr * z r := by
    intro i x hx
    exact alternatingPath_reservoir_coordinate_le_start
      z (innerEquiv i).1.1 (boolSign (innerEquiv i).1.2) r sr
      (innerEquiv i).2.2 (natAbs_boolSign _) hsr m x
      (by simpa [inner, innerFanPath] using hx)
  have hiFinish : ∀ i, sr * (inner i).finish r = sr * z r - m := by
    intro i
    simp only [inner, innerFanPath, LatticePath.finish_alternatingPath,
      Pi.add_apply, Pi.sub_apply,
      signedBasis_of_ne (Ne.symm (innerEquiv i).2.2), signedBasis_same,
      add_zero]
    have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
    push_cast
    nlinarith
  obtain ⟨outer, hoStart, hoEdges, hoSpheres, hoLength, hoFar,
      hoLower, hoFinish⟩ :=
    exists_separated_outerFamily hd δ hδpos hδ hscale y hy hyNonAxis
      q r hqr hyq hyr hyReservoir
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
      change sr * y r ≤ sr * x r at hge
      omega
    · symm
      apply edgeDisjoint_of_vertices_disjoint
      rw [Set.disjoint_left]
      intro x hxo hxi
      have hle := hiUpper j x (by simpa [paths] using hxo)
      have hge := hoLower i x (by simpa [paths] using hxi)
      rw [hrsign] at hge
      change sr * y r ≤ sr * x r at hge
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
        (δ ^ 3 * (n + 1 : ℝ)) (-sr * y r) m
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
        (δ ^ 3 * (n + 1 : ℝ)) (sr * z r) m
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
