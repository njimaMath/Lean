import Disjoint_paths.Lemmas.SeparatedOuterFan
import Disjoint_paths.Lemmas.OuterFanCount

/-!
# Complete outer family directed away from a separator
-/

namespace DisjointPaths

noncomputable section

theorem exists_separated_outerFamily {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (y : LatticePoint d) (hy : y ∈ sphere d (n + 1))
    (hnotAxis : ¬ IsAxisPoint (n + 1) y)
    (q r : Fin d) (hqr : q ≠ r) (hyq : y q ≠ 0) (hyr : y r ≠ 0)
    (hqReservoir : ((3 * pathScale δ n : ℕ) : ℤ) ≤
      coordinateSign (y q) * y q) :
    ∃ paths : Fin (pathCountAtOuter n y) → LatticePath d,
      (∀ i, (paths i).start = y) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i, ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) ∧
      (∀ i x, x ∈ (paths i).vertices →
        coordinateSign (y r) * y r ≤ coordinateSign (y r) * x r) ∧
      (∀ i, coordinateSign (y r) * y r + pathScale δ n ≤
        coordinateSign (y r) * (paths i).finish r) := by
  let m := pathScale δ n
  have hm : 0 < m := by
    have : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
    omega
  have hcard : Fintype.card (SupportExceptIndex y r) = pathCountAtOuter n y := by
    rw [card_supportExceptIndex y r hyr]
    simp [pathCountAtOuter, hnotAxis]
  let indexEquiv : Fin (pathCountAtOuter n y) ≃ SupportExceptIndex y r :=
    (Fintype.equivFinOfCardEq hcard).symm
  let familyPath (u : SupportExceptIndex y r) : LatticePath d :=
    if huq : u.1 = q then
      exceptionalSeparatedOuterPath y q r hqr m
    else
      separatedOuterPath y u.1 q r huq u.2.2 hqr m
  let paths : Fin (pathCountAtOuter n y) → LatticePath d := fun i ↦
    familyPath (indexEquiv i)
  have hq3 : ((3 * m : ℕ) : ℤ) ≤ coordinateSign (y q) * y q := by
    simpa [m] using hqReservoir
  have hq2 : ((2 * m : ℕ) : ℤ) ≤ coordinateSign (y q) * y q := by
    have hcast : ((2 * m : ℕ) : ℤ) ≤ ((3 * m : ℕ) : ℤ) := by
      exact_mod_cast (show 2 * m ≤ 3 * m by omega)
    exact hcast.trans hq3
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    let u := indexEquiv i
    by_cases huq : u.1 = q
    · simp [paths, familyPath, u, huq]
    · simp [paths, familyPath, u, huq]
  · intro i j hij
    let u := indexEquiv i
    let v := indexEquiv j
    have huv : u ≠ v := indexEquiv.injective.ne hij
    by_cases huq : u.1 = q <;> by_cases hvq : v.1 = q
    · exfalso
      apply huv
      exact Subtype.ext (huq.trans hvq.symm)
    · have hordinary := separatedOuterPath_edgeDisjoint_exceptional
        y v.1 q r hvq v.2.2 hqr m hm v.2.1
      simpa [paths, familyPath, u, v, huq, hvq] using hordinary.symm
    · have hordinary := separatedOuterPath_edgeDisjoint_exceptional
        y u.1 q r huq u.2.2 hqr m hm u.2.1
      simpa [paths, familyPath, u, v, huq, hvq] using hordinary
    · have huvCoord : u.1 ≠ v.1 := by
        intro h
        apply huv
        exact Subtype.ext h
      simpa [paths, familyPath, u, v, huq, hvq] using
        separatedOuterPaths_edgeDisjoint_of_distinct
        y q r hqr m hm u.1 v.1 u.2.1 v.2.1 huq u.2.2 hvq v.2.2 huvCoord
  · intro i x hx
    let u := indexEquiv i
    by_cases huq : u.1 = q
    · apply exceptionalSeparatedOuterPath_vertices_on_two_spheres
        y q r hqr m hy hq3 x
      simpa [paths, familyPath, u, huq] using hx
    · apply separatedOuterPath_vertices_on_two_spheres
        y u.1 q r huq u.2.2 hqr m hy hq2 x
      simpa [paths, familyPath, u, huq] using hx
  · intro i
    let u := indexEquiv i
    by_cases huq : u.1 = q
    · constructor
      · have hlower := pathScale_length_lower (δ := δ) n
        simpa [paths, familyPath, u, huq, m] using hlower.trans
          (show ((2 * m : ℕ) : ℤ) ≤ ((6 * m : ℕ) : ℤ) by
            exact_mod_cast (show 2 * m ≤ 6 * m by omega))
      · simpa [paths, familyPath, u, huq, m] using
          six_pathScale_length_upper hd δ n
    · have hab := separatedOuterInitial_add_remaining y u.1 m
      have hlenLower : 2 * m ≤
          2 * separatedOuterInitialLength y u.1 m +
            4 * separatedOuterRemainingLength y u.1 m := by omega
      have hlenUpper :
          2 * separatedOuterInitialLength y u.1 m +
            4 * separatedOuterRemainingLength y u.1 m ≤ 6 * m := by omega
      constructor
      · have hlower := pathScale_length_lower (δ := δ) n
        exact hlower.trans (by
          simpa [paths, familyPath, u, huq] using (show
            ((2 * m : ℕ) : ℤ) ≤
              ((2 * separatedOuterInitialLength y u.1 m +
                4 * separatedOuterRemainingLength y u.1 m : ℕ) : ℤ) by
            exact_mod_cast hlenLower))
      · have hupper := six_pathScale_length_upper hd δ n
        apply (show ((paths i).edgeLength : ℤ) ≤ ((6 * m : ℕ) : ℤ) by
          simpa [paths, familyPath, u, huq] using (show
            ((2 * separatedOuterInitialLength y u.1 m +
              4 * separatedOuterRemainingLength y u.1 m : ℕ) : ℤ) ≤
                ((6 * m : ℕ) : ℤ) by exact_mod_cast hlenUpper)).trans
        simpa [m] using hupper
  · intro i j hij x hx
    let u := indexEquiv i
    let v := indexEquiv j
    have huv : u ≠ v := indexEquiv.injective.ne hij
    let radius := δ ^ 3 * (n + 1 : ℝ)
    have hradius : radius ≤ (m : ℝ) :=
      separation_radius_le_pathScale hd hδpos hδ n hscale
    by_cases huq : u.1 = q <;> by_cases hvq : v.1 = q
    · exfalso
      apply huv
      exact Subtype.ext (huq.trans hvq.symm)
    · have hfar := exceptionalSeparatedOuterPath_endpoint_far_ordinary
        y v.1 q r hvq v.2.2 hqr m radius hradius x
        (by simpa [paths, familyPath, v, hvq] using hx)
      simpa [radius, paths, familyPath, u, huq] using hfar
    · have hfar := separatedOuterPath_endpoint_far_exceptional
        y u.1 q r huq u.2.2 hqr m radius hradius x
        (by simpa [paths, familyPath, v, hvq] using hx)
      simpa [radius, paths, familyPath, u, huq] using hfar
    · have huvCoord : u.1 ≠ v.1 := by
        intro h
        apply huv
        exact Subtype.ext h
      have hfar := separatedOuterPath_endpoint_far_of_distinct
        y q r hqr m u.1 v.1 huq u.2.2 hvq v.2.2 huvCoord radius hradius x
        (by simpa [paths, familyPath, v, hvq] using hx)
      simpa [radius, paths, familyPath, u, huq] using hfar
  · intro i x hx
    let u := indexEquiv i
    by_cases huq : u.1 = q
    · exact LatticePath.inwardAlternatingPath_reservoir_coordinate_ge_start
        y q (coordinateSign (y q)) r (coordinateSign (y r)) hqr
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) (3 * m) x
        (by simpa [paths, familyPath, u, huq, exceptionalSeparatedOuterPath] using hx)
    · exact (separatedOuterPath_separating_coordinate_bounds
        y u.1 q r huq u.2.2 hqr m x
        (by simpa [paths, familyPath, u, huq] using hx)).1
  · intro i
    let u := indexEquiv i
    by_cases huq : u.1 = q
    · rw [show paths i = exceptionalSeparatedOuterPath y q r hqr m by
          simp [paths, familyPath, u, huq],
        exceptionalSeparatedOuterPath_finish_separating_coordinate]
      omega
    · rw [show paths i = separatedOuterPath y u.1 q r huq u.2.2 hqr m by
          simp [paths, familyPath, u, huq],
        separatedOuterPath_finish_separating_coordinate]

end

end DisjointPaths
