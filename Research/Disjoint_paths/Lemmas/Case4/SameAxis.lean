import Disjoint_paths.Lemmas.FanCount
import Disjoint_paths.Lemmas.InwardAlternating
import Disjoint_paths.Lemmas.Scale
import Disjoint_paths.Lemmas.Separation

/-!
# Case 4: two axis points with the same axis

One positive zero-coordinate direction is removed from the inner fan and used
as the reservoir direction of the single outer path.  The two families can
then meet in at most the inner starting point, while their endpoints separate
in either the omitted coordinate or the private coordinate of the inner path.
-/

namespace DisjointPaths

noncomputable section

theorem case4_same_axis
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z y : LatticePoint d)
    (hz : z ∈ sphere d n) (hy : y ∈ sphere d (n + 1))
    (hzAxis : IsAxisPoint n z) (hyAxis : IsAxisPoint (n + 1) y)
    (p h : Fin d) (hhp : h ≠ p)
    (hzOff : ∀ r, r ≠ p → z r = 0)
    (hyOff : ∀ r, r ≠ p → y r = 0)
    (hzReservoir : (pathScale δ n : ℤ) ≤ coordinateSign (z p) * z p)
    (hyReservoir : (pathScale δ n : ℤ) ≤ coordinateSign (y p) * y p) :
    ∃ paths : PathIndex n z y → LatticePath d,
      (∀ i : Fin (pathCountAtInner n z), (paths (Sum.inl i)).start = z) ∧
      (∀ i : Fin (pathCountAtOuter n y), (paths (Sum.inr i)).start = y) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) := by
  classical
  let m := pathScale δ n
  have hm : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
  have hzH : z h = 0 := hzOff h hhp
  have hyH : y h = 0 := hyOff h hhp
  let omitted : InnerFanIndex z p :=
    ⟨(h, true), by simp [IsOutwardDirection, boolSign, hzH], hhp⟩
  let Selected := {q : InnerFanIndex z p // q ≠ omitted}
  letI : Fintype Selected := Fintype.ofFinite Selected
  have hpNonzero : z p ≠ 0 := by
    intro hpzero
    rw [coordinateSign_mul_self, hpzero] at hzReservoir
    norm_num at hzReservoir
    omega
  have hsupport : supportCard z = 1 :=
    supportCard_eq_one_of_isAxisPoint (by omega) hzAxis
  have hcardAll : Fintype.card (InnerFanIndex z p) = 2 * d - 2 := by
    rw [card_innerFanIndex z p hpNonzero, hsupport]
    omega
  have hcardSelected : Fintype.card Selected = 2 * d - 3 := by
    change Fintype.card {q : InnerFanIndex z p // ¬ q = omitted} = 2 * d - 3
    rw [Fintype.card_subtype_compl (fun q : InnerFanIndex z p => q = omitted)]
    simp [hcardAll]
    omega
  have hinnerCount : pathCountAtInner n z = 2 * d - 3 := by
    simp [pathCountAtInner, hzAxis]
  have houterCount : pathCountAtOuter n y = 1 := by
    simp [pathCountAtOuter, hyAxis]
  have hcard : Fintype.card Selected = pathCountAtInner n z := by
    rw [hcardSelected, hinnerCount]
  let indexEquiv : Fin (pathCountAtInner n z) ≃ Selected :=
    (Fintype.equivFinOfCardEq hcard).symm
  let innerPaths : Fin (pathCountAtInner n z) → LatticePath d := fun a =>
    innerFanPath z p (coordinateSign (z p)) (natAbs_coordinateSign _) m
      (indexEquiv a).1
  let outerPath : LatticePath d :=
    inwardAlternatingPath y p (coordinateSign (y p)) h 1 (Ne.symm hhp)
      (natAbs_coordinateSign _) (by norm_num) m
  let paths : PathIndex n z y → LatticePath d :=
    Sum.elim innerPaths (fun _ => outerPath)
  have hselectedSign : ∀ q : Selected,
      q.1.1.1 = h → boolSign q.1.1.2 = -1 := by
    intro q hqh
    have hne : q.1 ≠ omitted := q.2
    have hnotOne : boolSign q.1.1.2 ≠ 1 := by
      intro hs
      apply hne
      apply Subtype.ext
      apply Prod.ext hqh
      apply boolSign_injective
      simpa [omitted, boolSign] using hs
    rcases Int.natAbs_eq_iff.mp (natAbs_boolSign q.1.1.2) with hs | hs
    · exact False.elim (hnotOne hs)
    · simpa using hs
  have hinnerHUpper : ∀ a x, x ∈ (innerPaths a).vertices → x h ≤ 0 := by
    intro a x hx
    let q := indexEquiv a
    by_cases hqh : q.1.1.1 = h
    · have hs := hselectedSign q hqh
      have hge := LatticePath.alternatingPath_private_coordinate_ge_start
        z q.1.1.1 (boolSign q.1.1.2) p (coordinateSign (z p)) q.1.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x (by
          simpa [innerPaths, innerFanPath, q] using hx)
      rw [hqh, hs, hzH] at hge
      norm_num at hge
      omega
    · have hcoord := LatticePath.alternatingPath_other_coordinate
        z q.1.1.1 (boolSign q.1.1.2) p (coordinateSign (z p)) q.1.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x (by
          simpa [innerPaths, innerFanPath, q] using hx) h (Ne.symm hqh) hhp
      rw [hcoord, hzH]
  have houterPrivateUpper : ∀ (q : Selected) x,
      x ∈ outerPath.vertices →
        boolSign q.1.1.2 * x q.1.1.1 ≤
          boolSign q.1.1.2 * z q.1.1.1 := by
    intro q x hx
    by_cases hqh : q.1.1.1 = h
    · have hs := hselectedSign q hqh
      have hge := LatticePath.inwardAlternatingPath_reservoir_coordinate_ge_start
        y p (coordinateSign (y p)) h 1 (Ne.symm hhp)
        (natAbs_coordinateSign _) (by norm_num) m x (by
          simpa [outerPath] using hx)
      rw [hyH] at hge
      norm_num at hge
      rw [hqh, hs, hzH]
      norm_num
      omega
    · have hcoord := LatticePath.inwardAlternatingPath_other_coordinate
        y p (coordinateSign (y p)) h 1 (Ne.symm hhp)
        (natAbs_coordinateSign _) (by norm_num) m x (by
          simpa [outerPath] using hx) q.1.1.1 q.1.2.2 hqh
      rw [hcoord, hyOff q.1.1.1 q.1.2.2, hzOff q.1.1.1 q.1.2.2]
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    simp [paths, innerPaths]
  · intro a
    simp [paths, outerPath]
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · apply innerFanPath_edgeDisjoint
      have hab' : a ≠ b := by
        intro h
        apply hab
        cases h
        rfl
      exact fun h => hab' (indexEquiv.injective (Subtype.ext h))
    · apply LatticePath.edgeDisjoint_of_common_vertices_subsingleton _ _ z
      intro x hxi hxo
      let q := indexEquiv a
      have hge := LatticePath.alternatingPath_private_coordinate_ge_start
        z q.1.1.1 (boolSign q.1.1.2) p (coordinateSign (z p)) q.1.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x (by
          simpa [paths, innerPaths, innerFanPath, q] using hxi)
      have hle := houterPrivateUpper q x (by simpa [paths] using hxo)
      apply LatticePath.alternatingPath_eq_start_of_private_coordinate_eq
        z q.1.1.1 (boolSign q.1.1.2) p (coordinateSign (z p)) q.1.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x
        (by simpa [paths, innerPaths, innerFanPath, q] using hxi)
      exact le_antisymm hle hge
    · symm
      apply LatticePath.edgeDisjoint_of_common_vertices_subsingleton _ _ z
      intro x hxi hxo
      let q := indexEquiv b
      have hge := LatticePath.alternatingPath_private_coordinate_ge_start
        z q.1.1.1 (boolSign q.1.1.2) p (coordinateSign (z p)) q.1.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x (by
          simpa [paths, innerPaths, innerFanPath, q] using hxi)
      have hle := houterPrivateUpper q x (by simpa [paths] using hxo)
      apply LatticePath.alternatingPath_eq_start_of_private_coordinate_eq
        z q.1.1.1 (boolSign q.1.1.2) p (coordinateSign (z p)) q.1.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x
        (by simpa [paths, innerPaths, innerFanPath, q] using hxi)
      exact le_antisymm hle hge
    · exfalso
      have hab' : a = b := by
        apply Fin.ext
        rw [houterCount] at a b
        omega
      exact hab (congrArg Sum.inr hab')
  · intro a x hx
    rcases a with a | a
    · apply innerFanPath_vertices_on_two_spheres z p (coordinateSign (z p))
        (natAbs_coordinateSign _) m hz hzReservoir (indexEquiv a).1 x
      simpa [paths, innerPaths] using hx
    · apply LatticePath.inwardAlternatingPath_vertices_on_two_spheres
        y p (coordinateSign (y p)) h 1 (Ne.symm hhp)
        (natAbs_coordinateSign _) (by norm_num) m hy hyReservoir (by simp [hyH]) x
      simpa [paths, outerPath] using hx
  · intro a
    rcases a with a | a <;> constructor
    · simpa [paths, innerPaths, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, innerPaths, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
    · simpa [paths, outerPath, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, outerPath, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
  · intro a b hab x hx
    rcases a with a | a <;> rcases b with b | b
    · apply innerFanPath_endpoint_far z p (coordinateSign (z p))
        (natAbs_coordinateSign _) m (δ ^ 3 * (n + 1 : ℝ))
        (separation_radius_le_pathScale hd hδpos hδ n hscale)
        (by
          have hab' : a ≠ b := by
            intro h
            apply hab
            cases h
            rfl
          intro h
          exact hab' (indexEquiv.injective (Subtype.ext h))) x
      simpa [paths, innerPaths] using hx
    · let q := indexEquiv a
      apply endpoint_far_from_vertices_of_signed_coordinate_gap
        (innerPaths a) outerPath q.1.1.1 (boolSign q.1.1.2)
        (natAbs_boolSign _) (δ ^ 3 * (n + 1 : ℝ))
        (boolSign q.1.1.2 * z q.1.1.1) m
        (separation_radius_le_pathScale hd hδpos hδ n hscale) (by positivity)
      · have hfinish := alternatingPath_finish_private_signed
          z q.1.1.1 (boolSign q.1.1.2) p (coordinateSign (z p))
          q.1.2.2 (natAbs_boolSign _) (natAbs_coordinateSign _) m
        simpa [innerPaths, innerFanPath, q] using hfinish.symm.le
      · exact houterPrivateUpper q
      · simpa [paths, outerPath] using hx
    · apply endpoint_far_from_vertices_of_signed_coordinate_gap
        outerPath (innerPaths b) h 1 (by norm_num)
        (δ ^ 3 * (n + 1 : ℝ)) 0 m
        (separation_radius_le_pathScale hd hδpos hδ n hscale) (by positivity)
      · rw [LatticePath.finish_inwardAlternatingPath]
        simp [signedBasis, hhp, hyH]
      · intro w hw
        have := hinnerHUpper b w hw
        norm_num at this ⊢
        exact this
      · simpa [paths, innerPaths] using hx
    · exfalso
      have hab' : a = b := by
        apply Fin.ext
        rw [houterCount] at a b
        omega
      exact hab (congrArg Sum.inr hab')

end

end DisjointPaths
