import Disjoint_paths.Lemmas.FanCount
import Disjoint_paths.Lemmas.InwardAlternating
import Disjoint_paths.Lemmas.Scale
import Disjoint_paths.Lemmas.Separation

/-!
# Case 2: a near outer-axis point

The inner fan uses the outer axis as its reservoir.  A second nonzero inner
coordinate supplies the outer path's reservoir in the opposite sign.  Thus
no required inner direction is discarded.
-/

namespace DisjointPaths

noncomputable section

theorem case2_near_axis_nonAxis
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z y : LatticePoint d)
    (hz : z ∈ sphere d n) (hy : y ∈ sphere d (n + 1))
    (hzNonAxis : ¬ IsAxisPoint n z) (hyAxis : IsAxisPoint (n + 1) y)
    (p h : Fin d) (hhp : h ≠ p) (hzh : z h ≠ 0)
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
  let sh := -coordinateSign (z h)
  have hsh : Int.natAbs sh = 1 := by simp [sh, natAbs_coordinateSign]
  have hyH : y h = 0 := hyOff h hhp
  have hpNonzero : z p ≠ 0 := by
    intro hpzero
    rw [coordinateSign_mul_self, hpzero] at hzReservoir
    norm_num at hzReservoir
    have hm : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
    omega
  have hcard : Fintype.card (InnerFanIndex z p) = pathCountAtInner n z := by
    rw [card_innerFanIndex z p hpNonzero]
    simp [pathCountAtInner, hzNonAxis]
  let indexEquiv : Fin (pathCountAtInner n z) ≃ InnerFanIndex z p :=
    (Fintype.equivFinOfCardEq hcard).symm
  let innerPaths : Fin (pathCountAtInner n z) → LatticePath d := fun a =>
    innerFanPath z p (coordinateSign (z p)) (natAbs_coordinateSign _) m
      (indexEquiv a)
  let outerPath : LatticePath d :=
    inwardAlternatingPath y p (coordinateSign (y p)) h sh (Ne.symm hhp)
      (natAbs_coordinateSign _) hsh m
  let paths : PathIndex n z y → LatticePath d :=
    Sum.elim innerPaths (fun _ => outerPath)
  have houterCount : pathCountAtOuter n y = 1 := by
    simp [pathCountAtOuter, hyAxis]
  have hindexSign : ∀ q : InnerFanIndex z p,
      q.1.1 = h → boolSign q.1.2 = coordinateSign (z h) := by
    intro q hqh
    apply boolSign_eq_coordinateSign_of_outward z h q.1.2 hzh
    simpa [IsOutwardDirection, hqh] using q.2.1
  have hinnerHUpper : ∀ a x, x ∈ (innerPaths a).vertices → sh * x h ≤ 0 := by
    intro a x hx
    let q := indexEquiv a
    by_cases hqh : q.1.1 = h
    · have hs := hindexSign q hqh
      have hge := LatticePath.alternatingPath_private_coordinate_ge_start
        z q.1.1 (boolSign q.1.2) p (coordinateSign (z p)) q.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x (by
          simpa [innerPaths, innerFanPath, q] using hx)
      have hpositive : 0 < coordinateSign (z h) * z h := by
        rw [coordinateSign_mul_self]
        exact_mod_cast Int.natAbs_pos.mpr hzh
      rw [hqh, hs] at hge
      dsimp [sh]
      linarith
    · have hcoord := LatticePath.alternatingPath_other_coordinate
        z q.1.1 (boolSign q.1.2) p (coordinateSign (z p)) q.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x (by
          simpa [innerPaths, innerFanPath, q] using hx) h (Ne.symm hqh) hhp
      rw [hcoord]
      have hpositive : 0 < coordinateSign (z h) * z h := by
        rw [coordinateSign_mul_self]
        exact_mod_cast Int.natAbs_pos.mpr hzh
      dsimp [sh]
      linarith
  have houterPrivateUpper : ∀ (q : InnerFanIndex z p) x,
      x ∈ outerPath.vertices →
        boolSign q.1.2 * x q.1.1 ≤ boolSign q.1.2 * z q.1.1 := by
    intro q x hx
    by_cases hqh : q.1.1 = h
    · have hs := hindexSign q hqh
      have hge := LatticePath.inwardAlternatingPath_reservoir_coordinate_ge_start
        y p (coordinateSign (y p)) h sh (Ne.symm hhp)
        (natAbs_coordinateSign _) hsh m x (by simpa [outerPath] using hx)
      have hstart : coordinateSign (z h) * z h ≥ 0 := by
        rw [coordinateSign_mul_self]
        positivity
      rw [hyH] at hge
      rw [hqh, hs]
      dsimp [sh] at hge ⊢
      linarith
    · have hcoord := LatticePath.inwardAlternatingPath_other_coordinate
        y p (coordinateSign (y p)) h sh (Ne.symm hhp)
        (natAbs_coordinateSign _) hsh m x (by simpa [outerPath] using hx)
        q.1.1 q.2.2 hqh
      rw [hcoord, hyOff q.1.1 q.2.2]
      simpa [IsOutwardDirection] using q.2.1
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    simp [paths, innerPaths]
  · intro a
    simp [paths, outerPath]
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · apply innerFanPath_edgeDisjoint
      exact indexEquiv.injective.ne (by
        intro h
        apply hab
        cases h
        rfl)
    · apply LatticePath.edgeDisjoint_of_common_vertices_subsingleton _ _ z
      intro x hxi hxo
      let q := indexEquiv a
      have hge := LatticePath.alternatingPath_private_coordinate_ge_start
        z q.1.1 (boolSign q.1.2) p (coordinateSign (z p)) q.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x (by
          simpa [paths, innerPaths, innerFanPath, q] using hxi)
      have hle := houterPrivateUpper q x (by simpa [paths] using hxo)
      apply LatticePath.alternatingPath_eq_start_of_private_coordinate_eq
        z q.1.1 (boolSign q.1.2) p (coordinateSign (z p)) q.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x
        (by simpa [paths, innerPaths, innerFanPath, q] using hxi)
      exact le_antisymm hle hge
    · symm
      apply LatticePath.edgeDisjoint_of_common_vertices_subsingleton _ _ z
      intro x hxi hxo
      let q := indexEquiv b
      have hge := LatticePath.alternatingPath_private_coordinate_ge_start
        z q.1.1 (boolSign q.1.2) p (coordinateSign (z p)) q.2.2
        (natAbs_boolSign _) (natAbs_coordinateSign _) m x (by
          simpa [paths, innerPaths, innerFanPath, q] using hxi)
      have hle := houterPrivateUpper q x (by simpa [paths] using hxo)
      apply LatticePath.alternatingPath_eq_start_of_private_coordinate_eq
        z q.1.1 (boolSign q.1.2) p (coordinateSign (z p)) q.2.2
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
        (natAbs_coordinateSign _) m hz hzReservoir (indexEquiv a) x
      simpa [paths, innerPaths] using hx
    · apply LatticePath.inwardAlternatingPath_vertices_on_two_spheres
        y p (coordinateSign (y p)) h sh (Ne.symm hhp)
        (natAbs_coordinateSign _) hsh m hy hyReservoir (by simp [hyH, sh]) x
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
    · have hab' : a ≠ b := by
        intro h
        apply hab
        cases h
        rfl
      apply innerFanPath_endpoint_far z p (coordinateSign (z p))
        (natAbs_coordinateSign _) m (δ ^ 3 * (n + 1 : ℝ))
        (separation_radius_le_pathScale hd hδpos hδ n hscale)
        (q := indexEquiv a) (r := indexEquiv b)
        (indexEquiv.injective.ne hab') x
      simpa [paths, innerPaths] using hx
    · let q := indexEquiv a
      apply endpoint_far_from_vertices_of_signed_coordinate_gap
        (innerPaths a) outerPath q.1.1 (boolSign q.1.2)
        (natAbs_boolSign _) (δ ^ 3 * (n + 1 : ℝ))
        (boolSign q.1.2 * z q.1.1) m
        (separation_radius_le_pathScale hd hδpos hδ n hscale) (by positivity)
      · have hfinish := alternatingPath_finish_private_signed
          z q.1.1 (boolSign q.1.2) p (coordinateSign (z p)) q.2.2
          (natAbs_boolSign _) (natAbs_coordinateSign _) m
        simpa [innerPaths, innerFanPath, q] using hfinish.symm.le
      · exact houterPrivateUpper q
      · simpa [paths, outerPath] using hx
    · apply endpoint_far_from_vertices_of_signed_coordinate_gap
        outerPath (innerPaths b) h sh hsh
        (δ ^ 3 * (n + 1 : ℝ)) 0 m
        (separation_radius_le_pathScale hd hδpos hδ n hscale) (by positivity)
      · rw [LatticePath.finish_inwardAlternatingPath]
        have hsq := sq_eq_one_of_natAbs_eq_one sh hsh
        simp [signedBasis, hhp, hyH]
        nlinarith
      · intro w hw
        exact hinnerHUpper b w hw
      · simpa [paths, innerPaths] using hx
    · exfalso
      have hab' : a = b := by
        apply Fin.ext
        rw [houterCount] at a b
        omega
      exact hab (congrArg Sum.inr hab')

end

end DisjointPaths
