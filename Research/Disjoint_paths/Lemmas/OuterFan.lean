import Disjoint_paths.Lemmas.OuterFanCount
import Disjoint_paths.Lemmas.Reservoir
import Disjoint_paths.Lemmas.Scale

/-!
# Exact outer fan in the long-coordinate regime
-/

namespace DisjointPaths

noncomputable section

theorem exists_long_nonAxis_outerFan
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (y : LatticePoint d) (hy : y ∈ sphere d (n + 1))
    (p : Fin d) (hp : y p ≠ 0)
    (hall : ∀ i, i ≠ p → y i ≠ 0 →
      (pathScale δ n : ℤ) ≤ coordinateSign (y i) * y i)
    (hnotAxis : ¬IsAxisPoint (n + 1) y) :
    ∃ paths : Fin (pathCountAtOuter n y) → LatticePath d,
      (∀ i, (paths i).start = y) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) ∧
      (∀ i x, x ∈ (paths i).vertices → ∀ r,
        y r - (pathScale δ n : ℤ) ≤ x r ∧
          x r ≤ y r + (pathScale δ n : ℤ)) := by
  let m := pathScale δ n
  have hm : 1 ≤ m := by
    have : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
    omega
  have hcard : Fintype.card (LongOuterIndex y p m) = pathCountAtOuter n y := by
    rw [card_longOuterIndex y p m hm hp hall]
    simp [pathCountAtOuter, hnotAxis]
  let indexEquiv : Fin (pathCountAtOuter n y) ≃ LongOuterIndex y p m :=
    (Fintype.equivFinOfCardEq hcard).symm
  let paths : Fin (pathCountAtOuter n y) → LatticePath d := fun i =>
    longOuterFanPath y p (coordinateSign (y p))
      (natAbs_coordinateSign (y p)) m (indexEquiv i)
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [paths]
  · intro i j hij
    apply longOuterFanPath_edgeDisjoint
    exact indexEquiv.injective.ne hij
  · intro i x hx
    apply longOuterFanPath_vertices_on_two_spheres y p (coordinateSign (y p))
      (natAbs_coordinateSign (y p)) m hy (by
        rw [coordinateSign_mul_self]
        positivity) (indexEquiv i) x hx
  · intro i
    constructor
    · simpa [paths, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
  · intro i j hij x hx
    apply longOuterFanPath_endpoint_far y p (coordinateSign (y p))
      (natAbs_coordinateSign (y p)) m
      (δ ^ 3 * (n + 1 : ℝ))
      (separation_radius_le_pathScale hd hδpos hδ n hscale)
      (indexEquiv.injective.ne hij) x hx
  · intro i x hx r
    constructor
    · simpa [paths, m] using longOuterFanPath_coordinate_lower_bound y p
        (coordinateSign (y p)) (natAbs_coordinateSign (y p)) m (indexEquiv i) x hx r
    · simpa [paths, m] using longOuterFanPath_coordinate_upper_bound y p
        (coordinateSign (y p)) (natAbs_coordinateSign (y p)) m (indexEquiv i) x hx r

theorem exists_axis_outerFan
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (_hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (y : LatticePoint d) (hy : y ∈ sphere d (n + 1))
    (haxis : IsAxisPoint (n + 1) y) :
    ∃ paths : Fin (pathCountAtOuter n y) → LatticePath d,
      (∀ i, (paths i).start = y) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) ∧
      (∀ i x, x ∈ (paths i).vertices → ∀ r,
        y r - (pathScale δ n : ℤ) ≤ x r ∧
          x r ≤ y r + (pathScale δ n : ℤ)) := by
  let m := pathScale δ n
  have hdm : d * m ≤ n := pathScale_reservoir_bound hd hn hδpos hδ
  obtain ⟨p, hpReservoir⟩ := exists_reservoir_coordinate
    (show 1 ≤ d by omega) y hy (by omega : d * m ≤ n + 1)
  letI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨q, hqp⟩ := exists_ne p
  let path := inwardAlternatingPath y p (coordinateSign (y p))
    q (coordinateSign (y q)) (Ne.symm hqp)
    (natAbs_coordinateSign (y p)) (natAbs_coordinateSign (y q)) m
  have hcount : pathCountAtOuter n y = 1 := by
    simp [pathCountAtOuter, haxis]
  let paths : Fin (pathCountAtOuter n y) → LatticePath d := fun _ => path
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [paths, path]
  · intro i j hij
    exfalso
    apply hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  · intro i x hx
    apply LatticePath.inwardAlternatingPath_vertices_on_two_spheres
      y p (coordinateSign (y p)) q (coordinateSign (y q)) (Ne.symm hqp)
      (natAbs_coordinateSign (y p)) (natAbs_coordinateSign (y q)) m hy
      hpReservoir (by
        rw [coordinateSign_mul_self]
        positivity) x
    simpa [paths, path] using hx
  · intro i
    constructor
    · simpa [paths, path, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, path, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
  · intro i j hij
    exfalso
    apply hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  · intro i x hx r
    have hdisp := LatticePath.inwardAlternatingPath_coordinate_displacement_le
      y p (coordinateSign (y p)) q (coordinateSign (y q)) (Ne.symm hqp)
      (natAbs_coordinateSign (y p)) (natAbs_coordinateSign (y q)) m x
      (by simpa [paths, path] using hx) r
    constructor
    · exact coordinate_sub_le_of_natAbs_sub_le x y r m hdisp
    · exact coordinate_le_add_of_natAbs_sub_le x y r m hdisp

end

end DisjointPaths
