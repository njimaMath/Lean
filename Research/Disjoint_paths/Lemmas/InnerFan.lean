import Disjoint_paths.Lemmas.Reservoir

/-!
# The ordinary inner fan

For a non-axis point on the inner sphere, this module constructs the exact
number of required paths.  A maximal coordinate is used as the reservoir.
-/

namespace DisjointPaths

noncomputable section

theorem exists_nonAxis_innerFan
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z : LatticePoint d) (hz : z ∈ sphere d n)
    (hnotAxis : ¬IsAxisPoint n z) :
    ∃ paths : Fin (pathCountAtInner n z) → LatticePath d,
      (∀ i, (paths i).start = z) ∧
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
        z r - (pathScale δ n : ℤ) ≤ x r ∧
          x r ≤ z r + (pathScale δ n : ℤ)) := by
  let m := pathScale δ n
  have hdm : d * m ≤ n := pathScale_reservoir_bound hd hn hδpos hδ
  obtain ⟨p, hpReservoir⟩ := exists_reservoir_coordinate
    (show 1 ≤ d by omega) z hz hdm
  have hmLarge : 12 ≤ m := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    exact hscale
  have hpNonzero : z p ≠ 0 := by
    intro hpzero
    simp [hpzero, m] at hpReservoir
    omega
  have hcard : Fintype.card (InnerFanIndex z p) = pathCountAtInner n z := by
    rw [card_innerFanIndex z p hpNonzero]
    simp [pathCountAtInner, hnotAxis]
  let indexEquiv : Fin (pathCountAtInner n z) ≃ InnerFanIndex z p :=
    (Fintype.equivFinOfCardEq hcard).symm
  let paths : Fin (pathCountAtInner n z) → LatticePath d := fun i =>
    innerFanPath z p (coordinateSign (z p)) (natAbs_coordinateSign (z p)) m
      (indexEquiv i)
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [paths]
  · intro i j hij
    apply innerFanPath_edgeDisjoint
    exact indexEquiv.injective.ne hij
  · intro i x hx
    apply innerFanPath_vertices_on_two_spheres z p (coordinateSign (z p))
      (natAbs_coordinateSign (z p)) m hz hpReservoir (indexEquiv i) x hx
  · intro i
    constructor
    · simpa [paths, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
  · intro i j hij x hx
    apply innerFanPath_endpoint_far z p (coordinateSign (z p))
      (natAbs_coordinateSign (z p)) m
      (δ ^ 3 * (n + 1 : ℝ))
      (separation_radius_le_pathScale hd hδpos hδ n hscale)
      (indexEquiv.injective.ne hij) x hx
  · intro i x hx r
    constructor
    · simpa [paths, m] using innerFanPath_coordinate_lower_bound z p
        (coordinateSign (z p)) (natAbs_coordinateSign (z p)) m (indexEquiv i) x hx r
    · simpa [paths, m] using innerFanPath_coordinate_upper_bound z p
        (coordinateSign (z p)) (natAbs_coordinateSign (z p)) m (indexEquiv i) x hx r

theorem exists_axis_innerFan
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z : LatticePoint d) (hz : z ∈ sphere d n)
    (haxis : IsAxisPoint n z) :
    ∃ paths : Fin (pathCountAtInner n z) → LatticePath d,
      (∀ i, (paths i).start = z) ∧
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
        z r - (pathScale δ n : ℤ) ≤ x r ∧
          x r ≤ z r + (pathScale δ n : ℤ)) := by
  let m := pathScale δ n
  have hdm : d * m ≤ n := pathScale_reservoir_bound hd hn hδpos hδ
  obtain ⟨p, hpReservoir⟩ := exists_reservoir_coordinate
    (show 1 ≤ d by omega) z hz hdm
  have hmLarge : 12 ≤ m := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    exact hscale
  have hpNonzero : z p ≠ 0 := by
    intro hpzero
    simp [hpzero, m] at hpReservoir
    omega
  have hsupport : supportCard z = 1 :=
    supportCard_eq_one_of_isAxisPoint (by omega) haxis
  have hcardAll : Fintype.card (InnerFanIndex z p) = 2 * d - 2 := by
    rw [card_innerFanIndex z p hpNonzero, hsupport]
    omega
  have hcount : pathCountAtInner n z = 2 * d - 3 := by
    simp [pathCountAtInner, haxis]
  have hle : pathCountAtInner n z ≤ Fintype.card (InnerFanIndex z p) := by
    rw [hcardAll, hcount]
    omega
  let allEquiv := Fintype.equivFin (InnerFanIndex z p)
  let fanIndex : Fin (pathCountAtInner n z) → InnerFanIndex z p := fun i =>
    allEquiv.symm ⟨i.val, lt_of_lt_of_le i.isLt hle⟩
  have hfanIndex : Function.Injective fanIndex := by
    intro i j hij
    have hfin := allEquiv.symm.injective hij
    have hval : i.val = j.val := congrArg
      (fun k : Fin (Fintype.card (InnerFanIndex z p)) => k.val) hfin
    exact Fin.ext hval
  let paths : Fin (pathCountAtInner n z) → LatticePath d := fun i =>
    innerFanPath z p (coordinateSign (z p)) (natAbs_coordinateSign (z p)) m
      (fanIndex i)
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [paths]
  · intro i j hij
    apply innerFanPath_edgeDisjoint
    exact hfanIndex.ne hij
  · intro i x hx
    apply innerFanPath_vertices_on_two_spheres z p (coordinateSign (z p))
      (natAbs_coordinateSign (z p)) m hz hpReservoir (fanIndex i) x hx
  · intro i
    constructor
    · simpa [paths, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
  · intro i j hij x hx
    apply innerFanPath_endpoint_far z p (coordinateSign (z p))
      (natAbs_coordinateSign (z p)) m
      (δ ^ 3 * (n + 1 : ℝ))
      (separation_radius_le_pathScale hd hδpos hδ n hscale)
      (hfanIndex.ne hij) x hx
  · intro i x hx r
    constructor
    · simpa [paths, m] using innerFanPath_coordinate_lower_bound z p
        (coordinateSign (z p)) (natAbs_coordinateSign (z p)) m (fanIndex i) x hx r
    · simpa [paths, m] using innerFanPath_coordinate_upper_bound z p
        (coordinateSign (z p)) (natAbs_coordinateSign (z p)) m (fanIndex i) x hx r

theorem exists_innerFan
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z : LatticePoint d) (hz : z ∈ sphere d n) :
    ∃ paths : Fin (pathCountAtInner n z) → LatticePath d,
      (∀ i, (paths i).start = z) ∧
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
        z r - (pathScale δ n : ℤ) ≤ x r ∧
          x r ≤ z r + (pathScale δ n : ℤ)) := by
  by_cases haxis : IsAxisPoint n z
  · exact exists_axis_innerFan hd δ hδpos hδ hn hscale z hz haxis
  · exact exists_nonAxis_innerFan hd δ hδpos hδ hn hscale z hz haxis

end

end DisjointPaths
