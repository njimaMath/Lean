import Disjoint_paths.Lemmas.Case5.Cross
import Disjoint_paths.Lemmas.FanCount
import Disjoint_paths.Lemmas.OuterFanCount
import Disjoint_paths.Lemmas.Reservoir
import Disjoint_paths.Lemmas.Scale
import Disjoint_paths.Lemmas.Family

/-!
# Case 5: the long nonzero neighboring coordinate

Both families use the joining coordinate as their reservoir.  The cross-family
proof uses exact coordinate formulas, including the two-coordinate estimate in
the short outer continuation.
-/

namespace DisjointPaths

noncomputable section

theorem case5_long_nonzero
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z y : LatticePoint d) (hz : z ∈ sphere d n)
    (hy : y ∈ sphere d (n + 1))
    (hzNonAxis : ¬ IsAxisPoint n z)
    (hyNonAxis : ¬ IsAxisPoint (n + 1) y)
    (r : Fin d) (hzr : z r ≠ 0)
    (hlong : pathScale δ n ≤ Int.natAbs (z r))
    (hrsign : coordinateSign (y r) = coordinateSign (z r))
    (hrstep : coordinateSign (z r) * y r =
      coordinateSign (z r) * z r + 1)
    (hother : ∀ k, k ≠ r → y k = z k) :
    ∃ paths : PathIndex n z y → LatticePath d,
      FamilyProperties (n := n) δ z y paths := by
  classical
  let m := pathScale δ n
  let sr := coordinateSign (z r)
  have hsr : Int.natAbs sr = 1 := natAbs_coordinateSign _
  have hm : 0 < m := by
    have : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
    omega
  have hyR : y r ≠ 0 := by
    intro hyzero
    rw [hyzero] at hrstep
    simp only [mul_zero] at hrstep
    have hzpositive : (0 : ℤ) < coordinateSign (z r) * z r := by
      rw [coordinateSign_mul_self]
      exact_mod_cast Int.natAbs_pos.mpr hzr
    omega
  have hzReservoir : (m : ℤ) ≤ sr * z r := by
    dsimp [sr]
    rw [coordinateSign_mul_self]
    exact_mod_cast hlong
  have hyReservoir : (m : ℤ) ≤ coordinateSign (y r) * y r := by
    rw [hrsign]
    dsimp [sr] at hzReservoir ⊢
    omega
  have hinnerCard : Fintype.card (InnerFanIndex z r) =
      pathCountAtInner n z := by
    rw [card_innerFanIndex z r hzr]
    simp [pathCountAtInner, hzNonAxis]
  let innerEquiv : Fin (pathCountAtInner n z) ≃ InnerFanIndex z r :=
    (Fintype.equivFinOfCardEq hinnerCard).symm
  have houterCard : Fintype.card (SupportExceptIndex y r) =
      pathCountAtOuter n y := by
    rw [card_supportExceptIndex y r hyR]
    simp [pathCountAtOuter, hyNonAxis]
  let outerEquiv : Fin (pathCountAtOuter n y) ≃ SupportExceptIndex y r :=
    (Fintype.equivFinOfCardEq houterCard).symm
  let helper (u : SupportExceptIndex y r) : Fin d :=
    thirdCoordinate hd u.1 r u.2.2
  have huHelper : ∀ u, u.1 ≠ helper u := by
    intro u
    exact Ne.symm (thirdCoordinate_ne_left hd u.1 r u.2.2)
  have hhelperR : ∀ u, helper u ≠ r := by
    intro u
    exact thirdCoordinate_ne_right hd u.1 r u.2.2
  let inner : Fin (pathCountAtInner n z) → LatticePath d := fun i =>
    innerFanPath z r sr hsr m (innerEquiv i)
  let outer : Fin (pathCountAtOuter n y) → LatticePath d := fun i =>
    let u := outerEquiv i
    outerPrivatePath y u.1 (helper u) r m u.2.1
      (huHelper u) u.2.2 (hhelperR u)
  let paths : PathIndex n z y → LatticePath d := Sum.elim inner outer
  refine ⟨paths, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [paths, inner]
  · intro i
    simp [paths, outer]
  · intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · apply innerFanPath_edgeDisjoint
      apply innerEquiv.injective.ne
      intro h
      apply hij
      simp [h]
    · let q := innerEquiv i
      let u := outerEquiv j
      simpa [paths, inner, outer, q, u] using
        innerFanPath_edgeDisjoint_outerPrivatePath_neighbor
          z y r sr hsr m q u.1 (helper u) u.2.1
          (huHelper u) u.2.2 (hhelperR u) hrsign hrstep hother
    · symm
      let q := innerEquiv j
      let u := outerEquiv i
      simpa [paths, inner, outer, q, u] using
        innerFanPath_edgeDisjoint_outerPrivatePath_neighbor
          z y r sr hsr m q u.1 (helper u) u.2.1
          (huHelper u) u.2.2 (hhelperR u) hrsign hrstep hother
    · let u := outerEquiv i
      let v := outerEquiv j
      have huv : u.1 ≠ v.1 := by
        intro huv
        apply hij
        simp only [Sum.inr.injEq]
        exact outerEquiv.injective (Subtype.ext huv)
      simpa [paths, outer, u, v] using
        outerPrivatePaths_edgeDisjoint_of_distinct y r
          u.1 (helper u) v.1 (helper v) m u.2.1 v.2.1
          (huHelper u) (hhelperR u) u.2.2
          (huHelper v) (hhelperR v) v.2.2 huv
  · intro i x hx
    rcases i with i | i
    · apply innerFanPath_vertices_on_two_spheres z r sr hsr m hz
        hzReservoir (innerEquiv i) x
      simpa [paths, inner] using hx
    · let u := outerEquiv i
      apply outerPrivatePath_vertices_on_two_spheres y u.1 (helper u) r m
        u.2.1 (huHelper u) u.2.2 (hhelperR u) hy hyReservoir x
      simpa [paths, outer, u] using hx
  · intro i
    rcases i with i | i <;> constructor
    · simpa [paths, inner, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, inner, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
    · simpa [paths, outer, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, outer, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
  · intro i j hij x hx
    rcases i with i | i <;> rcases j with j | j
    · have hijFin : i ≠ j := by
        intro h
        apply hij
        exact congrArg Sum.inl h
      apply innerFanPath_endpoint_far z r sr hsr m
        (δ ^ 3 * (n + 1 : ℝ))
        (separation_radius_le_pathScale hd hδpos hδ n hscale)
        (innerEquiv.injective.ne hijFin) x
      simpa [paths, inner] using hx
    · let q := innerEquiv i
      let u := outerEquiv j
      apply innerFanPath_endpoint_far_outerPrivatePath_neighbor
        z y r sr hsr m q u.1 (helper u) u.2.1
        (huHelper u) u.2.2 (hhelperR u) hrsign hrstep hother
        (δ ^ 3 * (n + 1 : ℝ))
        (separation_radius_le_pathScale hd hδpos hδ n hscale) x
      simpa [paths, inner, outer, q, u] using hx
    · let u := outerEquiv i
      let q := innerEquiv j
      apply outerPrivatePath_endpoint_far_innerFanPath_neighbor
        z y r sr hsr m q u.1 (helper u) u.2.1
        (huHelper u) u.2.2 (hhelperR u) hother
        (δ ^ 3 * (n + 1 : ℝ))
        (separation_radius_le_pathScale hd hδpos hδ n hscale) x
      simpa [paths, inner, outer, q, u] using hx
    · let u := outerEquiv i
      let v := outerEquiv j
      have huv : u.1 ≠ v.1 := by
        intro huv
        apply hij
        simp only [Sum.inr.injEq]
        exact outerEquiv.injective (Subtype.ext huv)
      apply outerPrivatePath_endpoint_far_of_distinct y r
        u.1 (helper u) v.1 (helper v) m u.2.1 v.2.1
        (huHelper u) (hhelperR u) u.2.2
        (huHelper v) (hhelperR v) v.2.2 huv
        (δ ^ 3 * (n + 1 : ℝ))
        (separation_radius_le_pathScale hd hδpos hδ n hscale) x
      simpa [paths, outer, v] using hx

end

end DisjointPaths
