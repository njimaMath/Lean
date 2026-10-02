import Disjoint_paths.Lemmas.OuterFanCount
import Disjoint_paths.Lemmas.OuterPrivateFan
import Disjoint_paths.Lemmas.Reservoir

/-!
# The complete continued outer family

Every non-reservoir nonzero coordinate supplies one private path.  Short
private coordinates use the continuation construction, so no lower bound on
the individual private coordinates is required.
-/

namespace DisjointPaths

noncomputable section

theorem exists_nonAxis_outerPrivateFamily
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (y : LatticePoint d) (hy : y ∈ sphere d (n + 1))
    (hnotAxis : ¬ IsAxisPoint (n + 1) y) :
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
  have hm : 12 ≤ m :=
    (Nat.le_floor_iff (by positivity)).mpr hscale
  have hpNonzero : y p ≠ 0 := by
    intro hpzero
    rw [coordinateSign_mul_self, hpzero] at hpReservoir
    norm_num at hpReservoir
    omega
  have hcard : Fintype.card (SupportExceptIndex y p) = pathCountAtOuter n y := by
    rw [card_supportExceptIndex y p hpNonzero]
    simp [pathCountAtOuter, hnotAxis]
  let indexEquiv : Fin (pathCountAtOuter n y) ≃ SupportExceptIndex y p :=
    (Fintype.equivFinOfCardEq hcard).symm
  let helper (q : SupportExceptIndex y p) : Fin d :=
    thirdCoordinate hd q.1 p q.2.2
  have hhelperPrivate : ∀ q, q.1 ≠ helper q := by
    intro q
    exact Ne.symm (thirdCoordinate_ne_left hd q.1 p q.2.2)
  have hhelperReservoir : ∀ q, helper q ≠ p := by
    intro q
    exact thirdCoordinate_ne_right hd q.1 p q.2.2
  let paths : Fin (pathCountAtOuter n y) → LatticePath d := fun a =>
    let q := indexEquiv a
    outerPrivatePath y q.1 (helper q) p m q.2.1
      (hhelperPrivate q) q.2.2 (hhelperReservoir q)
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    simp [paths]
  · intro a b hab
    let qa := indexEquiv a
    let qb := indexEquiv b
    have hprivate : qa.1 ≠ qb.1 := by
      intro h
      apply hab
      apply indexEquiv.injective
      exact Subtype.ext h
    exact outerPrivatePaths_edgeDisjoint_of_distinct y p
      qa.1 (helper qa) qb.1 (helper qb) m qa.2.1 qb.2.1
      (hhelperPrivate qa) (hhelperReservoir qa) qa.2.2
      (hhelperPrivate qb) (hhelperReservoir qb) qb.2.2 hprivate
  · intro a x hx
    let q := indexEquiv a
    apply outerPrivatePath_vertices_on_two_spheres y q.1 (helper q) p m
      q.2.1 (hhelperPrivate q) q.2.2 (hhelperReservoir q) hy hpReservoir x
    simpa [paths, q] using hx
  · intro a
    constructor
    · simpa [paths, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
  · intro a b hab x hx
    let qa := indexEquiv a
    let qb := indexEquiv b
    have hprivate : qa.1 ≠ qb.1 := by
      intro h
      apply hab
      apply indexEquiv.injective
      exact Subtype.ext h
    apply outerPrivatePath_endpoint_far_of_distinct y p
      qa.1 (helper qa) qb.1 (helper qb) m qa.2.1 qb.2.1
      (hhelperPrivate qa) (hhelperReservoir qa) qa.2.2
      (hhelperPrivate qb) (hhelperReservoir qb) qb.2.2 hprivate
      (δ ^ 3 * (n + 1 : ℝ))
      (separation_radius_le_pathScale hd hδpos hδ n hscale) x
    simpa [paths, qb] using hx
  · intro a x hx r
    let q := indexEquiv a
    simpa [paths, q, m] using
      outerPrivatePath_coordinate_bounds y q.1 (helper q) p m q.2.1
        (hhelperPrivate q) q.2.2 (hhelperReservoir q) x
        (by simpa [paths, q] using hx) r

end

end DisjointPaths
