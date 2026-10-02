import Disjoint_paths.Lemmas.PathJoin
import Disjoint_paths.Lemmas.Fan
import Disjoint_paths.Lemmas.FanCount
import Disjoint_paths.Lemmas.Scale

/-!
# Inner fan with a common continuation

Each ordinary inner-fan path is followed by an alternating segment in one
fixed outward coordinate.  The original private coordinate remains available
for comparisons inside the family, while the fixed coordinate separates this
family from paths constructed in the opposite half-space.
-/

namespace DisjointPaths

noncomputable section

private lemma innerFanContinuation_compatible {d : ℕ}
    (z : LatticePoint d) (p r : Fin d) (hzr : z r ≠ 0)
    (q : InnerFanIndex z p) :
    q.1.1 ≠ r ∨
      (q.1.1 = r ∧ boolSign q.1.2 = coordinateSign (z r)) := by
  by_cases hqr : q.1.1 = r
  · right
    subst r
    refine ⟨rfl, ?_⟩
    exact boolSign_eq_coordinateSign_of_outward z q.1.1 q.1.2
      hzr q.2.1
  · exact Or.inl hqr

def extendedInnerFanPath {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (q : InnerFanIndex z p) : LatticePath d :=
  LatticePath.continueAlternatingPath z q.1.1 (boolSign q.1.2)
    r (coordinateSign (z r)) p sp q.2.2 hrp
    (natAbs_boolSign q.1.2) (natAbs_coordinateSign (z r)) hsp m m
    (innerFanContinuation_compatible z p r hzr q)

@[simp] lemma extendedInnerFanPath_start {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (q : InnerFanIndex z p) :
    (extendedInnerFanPath z p sp hsp r hrp hzr m q).start = z := by
  simp [extendedInnerFanPath]

@[simp] lemma extendedInnerFanPath_edgeLength {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (q : InnerFanIndex z p) :
    (extendedInnerFanPath z p sp hsp r hrp hzr m q).edgeLength = 4 * m := by
  simp [extendedInnerFanPath]
  omega

lemma extendedInnerFanPath_signed_coordinate_lower {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (q : InnerFanIndex z p)
    (x : LatticePoint d)
    (hx : x ∈ (extendedInnerFanPath z p sp hsp r hrp hzr m q).vertices) :
    coordinateSign (z r) * z r ≤ coordinateSign (z r) * x r := by
  exact LatticePath.continueAlternatingPath_signed_continuation_coordinate_lower
    z q.1.1 (boolSign q.1.2) r (coordinateSign (z r)) p sp
    q.2.2 hrp (natAbs_boolSign q.1.2) (natAbs_coordinateSign (z r))
    hsp m m (innerFanContinuation_compatible z p r hzr q) x hx

lemma extendedInnerFanPath_finish_signed_coordinate {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (q : InnerFanIndex z p) :
    coordinateSign (z r) * z r + m ≤ coordinateSign (z r) *
      (extendedInnerFanPath z p sp hsp r hrp hzr m q).finish r := by
  exact LatticePath.continueAlternatingPath_finish_signed_continuation_coordinate
    z q.1.1 (boolSign q.1.2) r (coordinateSign (z r)) p sp
    q.2.2 hrp (natAbs_boolSign q.1.2) (natAbs_coordinateSign (z r))
    hsp m m (innerFanContinuation_compatible z p r hzr q)

lemma extendedInnerFanPath_coordinate_bounds {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (q : InnerFanIndex z p)
    (x : LatticePoint d)
    (hx : x ∈ (extendedInnerFanPath z p sp hsp r hrp hzr m q).vertices)
    (k : Fin d) : z k - 2 * m ≤ x k ∧ x k ≤ z k + 2 * m := by
  simpa [extendedInnerFanPath, two_mul] using
    LatticePath.continueAlternatingPath_coordinate_bounds
      z q.1.1 (boolSign q.1.2) r (coordinateSign (z r)) p sp
      q.2.2 hrp (natAbs_boolSign q.1.2) (natAbs_coordinateSign (z r))
      hsp m m (innerFanContinuation_compatible z p r hzr q) x hx k

lemma extendedInnerFanPath_vertices_on_two_spheres {d n : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (q : InnerFanIndex z p)
    (hz : z ∈ sphere d n) (hreservoir : (2 * m : ℕ) ≤ sp * z p) :
    ∀ x ∈ (extendedInnerFanPath z p sp hsp r hrp hzr m q).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  have hfirstReservoir : (m : ℤ) ≤ sp * z p := by
    exact_mod_cast (show m ≤ (sp * z p : ℤ) by omega)
  have hfinishReservoir : sp *
      (alternatingPath z q.1.1 (boolSign q.1.2) p sp q.2.2
        (natAbs_boolSign q.1.2) hsp m).finish p = sp * z p - m := by
    rw [LatticePath.finish_alternatingPath]
    have hsq := sq_eq_one_of_natAbs_eq_one sp hsp
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_of_ne (Ne.symm q.2.2),
      signedBasis_same, add_zero]
    nlinarith
  have hsecondReservoir : (m : ℤ) ≤ sp *
      (alternatingPath z q.1.1 (boolSign q.1.2) p sp q.2.2
        (natAbs_boolSign q.1.2) hsp m).finish p := by
    rw [hfinishReservoir]
    have hcast : (2 : ℤ) * m ≤ sp * z p := by
      exact_mod_cast hreservoir
    omega
  have houtSecond : 0 ≤ coordinateSign (z r) *
      (alternatingPath z q.1.1 (boolSign q.1.2) p sp q.2.2
        (natAbs_boolSign q.1.2) hsp m).finish r := by
    have hstart : 0 ≤ coordinateSign (z r) * z r := by
      rw [coordinateSign_mul_self]
      positivity
    rcases innerFanContinuation_compatible z p r hzr q with hir | ⟨hir, hs⟩
    · have hcoord := LatticePath.alternatingPath_other_coordinate
        z q.1.1 (boolSign q.1.2) p sp q.2.2
        (natAbs_boolSign q.1.2) hsp m
        (alternatingPath z q.1.1 (boolSign q.1.2) p sp q.2.2
          (natAbs_boolSign q.1.2) hsp m).finish
        (LatticePath.finish_mem_vertices _) r hir.symm hrp
      rwa [hcoord]
    · subst r
      have hprivate := LatticePath.alternatingPath_private_coordinate_ge_start
        z q.1.1 (boolSign q.1.2) p sp q.2.2
        (natAbs_boolSign q.1.2) hsp m _ (LatticePath.finish_mem_vertices _)
      have hstart' : 0 ≤ boolSign q.1.2 * z q.1.1 := by
        simpa [hs] using hstart
      rw [← hs]
      exact hstart'.trans hprivate
  apply LatticePath.continueAlternatingPath_vertices_on_two_spheres
    z q.1.1 (boolSign q.1.2) r (coordinateSign (z r)) p sp
    q.2.2 hrp (natAbs_boolSign q.1.2) (natAbs_coordinateSign (z r))
    hsp m m (innerFanContinuation_compatible z p r hzr q) hz q.2.1
    hfirstReservoir
  · exact LatticePath.finish_alternatingPath_mem_inner_sphere_of_signs
      z q.1.1 (boolSign q.1.2) p sp q.2.2
      (natAbs_boolSign q.1.2) hsp m hz q.2.1 hfirstReservoir
  · exact houtSecond
  · exact hsecondReservoir

private lemma innerFanIndex_direction_ne {d : ℕ} {z : LatticePoint d}
    {p : Fin d} {q s : InnerFanIndex z p} (hqs : q ≠ s) :
    q.1.1 ≠ s.1.1 ∨ boolSign q.1.2 ≠ boolSign s.1.2 := by
  by_contra h
  have h := not_or.mp h
  apply hqs
  apply Subtype.ext
  apply Prod.ext (not_ne_iff.mp h.1)
  exact boolSign_injective (not_ne_iff.mp h.2)

private lemma extendedInnerFanPath_private_upper_of_ne_continuation {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) {q s : InnerFanIndex z p}
    (hqs : q ≠ s) (hqr : q.1.1 ≠ r) :
    ∀ x ∈ (extendedInnerFanPath z p sp hsp r hrp hzr m s).vertices,
      boolSign q.1.2 * x q.1.1 ≤ boolSign q.1.2 * z q.1.1 := by
  intro x hx
  rcases LatticePath.mem_vertices_continueAlternatingPath
      z s.1.1 (boolSign s.1.2) r (coordinateSign (z r)) p sp
      s.2.2 hrp (natAbs_boolSign s.1.2) (natAbs_coordinateSign (z r))
      hsp m m (innerFanContinuation_compatible z p r hzr s) x
      (by simpa [extendedInnerFanPath] using hx) with hx | hx
  · exact alternatingPath_private_signed_upper_of_distinct z p sp
      q.1.1 s.1.1 (boolSign q.1.2) (boolSign s.1.2)
      q.2.2 s.2.2 (natAbs_boolSign q.1.2) (natAbs_boolSign s.1.2)
      hsp (innerFanIndex_direction_ne hqs) m x hx
  · have hcoord := LatticePath.alternatingPath_other_coordinate
      (alternatingPath z s.1.1 (boolSign s.1.2) p sp s.2.2
        (natAbs_boolSign s.1.2) hsp m).finish
      r (coordinateSign (z r)) p sp hrp (natAbs_coordinateSign (z r))
      hsp m x hx q.1.1 hqr q.2.2
    rw [hcoord]
    exact alternatingPath_private_signed_upper_of_distinct z p sp
      q.1.1 s.1.1 (boolSign q.1.2) (boolSign s.1.2)
      q.2.2 s.2.2 (natAbs_boolSign q.1.2) (natAbs_boolSign s.1.2)
      hsp (innerFanIndex_direction_ne hqs) m _ (LatticePath.finish_mem_vertices _)

private lemma extendedInnerFanPath_private_upper_of_eq_continuation {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) {q s : InnerFanIndex z p}
    (hqs : q ≠ s) (hqr : q.1.1 = r) :
    ∀ x ∈ (extendedInnerFanPath z p sp hsp r hrp hzr m s).vertices,
      boolSign q.1.2 * x q.1.1 ≤ boolSign q.1.2 * z q.1.1 + m := by
  have hsign : boolSign q.1.2 = coordinateSign (z r) := by
    simpa [hqr] using boolSign_eq_coordinateSign_of_outward
      z q.1.1 q.1.2 (hqr.symm ▸ hzr) q.2.1
  intro x hx
  rcases LatticePath.mem_vertices_continueAlternatingPath
      z s.1.1 (boolSign s.1.2) r (coordinateSign (z r)) p sp
      s.2.2 hrp (natAbs_boolSign s.1.2) (natAbs_coordinateSign (z r))
      hsp m m (innerFanContinuation_compatible z p r hzr s) x
      (by simpa [extendedInnerFanPath] using hx) with hx | hx
  · have h := alternatingPath_private_signed_upper_of_distinct z p sp
      q.1.1 s.1.1 (boolSign q.1.2) (boolSign s.1.2)
      q.2.2 s.2.2 (natAbs_boolSign q.1.2) (natAbs_boolSign s.1.2)
      hsp (innerFanIndex_direction_ne hqs) m x hx
    omega
  · have hfirst := alternatingPath_private_signed_upper_of_distinct z p sp
      q.1.1 s.1.1 (boolSign q.1.2) (boolSign s.1.2)
      q.2.2 s.2.2 (natAbs_boolSign q.1.2) (natAbs_boolSign s.1.2)
      hsp (innerFanIndex_direction_ne hqs) m _ (LatticePath.finish_mem_vertices _)
    have hle := LatticePath.alternatingPath_private_coordinate_le_finish
      (alternatingPath z s.1.1 (boolSign s.1.2) p sp s.2.2
        (natAbs_boolSign s.1.2) hsp m).finish
      r (coordinateSign (z r)) p sp hrp (natAbs_coordinateSign (z r))
      hsp m x hx
    rw [LatticePath.finish_alternatingPath] at hle
    have hsq := sq_eq_one_of_natAbs_eq_one (coordinateSign (z r))
      (natAbs_coordinateSign (z r))
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
      signedBasis_of_ne hrp] at hle
    subst r
    rw [hsign] at hfirst ⊢
    nlinarith

lemma extendedInnerFanPath_endpoint_far {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (rsep : ℝ)
    (hrsep : rsep ≤ (m : ℝ)) {q s : InnerFanIndex z p} (hqs : q ≠ s) :
    ∀ x ∈ (extendedInnerFanPath z p sp hsp r hrp hzr m s).vertices,
      rsep ≤ (l1Dist (extendedInnerFanPath z p sp hsp r hrp hzr m q).finish x : ℝ) := by
  by_cases hqr : q.1.1 = r
  · subst r
    apply endpoint_far_from_vertices_of_signed_coordinate_gap
      (extendedInnerFanPath z p sp hsp q.1.1 hrp hzr m q)
      (extendedInnerFanPath z p sp hsp q.1.1 hrp hzr m s)
      q.1.1 (boolSign q.1.2) (natAbs_boolSign q.1.2)
      rsep (boolSign q.1.2 * z q.1.1 + m) m hrsep (by positivity)
    · have hsign := boolSign_eq_coordinateSign_of_outward
        z q.1.1 q.1.2 hzr q.2.1
      simp only [extendedInnerFanPath, LatticePath.finish_continueAlternatingPath]
      rw [LatticePath.finish_alternatingPath, LatticePath.finish_alternatingPath]
      have hsqQ := sq_eq_one_of_natAbs_eq_one (boolSign q.1.2)
        (natAbs_boolSign q.1.2)
      have hsqR := sq_eq_one_of_natAbs_eq_one (coordinateSign (z q.1.1))
        (natAbs_coordinateSign (z q.1.1))
      simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
        signedBasis_of_ne hrp]
      rw [hsign]
      nlinarith
    · exact extendedInnerFanPath_private_upper_of_eq_continuation
        z p sp hsp q.1.1 hrp hzr m hqs rfl
  · apply endpoint_far_from_vertices_of_signed_coordinate_gap
      (extendedInnerFanPath z p sp hsp r hrp hzr m q)
      (extendedInnerFanPath z p sp hsp r hrp hzr m s)
      q.1.1 (boolSign q.1.2) (natAbs_boolSign q.1.2)
      rsep (boolSign q.1.2 * z q.1.1) m hrsep (by positivity)
    · simp only [extendedInnerFanPath, LatticePath.finish_continueAlternatingPath]
      have hcoord := LatticePath.alternatingPath_other_coordinate
        (alternatingPath z q.1.1 (boolSign q.1.2) p sp q.2.2
          (natAbs_boolSign q.1.2) hsp m).finish
        r (coordinateSign (z r)) p sp hrp (natAbs_coordinateSign (z r))
        hsp m
        (alternatingPath
          (alternatingPath z q.1.1 (boolSign q.1.2) p sp q.2.2
            (natAbs_boolSign q.1.2) hsp m).finish
          r (coordinateSign (z r)) p sp hrp (natAbs_coordinateSign (z r))
          hsp m).finish
        (LatticePath.finish_mem_vertices _) q.1.1 hqr q.2.2
      rw [hcoord, alternatingPath_finish_private_signed]
    · exact extendedInnerFanPath_private_upper_of_ne_continuation
        z p sp hsp r hrp hzr m hqs hqr

private lemma extendedInnerFanPath_eq_start_of_private_upper {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (hm : 0 < m) (q : InnerFanIndex z p)
    (hqr : q.1.1 ≠ r) (x : LatticePoint d)
    (hx : x ∈ (extendedInnerFanPath z p sp hsp r hrp hzr m q).vertices)
    (hupper : boolSign q.1.2 * x q.1.1 ≤
      boolSign q.1.2 * z q.1.1) : x = z := by
  rcases LatticePath.mem_vertices_continueAlternatingPath
      z q.1.1 (boolSign q.1.2) r (coordinateSign (z r)) p sp
      q.2.2 hrp (natAbs_boolSign q.1.2) (natAbs_coordinateSign (z r))
      hsp m m (innerFanContinuation_compatible z p r hzr q) x
      (by simpa [extendedInnerFanPath] using hx) with hx | hx
  · have hlower := LatticePath.alternatingPath_private_coordinate_ge_start
      z q.1.1 (boolSign q.1.2) p sp q.2.2
      (natAbs_boolSign q.1.2) hsp m x hx
    apply LatticePath.alternatingPath_eq_start_of_private_coordinate_eq
      z q.1.1 (boolSign q.1.2) p sp q.2.2
      (natAbs_boolSign q.1.2) hsp m x hx
    exact le_antisymm hupper hlower
  · have hcoord := LatticePath.alternatingPath_other_coordinate
      (alternatingPath z q.1.1 (boolSign q.1.2) p sp q.2.2
        (natAbs_boolSign q.1.2) hsp m).finish
      r (coordinateSign (z r)) p sp hrp (natAbs_coordinateSign (z r))
      hsp m x hx q.1.1 hqr q.2.2
    have hfinish := alternatingPath_finish_private_signed
      z q.1.1 (boolSign q.1.2) p sp q.2.2
      (natAbs_boolSign q.1.2) hsp m
    rw [hcoord, hfinish] at hupper
    omega

lemma extendedInnerFanPaths_edgeDisjoint_of_distinct {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (r : Fin d) (hrp : r ≠ p)
    (hzr : z r ≠ 0) (m : ℕ) (hm : 0 < m)
    {q s : InnerFanIndex z p} (hqs : q ≠ s) :
    Disjoint (extendedInnerFanPath z p sp hsp r hrp hzr m q).edgeSet
      (extendedInnerFanPath z p sp hsp r hrp hzr m s).edgeSet := by
  apply LatticePath.edgeDisjoint_of_common_vertices_subsingleton _ _ z
  intro x hxq hxs
  by_cases hqr : q.1.1 = r
  · have hsr : s.1.1 ≠ r := by
      intro hsr
      apply hqs
      apply Subtype.ext
      apply Prod.ext (hqr.trans hsr.symm)
      apply boolSign_injective
      have hqsign := boolSign_eq_coordinateSign_of_outward
        z q.1.1 q.1.2 (hqr.symm ▸ hzr) q.2.1
      have hssign := boolSign_eq_coordinateSign_of_outward
        z s.1.1 s.1.2 (hsr.symm ▸ hzr) s.2.1
      rw [hqsign, hqr, hssign, hsr]
    apply extendedInnerFanPath_eq_start_of_private_upper
      z p sp hsp r hrp hzr m hm s hsr x hxs
    exact extendedInnerFanPath_private_upper_of_ne_continuation
      z p sp hsp r hrp hzr m hqs.symm hsr x hxq
  · apply extendedInnerFanPath_eq_start_of_private_upper
      z p sp hsp r hrp hzr m hm q hqr x hxq
    exact extendedInnerFanPath_private_upper_of_ne_continuation
      z p sp hsp r hrp hzr m hqs hqr x hxs

theorem exists_extended_innerFan {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z : LatticePoint d) (hz : z ∈ sphere d n)
    (p : Fin d) (sp : ℤ) (hsp : Int.natAbs sp = 1)
    (hpReservoir : ((2 * pathScale δ n : ℕ) : ℤ) ≤ sp * z p)
    (r : Fin d) (hrp : r ≠ p) (hzr : z r ≠ 0) :
    ∃ paths : Fin (pathCountAtInner n z) → LatticePath d,
      (∀ i, (paths i).start = z) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i, ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) ∧
      (∀ i x, x ∈ (paths i).vertices →
        coordinateSign (z r) * z r ≤ coordinateSign (z r) * x r) ∧
      (∀ i, coordinateSign (z r) * z r + pathScale δ n ≤
        coordinateSign (z r) * (paths i).finish r) ∧
      (∀ i x, x ∈ (paths i).vertices → ∀ k,
        z k - 2 * pathScale δ n ≤ x k ∧
          x k ≤ z k + 2 * pathScale δ n) := by
  let m := pathScale δ n
  have hm : 0 < m := by
    have : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
    omega
  have hpNonzero : z p ≠ 0 := by
    intro hpzero
    rw [hpzero] at hpReservoir
    simp at hpReservoir
    omega
  have hnpos : 0 < n := by
    have hple : Int.natAbs (z p) ≤ l1Norm z := by
      exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le (Int.natAbs (z i)))
        (Finset.mem_univ p)
    have hpabs : 0 < Int.natAbs (z p) := Int.natAbs_pos.mpr hpNonzero
    rw [hz] at hple
    omega
  obtain ⟨fanIndex, hfanIndex⟩ :
      ∃ fanIndex : Fin (pathCountAtInner n z) → InnerFanIndex z p,
        Function.Injective fanIndex := by
    by_cases haxis : IsAxisPoint n z
    · have hsupport : supportCard z = 1 :=
        supportCard_eq_one_of_isAxisPoint hnpos haxis
      have hcardAll : Fintype.card (InnerFanIndex z p) = 2 * d - 2 := by
        rw [card_innerFanIndex z p hpNonzero, hsupport]
        omega
      have hcount : pathCountAtInner n z = 2 * d - 3 := by
        simp [pathCountAtInner, haxis]
      have hle : pathCountAtInner n z ≤ Fintype.card (InnerFanIndex z p) := by
        rw [hcardAll, hcount]
        omega
      let allEquiv := Fintype.equivFin (InnerFanIndex z p)
      let fanIndex : Fin (pathCountAtInner n z) → InnerFanIndex z p := fun i ↦
        allEquiv.symm ⟨i.val, lt_of_lt_of_le i.isLt hle⟩
      refine ⟨fanIndex, ?_⟩
      intro i j hij
      have hfin := allEquiv.symm.injective hij
      exact Fin.ext (congrArg
        (fun k : Fin (Fintype.card (InnerFanIndex z p)) ↦ k.val) hfin)
    · have hcard : Fintype.card (InnerFanIndex z p) = pathCountAtInner n z := by
        rw [card_innerFanIndex z p hpNonzero]
        simp [pathCountAtInner, haxis]
      let indexEquiv : Fin (pathCountAtInner n z) ≃ InnerFanIndex z p :=
        (Fintype.equivFinOfCardEq hcard).symm
      exact ⟨indexEquiv, indexEquiv.injective⟩
  let paths : Fin (pathCountAtInner n z) → LatticePath d := fun i ↦
    extendedInnerFanPath z p sp hsp r hrp hzr m (fanIndex i)
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [paths]
  · intro i j hij
    exact extendedInnerFanPaths_edgeDisjoint_of_distinct
      z p sp hsp r hrp hzr m hm (hfanIndex.ne hij)
  · intro i x hx
    exact extendedInnerFanPath_vertices_on_two_spheres
      z p sp hsp r hrp hzr m (fanIndex i) hz hpReservoir x
      (by simpa [paths, m] using hx)
  · intro i
    constructor
    · have hlower := pathScale_length_lower (δ := δ) n
      simpa [paths, m] using hlower.trans
        (show ((2 * m : ℕ) : ℤ) ≤ ((4 * m : ℕ) : ℤ) by exact_mod_cast (by omega))
    · simpa [paths, m] using four_pathScale_length_upper (show 2 ≤ d by omega) δ n
  · intro i j hij x hx
    apply extendedInnerFanPath_endpoint_far z p sp hsp r hrp hzr m
      (δ ^ 3 * (n + 1 : ℝ))
      (separation_radius_le_pathScale hd hδpos hδ n hscale)
      (hfanIndex.ne hij) x
    simpa [paths, m] using hx
  · intro i x hx
    exact extendedInnerFanPath_signed_coordinate_lower
      z p sp hsp r hrp hzr m (fanIndex i) x (by simpa [paths, m] using hx)
  · intro i
    exact extendedInnerFanPath_finish_signed_coordinate
      z p sp hsp r hrp hzr m (fanIndex i)
  · intro i x hx k
    exact extendedInnerFanPath_coordinate_bounds
      z p sp hsp r hrp hzr m (fanIndex i) x (by simpa [paths, m] using hx) k

end

end DisjointPaths
