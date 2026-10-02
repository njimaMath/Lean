import Disjoint_paths.Lemmas.Alternating
import Disjoint_paths.Lemmas.Separation

/-!
# Pairwise properties of an alternating fan

All paths in a fan use the same reservoir coordinate and have distinct signed
private directions.  Their private coordinate separates their endpoints from
every vertex of every other path.
-/

namespace DisjointPaths

lemma alternatingPath_private_signed_upper_of_distinct {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (i j : Fin d) (si sj : ℤ)
    (hip : i ≠ p) (hjp : j ≠ p)
    (hsi : Int.natAbs si = 1) (hsj : Int.natAbs sj = 1)
    (hsp : Int.natAbs sp = 1) (hdirection : i ≠ j ∨ si ≠ sj)
    (m : ℕ) :
    ∀ x ∈ (alternatingPath z j sj p sp hjp hsj hsp m).vertices,
      si * x i ≤ si * z i := by
  intro x hx
  rcases (LatticePath.mem_vertices_alternatingPath_iff
    z j sj p sp hjp hsj hsp m x).mp hx with ⟨k, -, rfl⟩
  rcases Int.natAbs_eq_iff.mp hsi with rfl | rfl <;>
    rcases Int.natAbs_eq_iff.mp hsj with rfl | rfl
  · rcases hdirection with hij | hsign
    · simp [alternatingVertex, signedBasis, hij, hip]
    · simp at hsign
  · by_cases hij : i = j
    · subst j
      simp [alternatingVertex, signedBasis, hip]
      positivity
    · simp [alternatingVertex, signedBasis, hij, hip]
  · by_cases hij : i = j
    · subst j
      simp [alternatingVertex, signedBasis, hip]
      positivity
    · simp [alternatingVertex, signedBasis, hij, hip]
  · rcases hdirection with hij | hsign
    · simp [alternatingVertex, signedBasis, hij, hip]
    · simp at hsign

lemma alternatingPath_finish_private_signed {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) :
    si * (alternatingPath z i si p sp hip hsi hsp m).finish i =
      si * z i + m := by
  rw [LatticePath.finish_alternatingPath]
  have hsq := sq_eq_one_of_natAbs_eq_one si hsi
  simp [signedBasis, hip]
  nlinarith

lemma alternatingPath_endpoint_far_of_distinct {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (i j : Fin d) (si sj : ℤ)
    (hip : i ≠ p) (hjp : j ≠ p)
    (hsi : Int.natAbs si = 1) (hsj : Int.natAbs sj = 1)
    (hsp : Int.natAbs sp = 1) (hdirection : i ≠ j ∨ si ≠ sj)
    (m : ℕ) (r : ℝ) (hr : r ≤ (m : ℝ)) :
    ∀ x ∈ (alternatingPath z j sj p sp hjp hsj hsp m).vertices,
      r ≤ (l1Dist
        (alternatingPath z i si p sp hip hsi hsp m).finish x : ℝ) := by
  have hother := alternatingPath_private_signed_upper_of_distinct
    z p sp i j si sj hip hjp hsi hsj hsp hdirection m
  rcases Int.natAbs_eq_iff.mp hsi with rfl | rfl
  · apply endpoint_far_from_vertices_of_coordinate_gap
      (alternatingPath z i 1 p sp hip hsi hsp m)
      (alternatingPath z j sj p sp hjp hsj hsp m)
      i r ((alternatingPath z i 1 p sp hip hsi hsp m).finish i)
        (z i) m hr (by positivity)
    · exact le_rfl
    · intro x hx
      simpa using hother x hx
    · rw [LatticePath.finish_alternatingPath]
      simp [signedBasis, hip]
  · apply endpoint_far_from_vertices_of_reverse_coordinate_gap
      (alternatingPath z i (-1) p sp hip hsi hsp m)
      (alternatingPath z j sj p sp hjp hsj hsp m)
      i r ((alternatingPath z i (-1) p sp hip hsi hsp m).finish i)
        (z i) m hr (by positivity)
    · exact le_rfl
    · intro x hx
      have := hother x hx
      norm_num at this ⊢
      omega
    · rw [LatticePath.finish_alternatingPath]
      simp [signedBasis, hip]

lemma alternatingPaths_edgeDisjoint_of_distinct {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (i j : Fin d) (si sj : ℤ)
    (hip : i ≠ p) (hjp : j ≠ p)
    (hsi : Int.natAbs si = 1) (hsj : Int.natAbs sj = 1)
    (hsp : Int.natAbs sp = 1) (hdirection : i ≠ j ∨ si ≠ sj)
    (m : ℕ) :
    Disjoint
      (alternatingPath z i si p sp hip hsi hsp m).edgeSet
      (alternatingPath z j sj p sp hjp hsj hsp m).edgeSet := by
  apply LatticePath.edgeDisjoint_of_common_vertices_subsingleton _ _ z
  intro x hxi hxj
  rcases (LatticePath.mem_vertices_alternatingPath_iff
    z i si p sp hip hsi hsp m x).mp hxi with ⟨k, -, hk⟩
  rcases (LatticePath.mem_vertices_alternatingPath_iff
    z j sj p sp hjp hsj hsp m x).mp hxj with ⟨l, -, hl⟩
  have heq : alternatingVertex z i si p sp k =
      alternatingVertex z j sj p sp l := hk.trans hl.symm
  rcases Int.natAbs_eq_iff.mp hsi with rfl | rfl <;>
    rcases Int.natAbs_eq_iff.mp hsj with rfl | rfl
  · rcases hdirection with hij | hsign
    · have hi := congrFun heq i
      simp [alternatingVertex, signedBasis, hij, hip] at hi
      have hk0 : k = 0 := by omega
      subst k
      simpa using hk.symm
    · simp at hsign
  · by_cases hij : i = j
    · subst j
      have hi := congrFun heq i
      simp [alternatingVertex, signedBasis, hip] at hi
      have hk0 : k = 0 := by omega
      subst k
      simpa using hk.symm
    · have hi := congrFun heq i
      simp [alternatingVertex, signedBasis, hij, hip] at hi
      have hk0 : k = 0 := by omega
      subst k
      simpa using hk.symm
  · by_cases hij : i = j
    · subst j
      have hi := congrFun heq i
      simp [alternatingVertex, signedBasis, hip] at hi
      have hk0 : k = 0 := by omega
      subst k
      simpa using hk.symm
    · have hi := congrFun heq i
      simp [alternatingVertex, signedBasis, hij, hip] at hi
      have hk0 : k = 0 := by omega
      subst k
      simpa using hk.symm
  · rcases hdirection with hij | hsign
    · have hi := congrFun heq i
      simp [alternatingVertex, signedBasis, hij, hip] at hi
      have hk0 : k = 0 := by omega
      subst k
      simpa using hk.symm
    · simp at hsign

def boolSign (b : Bool) : ℤ := if b then 1 else -1

@[simp] lemma natAbs_boolSign (b : Bool) : Int.natAbs (boolSign b) = 1 := by
  cases b <;> simp [boolSign]

lemma boolSign_injective : Function.Injective boolSign := by
  intro a b h
  cases a <;> cases b <;> simp [boolSign] at h ⊢

def IsOutwardDirection {d : ℕ} (z : LatticePoint d)
    (q : Fin d × Bool) : Prop :=
  0 ≤ boolSign q.2 * z q.1

lemma boolSign_eq_coordinateSign_of_outward {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (b : Bool)
    (hzi : z i ≠ 0) (hout : 0 ≤ boolSign b * z i) :
    boolSign b = coordinateSign (z i) := by
  cases b <;> simp [boolSign, coordinateSign] at hout ⊢ <;> omega

/-- Signed outward directions other than the reservoir coordinate. -/
def InnerFanIndex {d : ℕ} (z : LatticePoint d) (p : Fin d) :=
  {q : Fin d × Bool // IsOutwardDirection z q ∧ q.1 ≠ p}

def innerFanPath {d : ℕ} (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ) (q : InnerFanIndex z p) :
    LatticePath d :=
  alternatingPath z q.1.1 (boolSign q.1.2) p sp q.2.2
    (natAbs_boolSign q.1.2) hsp m

@[simp] lemma innerFanPath_start {d : ℕ} (z : LatticePoint d)
    (p : Fin d) (sp : ℤ) (hsp : Int.natAbs sp = 1)
    (m : ℕ) (q : InnerFanIndex z p) :
    (innerFanPath z p sp hsp m q).start = z := by
  simp [innerFanPath]

@[simp] lemma innerFanPath_edgeLength {d : ℕ} (z : LatticePoint d)
    (p : Fin d) (sp : ℤ) (hsp : Int.natAbs sp = 1)
    (m : ℕ) (q : InnerFanIndex z p) :
    (innerFanPath z p sp hsp m q).edgeLength = 2 * m := by
  simp [innerFanPath]

lemma innerFanPath_vertices_on_two_spheres {d n : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (hz : z ∈ sphere d n) (hreservoir : (m : ℤ) ≤ sp * z p)
    (q : InnerFanIndex z p) :
    ∀ x ∈ (innerFanPath z p sp hsp m q).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  apply LatticePath.alternatingPath_vertices_on_two_spheres_of_signs
  · exact hz
  · exact q.2.1
  · exact hreservoir

lemma innerFanPath_coordinate_lower_bound {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ) (q : InnerFanIndex z p)
    (x : LatticePoint d) (hx : x ∈ (innerFanPath z p sp hsp m q).vertices)
    (r : Fin d) :
    z r - m ≤ x r := by
  exact LatticePath.alternatingPath_coordinate_lower_bound
    z q.1.1 (boolSign q.1.2) p sp q.2.2
    (natAbs_boolSign q.1.2) hsp m x hx r

lemma innerFanPath_coordinate_upper_bound {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ) (q : InnerFanIndex z p)
    (x : LatticePoint d) (hx : x ∈ (innerFanPath z p sp hsp m q).vertices)
    (r : Fin d) :
    x r ≤ z r + m := by
  exact LatticePath.alternatingPath_coordinate_upper_bound
    z q.1.1 (boolSign q.1.2) p sp q.2.2
    (natAbs_boolSign q.1.2) hsp m x hx r

private lemma innerFanIndex_direction_ne {d : ℕ} {z : LatticePoint d}
    {p : Fin d} {q r : InnerFanIndex z p} (hqr : q ≠ r) :
    q.1.1 ≠ r.1.1 ∨ boolSign q.1.2 ≠ boolSign r.1.2 := by
  by_contra h
  have h := not_or.mp h
  apply hqr
  apply Subtype.ext
  apply Prod.ext (not_ne_iff.mp h.1)
  exact boolSign_injective (not_ne_iff.mp h.2)

lemma innerFanPath_edgeDisjoint {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    {q r : InnerFanIndex z p} (hqr : q ≠ r) :
    Disjoint (innerFanPath z p sp hsp m q).edgeSet
      (innerFanPath z p sp hsp m r).edgeSet := by
  exact alternatingPaths_edgeDisjoint_of_distinct z p sp
    q.1.1 r.1.1 (boolSign q.1.2) (boolSign r.1.2)
    q.2.2 r.2.2 (natAbs_boolSign q.1.2) (natAbs_boolSign r.1.2)
    hsp (innerFanIndex_direction_ne hqr) m

lemma innerFanPath_endpoint_far {d : ℕ}
    (z : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ) (rsep : ℝ)
    (hrsep : rsep ≤ (m : ℝ))
    {q r : InnerFanIndex z p} (hqr : q ≠ r) :
    ∀ x ∈ (innerFanPath z p sp hsp m r).vertices,
      rsep ≤ (l1Dist (innerFanPath z p sp hsp m q).finish x : ℝ) := by
  exact alternatingPath_endpoint_far_of_distinct z p sp
    q.1.1 r.1.1 (boolSign q.1.2) (boolSign r.1.2)
    q.2.2 r.2.2 (natAbs_boolSign q.1.2) (natAbs_boolSign r.1.2)
    hsp (innerFanIndex_direction_ne hqr) m rsep hrsep

end DisjointPaths
