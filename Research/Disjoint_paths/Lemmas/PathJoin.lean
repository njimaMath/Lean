import Disjoint_paths.Lemmas.Alternating

/-!
# Joining self-avoiding lattice paths

The second path's initial vertex is omitted, so the common junction occurs
only once in the resulting vertex list.
-/

namespace DisjointPaths

namespace LatticePath

def join {d : ℕ} (p q : LatticePath d)
    (hjoin : p.finish = q.start)
    (hcommon : ∀ x, x ∈ p.vertices → x ∈ q.vertices → x = p.finish) :
    LatticePath d where
  vertices := p.vertices ++ q.vertices.tail
  nonempty := by
    intro hnil
    have hmem : p.start ∈ p.vertices ++ q.vertices.tail :=
      List.mem_append_left _ (start_mem_vertices p)
    rw [hnil] at hmem
    simp at hmem
  adjacent := by
    rw [List.isChain_append]
    refine ⟨p.adjacent, q.adjacent.tail, ?_⟩
    intro x hx y hy
    have hxfinish : x = p.finish := by
      have hlast : p.vertices.getLast? = some p.finish := by
        simpa [finish] using List.getLast?_eq_getLast_of_ne_nil p.nonempty
      rw [hlast] at hx
      exact (Option.some.inj hx).symm
    subst x
    rw [hjoin]
    cases hq : q.vertices with
    | nil => exact False.elim (q.nonempty hq)
    | cons a tail =>
        cases tail with
        | nil => simp [hq] at hy
        | cons b rest =>
            have hab := (List.isChain_cons_cons.mp (by simpa [hq] using q.adjacent)).1
            have hyb : y = b := by simpa [hq] using hy.symm
            simpa [start, hq, hyb] using hab
  nodup := by
    apply p.nodup.append q.nodup.tail
    rw [List.disjoint_left]
    intro x hxp hxqt
    have hxq : x ∈ q.vertices := by
      exact List.mem_of_mem_tail hxqt
    have hxfinish := hcommon x hxp hxq
    have hfinishTail : p.finish ∈ q.vertices.tail := by
      simpa [hxfinish] using hxqt
    have hstartTail : q.start ∈ q.vertices.tail := by
      rw [← hjoin]
      exact hfinishTail
    cases hq : q.vertices with
    | nil => exact False.elim (q.nonempty hq)
    | cons a tail =>
        have hstart : q.start = a := by simp [start, hq]
        have haTail : a ∈ tail := by
          simpa [hq, hstart] using hstartTail
        exact (List.nodup_cons.mp (by simpa [hq] using q.nodup)).1 haTail

@[simp] lemma vertices_join {d : ℕ} (p q : LatticePath d)
    (hjoin : p.finish = q.start)
    (hcommon : ∀ x, x ∈ p.vertices → x ∈ q.vertices → x = p.finish) :
    (join p q hjoin hcommon).vertices = p.vertices ++ q.vertices.tail := rfl

@[simp] lemma start_join {d : ℕ} (p q : LatticePath d)
    (hjoin : p.finish = q.start)
    (hcommon : ∀ x, x ∈ p.vertices → x ∈ q.vertices → x = p.finish) :
    (join p q hjoin hcommon).start = p.start := by
  cases hp : p.vertices with
  | nil => exact False.elim (p.nonempty hp)
  | cons a tail => simp [join, start, hp]

@[simp] lemma finish_join {d : ℕ} (p q : LatticePath d)
    (hjoin : p.finish = q.start)
    (hcommon : ∀ x, x ∈ p.vertices → x ∈ q.vertices → x = p.finish) :
    (join p q hjoin hcommon).finish = q.finish := by
  cases hq : q.vertices with
  | nil => exact False.elim (q.nonempty hq)
  | cons a tail =>
      cases tail with
      | nil =>
          simp [join, finish, hq]
          simpa [start, finish, hq] using hjoin
      | cons b rest =>
          simp [join, finish, hq]

@[simp] lemma edgeLength_join {d : ℕ} (p q : LatticePath d)
    (hjoin : p.finish = q.start)
    (hcommon : ∀ x, x ∈ p.vertices → x ∈ q.vertices → x = p.finish) :
    (join p q hjoin hcommon).edgeLength = p.edgeLength + q.edgeLength := by
  cases hp : p.vertices with
  | nil => exact False.elim (p.nonempty hp)
  | cons a ptail =>
      cases hq : q.vertices with
      | nil => exact False.elim (q.nonempty hq)
      | cons b qtail =>
          simp [join, edgeLength, hp, hq]

lemma alternatingPath_continuation_common_vertices {d : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr)) :
    let first := alternatingPath z i si p sp hip hsi hsp a
    let second := alternatingPath first.finish r sr p sp hrp hsr hsp b
    ∀ x, x ∈ first.vertices → x ∈ second.vertices → x = first.finish := by
  dsimp
  intro x hxFirst hxSecond
  let first := alternatingPath z i si p sp hip hsi hsp a
  have hprivate : si * x i = si * first.finish i := by
    rcases hcompat with hir | ⟨hir, hs⟩
    · have hcoord := alternatingPath_other_coordinate
        first.finish r sr p sp hrp hsr hsp b x hxSecond i hir hip
      rw [hcoord]
    · subst r
      subst sr
      have hle := alternatingPath_private_coordinate_le_finish
        z i si p sp hip hsi hsp a x hxFirst
      have hge := alternatingPath_private_coordinate_ge_start
        first.finish i si p sp hip hsi hsp b x hxSecond
      exact le_antisymm hle hge
  have hreservoir : sp * x p ≤ sp * first.finish p :=
    alternatingPath_reservoir_coordinate_le_start
      first.finish r sr p sp hrp hsr hsp b x hxSecond
  exact alternatingPath_eq_finish_of_private_eq_of_reservoir_le
    z i si p sp hip hsi hsp a x hxFirst hprivate hreservoir

def continueAlternatingPath {d : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr)) : LatticePath d :=
  let first := alternatingPath z i si p sp hip hsi hsp a
  let second := alternatingPath first.finish r sr p sp hrp hsr hsp b
  join first second (by
    exact (start_alternatingPath first.finish r sr p sp hrp hsr hsp b).symm)
    (alternatingPath_continuation_common_vertices z i si r sr p sp hip hrp
      hsi hsr hsp a b hcompat)

@[simp] lemma start_continueAlternatingPath {d : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr)) :
    (continueAlternatingPath z i si r sr p sp hip hrp hsi hsr hsp a b hcompat).start = z := by
  simp [continueAlternatingPath]

@[simp] lemma finish_continueAlternatingPath {d : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr)) :
    (continueAlternatingPath z i si r sr p sp hip hrp hsi hsr hsp a b hcompat).finish =
      (alternatingPath
        (alternatingPath z i si p sp hip hsi hsp a).finish
        r sr p sp hrp hsr hsp b).finish := by
  simp [continueAlternatingPath]

@[simp] lemma edgeLength_continueAlternatingPath {d : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr)) :
    (continueAlternatingPath z i si r sr p sp hip hrp hsi hsr hsp a b hcompat).edgeLength =
      2 * a + 2 * b := by
  simp [continueAlternatingPath]

lemma mem_vertices_continueAlternatingPath {d : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr))
    (x : LatticePoint d)
    (hx : x ∈ (continueAlternatingPath z i si r sr p sp hip hrp
      hsi hsr hsp a b hcompat).vertices) :
    x ∈ (alternatingPath z i si p sp hip hsi hsp a).vertices ∨
      x ∈ (alternatingPath
        (alternatingPath z i si p sp hip hsi hsp a).finish
        r sr p sp hrp hsr hsp b).vertices := by
  change x ∈ (alternatingPath z i si p sp hip hsi hsp a).vertices ++
    (alternatingPath (alternatingPath z i si p sp hip hsi hsp a).finish
      r sr p sp hrp hsr hsp b).vertices.tail at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (List.mem_of_mem_tail hx)

lemma continueAlternatingPath_vertices_on_two_spheres {d n : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr))
    (hz : z ∈ sphere d n) (houtFirst : 0 ≤ si * z i)
    (hreservoirFirst : (a : ℤ) ≤ sp * z p)
    (hfinishSphere :
      (alternatingPath z i si p sp hip hsi hsp a).finish ∈ sphere d n)
    (houtSecond : 0 ≤ sr *
      (alternatingPath z i si p sp hip hsi hsp a).finish r)
    (hreservoirSecond : (b : ℤ) ≤ sp *
      (alternatingPath z i si p sp hip hsi hsp a).finish p) :
    ∀ x ∈ (continueAlternatingPath z i si r sr p sp hip hrp
      hsi hsr hsp a b hcompat).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  intro x hx
  rcases mem_vertices_continueAlternatingPath z i si r sr p sp hip hrp
      hsi hsr hsp a b hcompat x hx with hx | hx
  · exact alternatingPath_vertices_on_two_spheres_of_signs
      z i si p sp hip hsi hsp a hz houtFirst hreservoirFirst x hx
  · exact alternatingPath_vertices_on_two_spheres_of_signs
      (alternatingPath z i si p sp hip hsi hsp a).finish
      r sr p sp hrp hsr hsp b hfinishSphere houtSecond hreservoirSecond x hx

lemma continueAlternatingPath_coordinate_bounds {d : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr))
    (x : LatticePoint d)
    (hx : x ∈ (continueAlternatingPath z i si r sr p sp hip hrp
      hsi hsr hsp a b hcompat).vertices) (q : Fin d) :
    z q - (a + b : ℕ) ≤ x q ∧ x q ≤ z q + (a + b : ℕ) := by
  rcases mem_vertices_continueAlternatingPath z i si r sr p sp hip hrp
      hsi hsr hsp a b hcompat x hx with hx | hx
  · constructor
    · have h := alternatingPath_coordinate_lower_bound
        z i si p sp hip hsi hsp a x hx q
      omega
    · have h := alternatingPath_coordinate_upper_bound
        z i si p sp hip hsi hsp a x hx q
      omega
  · have hfirstLower := alternatingPath_coordinate_lower_bound
      z i si p sp hip hsi hsp a
      (alternatingPath z i si p sp hip hsi hsp a).finish
      (LatticePath.finish_mem_vertices _) q
    have hfirstUpper := alternatingPath_coordinate_upper_bound
      z i si p sp hip hsi hsp a
      (alternatingPath z i si p sp hip hsi hsp a).finish
      (LatticePath.finish_mem_vertices _) q
    have hsecondLower := alternatingPath_coordinate_lower_bound
      (alternatingPath z i si p sp hip hsi hsp a).finish
      r sr p sp hrp hsr hsp b x hx q
    have hsecondUpper := alternatingPath_coordinate_upper_bound
      (alternatingPath z i si p sp hip hsi hsp a).finish
      r sr p sp hrp hsr hsp b x hx q
    constructor <;> omega

lemma continueAlternatingPath_signed_continuation_coordinate_lower {d : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr))
    (x : LatticePoint d)
    (hx : x ∈ (continueAlternatingPath z i si r sr p sp hip hrp
      hsi hsr hsp a b hcompat).vertices) :
    sr * z r ≤ sr * x r := by
  have hfirst : ∀ y ∈ (alternatingPath z i si p sp hip hsi hsp a).vertices,
      sr * z r ≤ sr * y r := by
    intro y hy
    rcases hcompat with hir | ⟨hir, hs⟩
    · have hcoord := alternatingPath_other_coordinate
        z i si p sp hip hsi hsp a y hy r hir.symm hrp
      rw [hcoord]
    · subst r
      subst sr
      exact alternatingPath_private_coordinate_ge_start
        z i si p sp hip hsi hsp a y hy
  rcases mem_vertices_continueAlternatingPath z i si r sr p sp hip hrp
      hsi hsr hsp a b hcompat x hx with hx | hx
  · exact hfirst x hx
  · exact (hfirst _ (LatticePath.finish_mem_vertices _)).trans
      (alternatingPath_private_coordinate_ge_start
        (alternatingPath z i si p sp hip hsi hsp a).finish
        r sr p sp hrp hsr hsp b x hx)

lemma continueAlternatingPath_finish_signed_continuation_coordinate {d : ℕ}
    (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (r : Fin d) (sr : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hrp : r ≠ p)
    (hsi : Int.natAbs si = 1) (hsr : Int.natAbs sr = 1)
    (hsp : Int.natAbs sp = 1) (a b : ℕ)
    (hcompat : i ≠ r ∨ (i = r ∧ si = sr)) :
    sr * z r + b ≤ sr *
      (continueAlternatingPath z i si r sr p sp hip hrp
        hsi hsr hsp a b hcompat).finish r := by
  rw [finish_continueAlternatingPath]
  have hfirst : sr * z r ≤ sr *
      (alternatingPath z i si p sp hip hsi hsp a).finish r := by
    rcases hcompat with hir | ⟨hir, hs⟩
    · have hcoord := alternatingPath_other_coordinate
        z i si p sp hip hsi hsp a
        (alternatingPath z i si p sp hip hsi hsp a).finish
        (LatticePath.finish_mem_vertices _) r hir.symm hrp
      rw [hcoord]
    · subst r
      subst sr
      exact alternatingPath_private_coordinate_ge_start
        z i si p sp hip hsi hsp a _ (LatticePath.finish_mem_vertices _)
  have hsecond : sr *
      (alternatingPath
        (alternatingPath z i si p sp hip hsi hsp a).finish
        r sr p sp hrp hsr hsp b).finish r =
      sr * (alternatingPath z i si p sp hip hsi hsp a).finish r + b := by
    rw [finish_alternatingPath]
    have hsq := sq_eq_one_of_natAbs_eq_one sr hsr
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
      signedBasis_of_ne hrp]
    nlinarith
  nlinarith

lemma alternatingPath_different_reservoirs_common_vertices {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ)
    (p : Fin d) (sp : ℤ) (q : Fin d) (sq : ℤ)
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hsi : Int.natAbs si = 1) (hsp : Int.natAbs sp = 1)
    (hsq : Int.natAbs sq = 1) (a b : ℕ) :
    let first := alternatingPath z i si p sp hip hsi hsp a
    let second := alternatingPath first.finish i si q sq hiq hsi hsq b
    ∀ x, x ∈ first.vertices → x ∈ second.vertices → x = first.finish := by
  dsimp
  intro x hxFirst hxSecond
  let first := alternatingPath z i si p sp hip hsi hsp a
  have hprivate : si * x i = si * first.finish i := by
    exact le_antisymm
      (alternatingPath_private_coordinate_le_finish
        z i si p sp hip hsi hsp a x hxFirst)
      (alternatingPath_private_coordinate_ge_start
        first.finish i si q sq hiq hsi hsq b x hxSecond)
  have hpcoord := alternatingPath_other_coordinate
    first.finish i si q sq hiq hsi hsq b x hxSecond p (Ne.symm hip) hpq
  have hreservoir : sp * x p ≤ sp * first.finish p := by rw [hpcoord]
  exact alternatingPath_eq_finish_of_private_eq_of_reservoir_le
    z i si p sp hip hsi hsp a x hxFirst hprivate hreservoir

def continueAlternatingDifferentReservoirs {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ)
    (p : Fin d) (sp : ℤ) (q : Fin d) (sq : ℤ)
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hsi : Int.natAbs si = 1) (hsp : Int.natAbs sp = 1)
    (hsq : Int.natAbs sq = 1) (a b : ℕ) : LatticePath d :=
  let first := alternatingPath z i si p sp hip hsi hsp a
  let second := alternatingPath first.finish i si q sq hiq hsi hsq b
  join first second (by
    exact (start_alternatingPath first.finish i si q sq hiq hsi hsq b).symm)
    (alternatingPath_different_reservoirs_common_vertices
      z i si p sp q sq hip hiq hpq hsi hsp hsq a b)

@[simp] lemma start_continueAlternatingDifferentReservoirs {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ)
    (p : Fin d) (sp : ℤ) (q : Fin d) (sq : ℤ)
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hsi : Int.natAbs si = 1) (hsp : Int.natAbs sp = 1)
    (hsq : Int.natAbs sq = 1) (a b : ℕ) :
    (continueAlternatingDifferentReservoirs z i si p sp q sq
      hip hiq hpq hsi hsp hsq a b).start = z := by
  simp [continueAlternatingDifferentReservoirs]

@[simp] lemma finish_continueAlternatingDifferentReservoirs {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ)
    (p : Fin d) (sp : ℤ) (q : Fin d) (sq : ℤ)
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hsi : Int.natAbs si = 1) (hsp : Int.natAbs sp = 1)
    (hsq : Int.natAbs sq = 1) (a b : ℕ) :
    (continueAlternatingDifferentReservoirs z i si p sp q sq
      hip hiq hpq hsi hsp hsq a b).finish =
      (alternatingPath
        (alternatingPath z i si p sp hip hsi hsp a).finish
        i si q sq hiq hsi hsq b).finish := by
  simp [continueAlternatingDifferentReservoirs]

@[simp] lemma edgeLength_continueAlternatingDifferentReservoirs {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ)
    (p : Fin d) (sp : ℤ) (q : Fin d) (sq : ℤ)
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hsi : Int.natAbs si = 1) (hsp : Int.natAbs sp = 1)
    (hsq : Int.natAbs sq = 1) (a b : ℕ) :
    (continueAlternatingDifferentReservoirs z i si p sp q sq
      hip hiq hpq hsi hsp hsq a b).edgeLength = 2 * a + 2 * b := by
  simp [continueAlternatingDifferentReservoirs]

lemma mem_vertices_continueAlternatingDifferentReservoirs {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ)
    (p : Fin d) (sp : ℤ) (q : Fin d) (sq : ℤ)
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hsi : Int.natAbs si = 1) (hsp : Int.natAbs sp = 1)
    (hsq : Int.natAbs sq = 1) (a b : ℕ) (x : LatticePoint d)
    (hx : x ∈ (continueAlternatingDifferentReservoirs z i si p sp q sq
      hip hiq hpq hsi hsp hsq a b).vertices) :
    x ∈ (alternatingPath z i si p sp hip hsi hsp a).vertices ∨
      x ∈ (alternatingPath
        (alternatingPath z i si p sp hip hsi hsp a).finish
        i si q sq hiq hsi hsq b).vertices := by
  change x ∈ (alternatingPath z i si p sp hip hsi hsp a).vertices ++
    (alternatingPath (alternatingPath z i si p sp hip hsi hsp a).finish
      i si q sq hiq hsi hsq b).vertices.tail at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (List.mem_of_mem_tail hx)

lemma continueAlternatingDifferentReservoirs_eq_start_of_private_eq {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ)
    (p : Fin d) (sp : ℤ) (q : Fin d) (sq : ℤ)
    (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hsi : Int.natAbs si = 1) (hsp : Int.natAbs sp = 1)
    (hsq : Int.natAbs sq = 1) (a b : ℕ) (x : LatticePoint d)
    (hx : x ∈ (continueAlternatingDifferentReservoirs z i si p sp q sq
      hip hiq hpq hsi hsp hsq a b).vertices)
    (heq : si * x i = si * z i) : x = z := by
  rcases mem_vertices_continueAlternatingDifferentReservoirs
      z i si p sp q sq hip hiq hpq hsi hsp hsq a b x hx with hx | hx
  · exact alternatingPath_eq_start_of_private_coordinate_eq
      z i si p sp hip hsi hsp a x hx heq
  · have hge := alternatingPath_private_coordinate_ge_start
      (alternatingPath z i si p sp hip hsi hsp a).finish
      i si q sq hiq hsi hsq b x hx
    have hfinish : si * (alternatingPath z i si p sp hip hsi hsp a).finish i =
        si * z i + a := by
      rw [finish_alternatingPath]
      have hsq' := sq_eq_one_of_natAbs_eq_one si hsi
      simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
        signedBasis_of_ne hip]
      nlinarith
    have ha : a = 0 := by omega
    subst a
    have hfirst :
        (alternatingPath z i si p sp hip hsi hsp 0).finish = z := by
      rw [finish_alternatingPath]
      ext k
      simp [signedBasis]
    rw [hfirst] at hx
    exact alternatingPath_eq_start_of_private_coordinate_eq
      z i si q sq hiq hsi hsq b x hx heq

end LatticePath

end DisjointPaths
