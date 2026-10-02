import Disjoint_paths.Lemmas.InwardAlternating
import Disjoint_paths.Lemmas.PathJoin
import Disjoint_paths.Lemmas.Scale
import Disjoint_paths.Lemmas.Separation

/-!
# Outer paths with a fixed separating coordinate

An ordinary path first spends as much of its private coordinate as possible,
moving outward in the separating coordinate.  Any remaining displacement is
made with two consecutive reservoir stages.  The endpoint moves one full
scale both in its private direction and in the separating direction.
-/

namespace DisjointPaths

noncomputable section

def separatedOuterInitialLength {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (m : ℕ) : ℕ := min m (Int.natAbs (y i))

def separatedOuterRemainingLength {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (m : ℕ) : ℕ := m - separatedOuterInitialLength y i m

private lemma separatedOuter_common_vertices {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r) (m : ℕ) :
    let a := separatedOuterInitialLength y i m
    let b := separatedOuterRemainingLength y i m
    let first := inwardAlternatingPath y i (coordinateSign (y i))
      r (coordinateSign (y r)) hir (natAbs_coordinateSign _)
      (natAbs_coordinateSign _) a
    let rest := LatticePath.continueAlternatingDifferentReservoirs
      first.finish q (-coordinateSign (y q))
      r (-coordinateSign (y r)) i (coordinateSign (y i))
      hqr (Ne.symm hiq) (Ne.symm hir)
      (by simpa using natAbs_coordinateSign (y q))
      (by simpa using natAbs_coordinateSign (y r))
      (natAbs_coordinateSign _) b b
    ∀ x, x ∈ first.vertices → x ∈ rest.vertices → x = first.finish := by
  dsimp
  intro x hxFirst hxRest
  let a := separatedOuterInitialLength y i m
  let first := inwardAlternatingPath y i (coordinateSign (y i))
    r (coordinateSign (y r)) hir (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a
  have hxq : x q = y q := LatticePath.inwardAlternatingPath_other_coordinate
    y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
    (natAbs_coordinateSign _) (natAbs_coordinateSign _) a x hxFirst q
    (Ne.symm hiq) hqr
  have hfinishq : first.finish q = y q :=
    LatticePath.inwardAlternatingPath_other_coordinate
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a first.finish
      (LatticePath.finish_mem_vertices _) q (Ne.symm hiq) hqr
  apply LatticePath.continueAlternatingDifferentReservoirs_eq_start_of_private_eq
    first.finish q (-coordinateSign (y q))
    r (-coordinateSign (y r)) i (coordinateSign (y i))
    hqr (Ne.symm hiq) (Ne.symm hir)
    (by simpa using natAbs_coordinateSign (y q))
    (by simpa using natAbs_coordinateSign (y r))
    (natAbs_coordinateSign _) _ _ x hxRest
  rw [hxq, hfinishq]

def separatedOuterPath {d : ℕ} (y : LatticePoint d)
    (i q r : Fin d) (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r)
    (m : ℕ) : LatticePath d :=
  let a := separatedOuterInitialLength y i m
  let b := separatedOuterRemainingLength y i m
  let first := inwardAlternatingPath y i (coordinateSign (y i))
    r (coordinateSign (y r)) hir (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a
  let rest := LatticePath.continueAlternatingDifferentReservoirs
    first.finish q (-coordinateSign (y q))
    r (-coordinateSign (y r)) i (coordinateSign (y i))
    hqr (Ne.symm hiq) (Ne.symm hir)
    (by simpa using natAbs_coordinateSign (y q))
    (by simpa using natAbs_coordinateSign (y r))
    (natAbs_coordinateSign _) b b
  LatticePath.join first rest (by
    exact (LatticePath.start_continueAlternatingDifferentReservoirs
      first.finish q (-coordinateSign (y q))
      r (-coordinateSign (y r)) i (coordinateSign (y i))
      hqr (Ne.symm hiq) (Ne.symm hir)
      (by simpa using natAbs_coordinateSign (y q))
      (by simpa using natAbs_coordinateSign (y r))
      (natAbs_coordinateSign _) b b).symm)
    (separatedOuter_common_vertices y i q r hiq hir hqr m)

@[simp] lemma separatedOuterPath_start {d : ℕ} (y : LatticePoint d)
    (i q r : Fin d) (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r)
    (m : ℕ) : (separatedOuterPath y i q r hiq hir hqr m).start = y := by
  simp [separatedOuterPath]

@[simp] lemma separatedOuterPath_edgeLength {d : ℕ} (y : LatticePoint d)
    (i q r : Fin d) (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r)
    (m : ℕ) :
    (separatedOuterPath y i q r hiq hir hqr m).edgeLength =
      2 * separatedOuterInitialLength y i m +
        4 * separatedOuterRemainingLength y i m := by
  simp [separatedOuterPath]
  omega

lemma separatedOuterInitial_add_remaining {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (m : ℕ) :
    separatedOuterInitialLength y i m + separatedOuterRemainingLength y i m = m := by
  simp [separatedOuterInitialLength, separatedOuterRemainingLength]

lemma mem_vertices_separatedOuterPath {d : ℕ} (y : LatticePoint d)
    (i q r : Fin d) (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r)
    (m : ℕ) (x : LatticePoint d)
    (hx : x ∈ (separatedOuterPath y i q r hiq hir hqr m).vertices) :
    let a := separatedOuterInitialLength y i m
    let b := separatedOuterRemainingLength y i m
    let first := inwardAlternatingPath y i (coordinateSign (y i))
      r (coordinateSign (y r)) hir (natAbs_coordinateSign _)
      (natAbs_coordinateSign _) a
    x ∈ first.vertices ∨
      x ∈ (LatticePath.continueAlternatingDifferentReservoirs
        first.finish q (-coordinateSign (y q))
        r (-coordinateSign (y r)) i (coordinateSign (y i))
        hqr (Ne.symm hiq) (Ne.symm hir)
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r))
        (natAbs_coordinateSign _) b b).vertices := by
  dsimp
  change x ∈ _ ++ _ at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (List.mem_of_mem_tail hx)

lemma separatedOuterPath_finish_private_coordinate {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r) (m : ℕ) :
    coordinateSign (y i) *
      (separatedOuterPath y i q r hiq hir hqr m).finish i =
        coordinateSign (y i) * y i - m := by
  simp only [separatedOuterPath, LatticePath.finish_join,
    LatticePath.finish_continueAlternatingDifferentReservoirs]
  rw [LatticePath.finish_alternatingPath, LatticePath.finish_alternatingPath,
    LatticePath.finish_inwardAlternatingPath]
  have hsqI := sq_eq_one_of_natAbs_eq_one (coordinateSign (y i))
    (natAbs_coordinateSign (y i))
  simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
    signedBasis_of_ne hir, signedBasis_of_ne hiq]
  have hab := separatedOuterInitial_add_remaining y i m
  nlinarith

lemma separatedOuterPath_finish_separating_coordinate {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r) (m : ℕ) :
    coordinateSign (y r) *
      (separatedOuterPath y i q r hiq hir hqr m).finish r =
        coordinateSign (y r) * y r + m := by
  simp only [separatedOuterPath, LatticePath.finish_join,
    LatticePath.finish_continueAlternatingDifferentReservoirs]
  rw [LatticePath.finish_alternatingPath, LatticePath.finish_alternatingPath,
    LatticePath.finish_inwardAlternatingPath]
  have hsqR := sq_eq_one_of_natAbs_eq_one (coordinateSign (y r))
    (natAbs_coordinateSign (y r))
  simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
    signedBasis_of_ne (Ne.symm hir), signedBasis_of_ne (Ne.symm hqr)]
  have hab := separatedOuterInitial_add_remaining y i m
  nlinarith

lemma separatedOuterPath_vertices_on_two_spheres {d n : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r) (m : ℕ)
    (hy : y ∈ sphere d (n + 1))
    (hqReservoir : ((2 * m : ℕ) : ℤ) ≤ coordinateSign (y q) * y q) :
    ∀ x ∈ (separatedOuterPath y i q r hiq hir hqr m).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  let a := separatedOuterInitialLength y i m
  let b := separatedOuterRemainingLength y i m
  let first := inwardAlternatingPath y i (coordinateSign (y i))
    r (coordinateSign (y r)) hir (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a
  let mid := inwardAlternatingPath first.finish q (coordinateSign (y q))
    r (coordinateSign (y r)) hqr (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) b
  have haPrivate : (a : ℤ) ≤ coordinateSign (y i) * y i := by
    rw [coordinateSign_mul_self]
    exact_mod_cast (min_le_right m (Int.natAbs (y i)))
  have hfirstSphere : first.finish ∈ sphere d (n + 1) := by
    exact l1Norm_finish_inwardAlternatingPath
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a hy haPrivate
      (by rw [coordinateSign_mul_self]; positivity)
  have hfirstQ : first.finish q = y q := by
    exact LatticePath.inwardAlternatingPath_other_coordinate
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a first.finish
      (LatticePath.finish_mem_vertices _) q (Ne.symm hiq) hqr
  have hbLe : b ≤ m := by simp [b, separatedOuterRemainingLength]
  have hbPrivate : (b : ℤ) ≤ coordinateSign (y q) * first.finish q := by
    rw [hfirstQ]
    have hb2 : ((2 * b : ℕ) : ℤ) ≤ coordinateSign (y q) * y q := by
      exact hqReservoir.trans' (by exact_mod_cast Nat.mul_le_mul_left 2 hbLe)
    omega
  have hfirstR : 0 ≤ coordinateSign (y r) * first.finish r := by
    have hbase : 0 ≤ coordinateSign (y r) * y r := by
      rw [coordinateSign_mul_self]
      positivity
    exact hbase.trans (LatticePath.inwardAlternatingPath_reservoir_coordinate_ge_start
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a first.finish
      (LatticePath.finish_mem_vertices _))
  have hmidSphere : mid.finish ∈ sphere d (n + 1) := by
    exact l1Norm_finish_inwardAlternatingPath
      first.finish q (coordinateSign (y q)) r (coordinateSign (y r)) hqr
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) b hfirstSphere
      hbPrivate hfirstR
  intro x hx
  rcases mem_vertices_separatedOuterPath y i q r hiq hir hqr m x hx with hx | hx
  · exact LatticePath.inwardAlternatingPath_vertices_on_two_spheres
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a hy haPrivate
      (by rw [coordinateSign_mul_self]; positivity) x hx
  · rcases LatticePath.mem_vertices_continueAlternatingDifferentReservoirs
        first.finish q (-coordinateSign (y q))
        r (-coordinateSign (y r)) i (coordinateSign (y i))
        hqr (Ne.symm hiq) (Ne.symm hir)
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r))
        (natAbs_coordinateSign _) b b x (by simpa [first, b] using hx) with hx | hx
    · exact LatticePath.inwardAlternatingPath_vertices_on_two_spheres
        first.finish q (coordinateSign (y q)) r (coordinateSign (y r)) hqr
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) b hfirstSphere
        hbPrivate hfirstR x (by simpa [inwardAlternatingPath] using hx)
    · by_cases hb : b = 0
      · rw [hb] at hx
        let z0 := (alternatingPath first.finish q (-coordinateSign (y q))
          r (-coordinateSign (y r)) hqr
          (by simpa using natAbs_coordinateSign (y q))
          (by simpa using natAbs_coordinateSign (y r)) 0).finish
        rcases (LatticePath.mem_vertices_alternatingPath_iff
          z0 q (-coordinateSign (y q)) i (coordinateSign (y i))
          (Ne.symm hiq) (by simpa using natAbs_coordinateSign (y q))
          (natAbs_coordinateSign _) 0 x).mp (by simpa [z0] using hx) with
          ⟨k, hk, hkx⟩
        have hk0 : k = 0 := by omega
        subst k
        have hxStart : x = z0 := by
          rw [← hkx]
          simp
        have hz0 : z0 = first.finish := by
          dsimp [z0]
          rw [LatticePath.finish_alternatingPath]
          ext j
          simp [signedBasis]
        rw [hxStart, hz0]
        exact Or.inr hfirstSphere
      · have haEq : a = Int.natAbs (y i) := by
          simp [a, b, separatedOuterInitialLength,
            separatedOuterRemainingLength] at hb ⊢
          omega
        have hfirstI : coordinateSign (y i) * first.finish i = 0 := by
          dsimp [first]
          rw [inwardAlternatingPath_finish_private_coordinate,
            coordinateSign_mul_self, haEq]
          omega
        have hmidI : mid.finish i = first.finish i := by
          exact LatticePath.inwardAlternatingPath_other_coordinate
            first.finish q (coordinateSign (y q)) r (coordinateSign (y r)) hqr
            (natAbs_coordinateSign _) (natAbs_coordinateSign _) b mid.finish
            (LatticePath.finish_mem_vertices _) i hiq hir
        have houtI : 0 ≤ (-coordinateSign (y i)) * mid.finish i := by
          rw [hmidI]
          nlinarith
        have hmidQ : coordinateSign (y q) * mid.finish q =
            coordinateSign (y q) * first.finish q - b := by
          exact inwardAlternatingPath_finish_private_coordinate
            first.finish q (coordinateSign (y q)) r (coordinateSign (y r)) hqr
            (natAbs_coordinateSign _) (natAbs_coordinateSign _) b
        have hbPrivate2 : (b : ℤ) ≤ coordinateSign (y q) * mid.finish q := by
          have hb2 : (2 : ℤ) * b ≤ coordinateSign (y q) * y q := by
            have hb2m : (((2 * b : ℕ) : ℤ)) ≤ ((2 * m : ℕ) : ℤ) := by
              exact_mod_cast (show 2 * b ≤ 2 * m by omega)
            simpa using hb2m.trans hqReservoir
          rw [hfirstQ] at hmidQ
          omega
        exact LatticePath.inwardAlternatingPath_vertices_on_two_spheres
          mid.finish q (coordinateSign (y q)) i (-coordinateSign (y i))
          (Ne.symm hiq) (natAbs_coordinateSign _)
          (by simpa using natAbs_coordinateSign (y i)) b hmidSphere
          hbPrivate2 houtI x (by simpa [mid, inwardAlternatingPath] using hx)

lemma separatedOuterPath_private_coordinate_le_start {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (separatedOuterPath y i q r hiq hir hqr m).vertices) :
    coordinateSign (y i) * x i ≤ coordinateSign (y i) * y i := by
  let a := separatedOuterInitialLength y i m
  let b := separatedOuterRemainingLength y i m
  let first := inwardAlternatingPath y i (coordinateSign (y i))
    r (coordinateSign (y r)) hir (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a
  have hfirstFinish : coordinateSign (y i) * first.finish i =
      coordinateSign (y i) * y i - a := by
    exact inwardAlternatingPath_finish_private_coordinate
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a
  rcases mem_vertices_separatedOuterPath y i q r hiq hir hqr m x hx with hx | hx
  · exact LatticePath.inwardAlternatingPath_private_coordinate_le_start
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a x hx
  · rcases LatticePath.mem_vertices_continueAlternatingDifferentReservoirs
        first.finish q (-coordinateSign (y q))
        r (-coordinateSign (y r)) i (coordinateSign (y i))
        hqr (Ne.symm hiq) (Ne.symm hir)
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r))
        (natAbs_coordinateSign _) b b x (by simpa [first, b] using hx) with hx | hx
    · have hcoord := LatticePath.alternatingPath_other_coordinate
        first.finish q (-coordinateSign (y q)) r (-coordinateSign (y r)) hqr
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r)) b x hx i hiq hir
      rw [hcoord, hfirstFinish]
      omega
    · have hmidI :
          (alternatingPath first.finish q (-coordinateSign (y q))
            r (-coordinateSign (y r)) hqr
            (by simpa using natAbs_coordinateSign (y q))
            (by simpa using natAbs_coordinateSign (y r)) b).finish i =
            first.finish i := by
          exact LatticePath.alternatingPath_other_coordinate
            first.finish q (-coordinateSign (y q)) r (-coordinateSign (y r)) hqr
            (by simpa using natAbs_coordinateSign (y q))
            (by simpa using natAbs_coordinateSign (y r)) b _
            (LatticePath.finish_mem_vertices _) i hiq hir
      have hle := LatticePath.alternatingPath_reservoir_coordinate_le_start
        (alternatingPath first.finish q (-coordinateSign (y q))
          r (-coordinateSign (y r)) hqr
          (by simpa using natAbs_coordinateSign (y q))
          (by simpa using natAbs_coordinateSign (y r)) b).finish
        q (-coordinateSign (y q)) i (coordinateSign (y i))
        (Ne.symm hiq) (by simpa using natAbs_coordinateSign (y q))
        (natAbs_coordinateSign _) b x hx
      rw [hmidI, hfirstFinish] at hle
      omega

lemma separatedOuterPath_other_coordinate {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (separatedOuterPath y i q r hiq hir hqr m).vertices)
    (k : Fin d) (hki : k ≠ i) (hkq : k ≠ q) (hkr : k ≠ r) :
    x k = y k := by
  let a := separatedOuterInitialLength y i m
  let b := separatedOuterRemainingLength y i m
  let first := inwardAlternatingPath y i (coordinateSign (y i))
    r (coordinateSign (y r)) hir (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a
  have hfirst : first.finish k = y k :=
    LatticePath.inwardAlternatingPath_other_coordinate
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a first.finish
      (LatticePath.finish_mem_vertices _) k hki hkr
  rcases mem_vertices_separatedOuterPath y i q r hiq hir hqr m x hx with hx | hx
  · exact LatticePath.inwardAlternatingPath_other_coordinate
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a x hx k hki hkr
  · rcases LatticePath.mem_vertices_continueAlternatingDifferentReservoirs
        first.finish q (-coordinateSign (y q))
        r (-coordinateSign (y r)) i (coordinateSign (y i))
        hqr (Ne.symm hiq) (Ne.symm hir)
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r))
        (natAbs_coordinateSign _) b b x (by simpa [first, b] using hx) with hx | hx
    · rw [LatticePath.alternatingPath_other_coordinate
        first.finish q (-coordinateSign (y q)) r (-coordinateSign (y r)) hqr
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r)) b x hx k hkq hkr,
        hfirst]
    · have hmid :
          (alternatingPath first.finish q (-coordinateSign (y q))
            r (-coordinateSign (y r)) hqr
            (by simpa using natAbs_coordinateSign (y q))
            (by simpa using natAbs_coordinateSign (y r)) b).finish k = y k := by
          rw [LatticePath.alternatingPath_other_coordinate
            first.finish q (-coordinateSign (y q)) r (-coordinateSign (y r)) hqr
            (by simpa using natAbs_coordinateSign (y q))
            (by simpa using natAbs_coordinateSign (y r)) b _
            (LatticePath.finish_mem_vertices _) k hkq hkr, hfirst]
      rw [LatticePath.alternatingPath_other_coordinate
        (alternatingPath first.finish q (-coordinateSign (y q))
          r (-coordinateSign (y r)) hqr
          (by simpa using natAbs_coordinateSign (y q))
          (by simpa using natAbs_coordinateSign (y r)) b).finish
        q (-coordinateSign (y q)) i (coordinateSign (y i))
        (Ne.symm hiq) (by simpa using natAbs_coordinateSign (y q))
        (natAbs_coordinateSign _) b x hx k hkq hki, hmid]

lemma separatedOuterPath_eq_start_of_private_coordinate_eq {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r)
    (m : ℕ) (hm : 0 < m) (hyi : y i ≠ 0)
    (x : LatticePoint d)
    (hx : x ∈ (separatedOuterPath y i q r hiq hir hqr m).vertices)
    (heq : coordinateSign (y i) * x i = coordinateSign (y i) * y i) :
    x = y := by
  let a := separatedOuterInitialLength y i m
  let b := separatedOuterRemainingLength y i m
  let first := inwardAlternatingPath y i (coordinateSign (y i))
    r (coordinateSign (y r)) hir (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a
  have ha : 0 < a := by
    have habs : 0 < Int.natAbs (y i) := Int.natAbs_pos.mpr hyi
    simp [a, separatedOuterInitialLength]
    omega
  have hfirstFinish : coordinateSign (y i) * first.finish i =
      coordinateSign (y i) * y i - a :=
    inwardAlternatingPath_finish_private_coordinate
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a
  rcases mem_vertices_separatedOuterPath y i q r hiq hir hqr m x hx with hx | hx
  · apply LatticePath.alternatingPath_eq_start_of_private_coordinate_eq
      y i (-coordinateSign (y i)) r (-coordinateSign (y r)) hir
      (by simpa using natAbs_coordinateSign (y i))
      (by simpa using natAbs_coordinateSign (y r)) a x
      (by simpa [inwardAlternatingPath] using hx)
    nlinarith
  · rcases LatticePath.mem_vertices_continueAlternatingDifferentReservoirs
        first.finish q (-coordinateSign (y q))
        r (-coordinateSign (y r)) i (coordinateSign (y i))
        hqr (Ne.symm hiq) (Ne.symm hir)
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r))
        (natAbs_coordinateSign _) b b x (by simpa [first, b] using hx) with hx | hx
    · have hcoord := LatticePath.alternatingPath_other_coordinate
        first.finish q (-coordinateSign (y q)) r (-coordinateSign (y r)) hqr
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r)) b x hx i hiq hir
      rw [hcoord, hfirstFinish] at heq
      omega
    · have hmidI :
          (alternatingPath first.finish q (-coordinateSign (y q))
            r (-coordinateSign (y r)) hqr
            (by simpa using natAbs_coordinateSign (y q))
            (by simpa using natAbs_coordinateSign (y r)) b).finish i =
            first.finish i :=
        LatticePath.alternatingPath_other_coordinate
          first.finish q (-coordinateSign (y q)) r (-coordinateSign (y r)) hqr
          (by simpa using natAbs_coordinateSign (y q))
          (by simpa using natAbs_coordinateSign (y r)) b _
          (LatticePath.finish_mem_vertices _) i hiq hir
      have hle := LatticePath.alternatingPath_reservoir_coordinate_le_start
        (alternatingPath first.finish q (-coordinateSign (y q))
          r (-coordinateSign (y r)) hqr
          (by simpa using natAbs_coordinateSign (y q))
          (by simpa using natAbs_coordinateSign (y r)) b).finish
        q (-coordinateSign (y q)) i (coordinateSign (y i))
        (Ne.symm hiq) (by simpa using natAbs_coordinateSign (y q))
        (natAbs_coordinateSign _) b x hx
      rw [hmidI, hfirstFinish] at hle
      omega

lemma separatedOuterPaths_edgeDisjoint_of_distinct {d : ℕ}
    (y : LatticePoint d) (q r : Fin d) (hqr : q ≠ r) (m : ℕ) (hm : 0 < m)
    (i j : Fin d) (hyi : y i ≠ 0) (hyj : y j ≠ 0)
    (hiq : i ≠ q) (hir : i ≠ r) (hjq : j ≠ q) (hjr : j ≠ r)
    (hij : i ≠ j) :
    Disjoint (separatedOuterPath y i q r hiq hir hqr m).edgeSet
      (separatedOuterPath y j q r hjq hjr hqr m).edgeSet := by
  apply LatticePath.edgeDisjoint_of_common_vertices_subsingleton _ _ y
  intro x hxi hxj
  apply separatedOuterPath_eq_start_of_private_coordinate_eq
    y i q r hiq hir hqr m hm hyi x hxi
  have hcoord := separatedOuterPath_other_coordinate
    y j q r hjq hjr hqr m x hxj i hij hiq hir
  rw [hcoord]

lemma separatedOuterPath_endpoint_far_of_distinct {d : ℕ}
    (y : LatticePoint d) (q r : Fin d) (hqr : q ≠ r) (m : ℕ)
    (i j : Fin d) (hiq : i ≠ q) (hir : i ≠ r)
    (hjq : j ≠ q) (hjr : j ≠ r) (hij : i ≠ j)
    (rsep : ℝ) (hrsep : rsep ≤ (m : ℝ)) :
    ∀ x ∈ (separatedOuterPath y j q r hjq hjr hqr m).vertices,
      rsep ≤ (l1Dist (separatedOuterPath y i q r hiq hir hqr m).finish x : ℝ) := by
  apply endpoint_far_from_vertices_of_signed_coordinate_gap
    (separatedOuterPath y i q r hiq hir hqr m)
    (separatedOuterPath y j q r hjq hjr hqr m)
    i (-coordinateSign (y i)) (by simpa using natAbs_coordinateSign (y i))
    rsep (-coordinateSign (y i) * y i) m hrsep (by positivity)
  · have hfinish := separatedOuterPath_finish_private_coordinate
      y i q r hiq hir hqr m
    nlinarith
  · intro x hx
    have hcoord := separatedOuterPath_other_coordinate
      y j q r hjq hjr hqr m x hx i hij hiq hir
    rw [hcoord]

lemma separatedOuterPath_separating_coordinate_bounds {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (separatedOuterPath y i q r hiq hir hqr m).vertices) :
    coordinateSign (y r) * y r ≤ coordinateSign (y r) * x r ∧
      coordinateSign (y r) * x r ≤ coordinateSign (y r) * y r + m := by
  let a := separatedOuterInitialLength y i m
  let b := separatedOuterRemainingLength y i m
  let first := inwardAlternatingPath y i (coordinateSign (y i))
    r (coordinateSign (y r)) hir (natAbs_coordinateSign _)
    (natAbs_coordinateSign _) a
  have hab := separatedOuterInitial_add_remaining y i m
  have hbase : coordinateSign (y r) * y r ≤
      coordinateSign (y r) * first.finish r :=
    LatticePath.inwardAlternatingPath_reservoir_coordinate_ge_start
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a first.finish
      (LatticePath.finish_mem_vertices _)
  have hfirstUpper : ∀ w ∈ first.vertices,
      coordinateSign (y r) * w r ≤ coordinateSign (y r) * first.finish r :=
    LatticePath.inwardAlternatingPath_reservoir_coordinate_le_finish
      y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) a
  have hfirstFinish : coordinateSign (y r) * first.finish r =
      coordinateSign (y r) * y r + a := by
    rw [LatticePath.finish_inwardAlternatingPath]
    have hsq := sq_eq_one_of_natAbs_eq_one (coordinateSign (y r))
      (natAbs_coordinateSign (y r))
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
      signedBasis_of_ne (Ne.symm hir)]
    nlinarith
  rcases mem_vertices_separatedOuterPath y i q r hiq hir hqr m x hx with hx | hx
  · constructor
    · exact (LatticePath.inwardAlternatingPath_reservoir_coordinate_ge_start
        y i (coordinateSign (y i)) r (coordinateSign (y r)) hir
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) a x hx)
    · have := hfirstUpper x hx
      rw [hfirstFinish] at this
      omega
  · rcases LatticePath.mem_vertices_continueAlternatingDifferentReservoirs
        first.finish q (-coordinateSign (y q))
        r (-coordinateSign (y r)) i (coordinateSign (y i))
        hqr (Ne.symm hiq) (Ne.symm hir)
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r))
        (natAbs_coordinateSign _) b b x (by simpa [first, b] using hx) with hx | hx
    · have hlower := LatticePath.alternatingPath_reservoir_coordinate_le_start
        first.finish q (-coordinateSign (y q)) r (-coordinateSign (y r)) hqr
        (by simpa using natAbs_coordinateSign (y q))
        (by simpa using natAbs_coordinateSign (y r)) b x hx
      have hupper := LatticePath.inwardAlternatingPath_reservoir_coordinate_le_finish
        first.finish q (coordinateSign (y q)) r (coordinateSign (y r)) hqr
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) b x
        (by simpa [inwardAlternatingPath] using hx)
      have hmidFinish : coordinateSign (y r) *
          (inwardAlternatingPath first.finish q (coordinateSign (y q))
            r (coordinateSign (y r)) hqr (natAbs_coordinateSign _)
            (natAbs_coordinateSign _) b).finish r =
          coordinateSign (y r) * first.finish r + b := by
        rw [LatticePath.finish_inwardAlternatingPath]
        have hsq := sq_eq_one_of_natAbs_eq_one (coordinateSign (y r))
          (natAbs_coordinateSign (y r))
        simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
          signedBasis_of_ne (Ne.symm hqr)]
        nlinarith
      constructor
      · nlinarith
      · rw [hmidFinish, hfirstFinish] at hupper
        omega
    · have hmidR :
          (alternatingPath first.finish q (-coordinateSign (y q))
            r (-coordinateSign (y r)) hqr
            (by simpa using natAbs_coordinateSign (y q))
            (by simpa using natAbs_coordinateSign (y r)) b).finish r =
          (inwardAlternatingPath first.finish q (coordinateSign (y q))
            r (coordinateSign (y r)) hqr (natAbs_coordinateSign _)
            (natAbs_coordinateSign _) b).finish r := by rfl
      have hxR := LatticePath.alternatingPath_other_coordinate
        (alternatingPath first.finish q (-coordinateSign (y q))
          r (-coordinateSign (y r)) hqr
          (by simpa using natAbs_coordinateSign (y q))
          (by simpa using natAbs_coordinateSign (y r)) b).finish
        q (-coordinateSign (y q)) i (coordinateSign (y i))
        (Ne.symm hiq) (by simpa using natAbs_coordinateSign (y q))
        (natAbs_coordinateSign _) b x hx r (Ne.symm hqr) (Ne.symm hir)
      have hmidLower := LatticePath.inwardAlternatingPath_reservoir_coordinate_ge_start
        first.finish q (coordinateSign (y q)) r (coordinateSign (y r)) hqr
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) b
        (inwardAlternatingPath first.finish q (coordinateSign (y q))
          r (coordinateSign (y r)) hqr (natAbs_coordinateSign _)
          (natAbs_coordinateSign _) b).finish (LatticePath.finish_mem_vertices _)
      have hmidFinish : coordinateSign (y r) *
          (inwardAlternatingPath first.finish q (coordinateSign (y q))
            r (coordinateSign (y r)) hqr (natAbs_coordinateSign _)
            (natAbs_coordinateSign _) b).finish r =
          coordinateSign (y r) * first.finish r + b := by
        rw [LatticePath.finish_inwardAlternatingPath]
        have hsq := sq_eq_one_of_natAbs_eq_one (coordinateSign (y r))
          (natAbs_coordinateSign (y r))
        simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
          signedBasis_of_ne (Ne.symm hqr)]
        nlinarith
      rw [hxR, hmidR, hmidFinish, hfirstFinish]
      constructor <;> omega

def exceptionalSeparatedOuterPath {d : ℕ} (y : LatticePoint d)
    (q r : Fin d) (hqr : q ≠ r) (m : ℕ) : LatticePath d :=
  inwardAlternatingPath y q (coordinateSign (y q)) r (coordinateSign (y r))
    hqr (natAbs_coordinateSign _) (natAbs_coordinateSign _) (3 * m)

@[simp] lemma exceptionalSeparatedOuterPath_start {d : ℕ} (y : LatticePoint d)
    (q r : Fin d) (hqr : q ≠ r) (m : ℕ) :
    (exceptionalSeparatedOuterPath y q r hqr m).start = y := by
  simp [exceptionalSeparatedOuterPath]

@[simp] lemma exceptionalSeparatedOuterPath_edgeLength {d : ℕ}
    (y : LatticePoint d) (q r : Fin d) (hqr : q ≠ r) (m : ℕ) :
    (exceptionalSeparatedOuterPath y q r hqr m).edgeLength = 6 * m := by
  simp [exceptionalSeparatedOuterPath]
  omega

lemma exceptionalSeparatedOuterPath_vertices_on_two_spheres {d n : ℕ}
    (y : LatticePoint d) (q r : Fin d) (hqr : q ≠ r) (m : ℕ)
    (hy : y ∈ sphere d (n + 1))
    (hqReservoir : ((3 * m : ℕ) : ℤ) ≤ coordinateSign (y q) * y q) :
    ∀ x ∈ (exceptionalSeparatedOuterPath y q r hqr m).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  exact LatticePath.inwardAlternatingPath_vertices_on_two_spheres
    y q (coordinateSign (y q)) r (coordinateSign (y r)) hqr
    (natAbs_coordinateSign _) (natAbs_coordinateSign _) (3 * m) hy
    hqReservoir (by rw [coordinateSign_mul_self]; positivity)

lemma exceptionalSeparatedOuterPath_finish_separating_coordinate {d : ℕ}
    (y : LatticePoint d) (q r : Fin d) (hqr : q ≠ r) (m : ℕ) :
    coordinateSign (y r) *
      (exceptionalSeparatedOuterPath y q r hqr m).finish r =
        coordinateSign (y r) * y r + 3 * m := by
  rw [exceptionalSeparatedOuterPath, LatticePath.finish_inwardAlternatingPath]
  have hsq := sq_eq_one_of_natAbs_eq_one (coordinateSign (y r))
    (natAbs_coordinateSign (y r))
  simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
    signedBasis_of_ne (Ne.symm hqr)]
  push_cast
  nlinarith

lemma exceptionalSeparatedOuterPath_other_coordinate {d : ℕ}
    (y : LatticePoint d) (q r : Fin d) (hqr : q ≠ r) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (exceptionalSeparatedOuterPath y q r hqr m).vertices)
    (i : Fin d) (hiq : i ≠ q) (hir : i ≠ r) : x i = y i := by
  exact LatticePath.inwardAlternatingPath_other_coordinate
    y q (coordinateSign (y q)) r (coordinateSign (y r)) hqr
    (natAbs_coordinateSign _) (natAbs_coordinateSign _) (3 * m)
    x hx i hiq hir

lemma separatedOuterPath_edgeDisjoint_exceptional {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r)
    (m : ℕ) (hm : 0 < m) (hyi : y i ≠ 0) :
    Disjoint (separatedOuterPath y i q r hiq hir hqr m).edgeSet
      (exceptionalSeparatedOuterPath y q r hqr m).edgeSet := by
  apply LatticePath.edgeDisjoint_of_common_vertices_subsingleton _ _ y
  intro x hxi hxq
  apply separatedOuterPath_eq_start_of_private_coordinate_eq
    y i q r hiq hir hqr m hm hyi x hxi
  rw [exceptionalSeparatedOuterPath_other_coordinate
    y q r hqr m x hxq i hiq hir]

lemma separatedOuterPath_endpoint_far_exceptional {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r) (m : ℕ)
    (rsep : ℝ) (hrsep : rsep ≤ (m : ℝ)) :
    ∀ x ∈ (exceptionalSeparatedOuterPath y q r hqr m).vertices,
      rsep ≤ (l1Dist (separatedOuterPath y i q r hiq hir hqr m).finish x : ℝ) := by
  apply endpoint_far_from_vertices_of_signed_coordinate_gap
    (separatedOuterPath y i q r hiq hir hqr m)
    (exceptionalSeparatedOuterPath y q r hqr m)
    i (-coordinateSign (y i)) (by simpa using natAbs_coordinateSign (y i))
    rsep (-coordinateSign (y i) * y i) m hrsep (by positivity)
  · have hfinish := separatedOuterPath_finish_private_coordinate
      y i q r hiq hir hqr m
    nlinarith
  · intro x hx
    rw [exceptionalSeparatedOuterPath_other_coordinate
      y q r hqr m x hx i hiq hir]

lemma exceptionalSeparatedOuterPath_endpoint_far_ordinary {d : ℕ}
    (y : LatticePoint d) (i q r : Fin d)
    (hiq : i ≠ q) (hir : i ≠ r) (hqr : q ≠ r) (m : ℕ)
    (rsep : ℝ) (hrsep : rsep ≤ (m : ℝ)) :
    ∀ x ∈ (separatedOuterPath y i q r hiq hir hqr m).vertices,
      rsep ≤ (l1Dist (exceptionalSeparatedOuterPath y q r hqr m).finish x : ℝ) := by
  apply endpoint_far_from_vertices_of_signed_coordinate_gap
    (exceptionalSeparatedOuterPath y q r hqr m)
    (separatedOuterPath y i q r hiq hir hqr m)
    r (coordinateSign (y r)) (natAbs_coordinateSign (y r))
    rsep (coordinateSign (y r) * y r + m) m hrsep (by positivity)
  · rw [exceptionalSeparatedOuterPath_finish_separating_coordinate]
    omega
  · intro x hx
    exact (separatedOuterPath_separating_coordinate_bounds
      y i q r hiq hir hqr m x hx).2

end

end DisjointPaths
