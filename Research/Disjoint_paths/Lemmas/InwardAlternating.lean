import Disjoint_paths.Lemmas.Alternating

/-!
# Alternating paths starting on the outer sphere

These paths first move inward in a private coordinate and then outward in a
reservoir coordinate.  Thus their even vertices remain on the outer sphere
and their odd vertices lie on the inner sphere.
-/

namespace DisjointPaths

def inwardAlternatingPath {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) : LatticePath d :=
  alternatingPath y i (-si) p (-sp) hip (by simpa) (by simpa) m

lemma inwardAlternatingVertex_private_coordinate {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1) (k : ℕ) :
    si * (alternatingVertex y i (-si) p (-sp) k) i =
      si * y i - (k + 1) / 2 := by
  have hsq := sq_eq_one_of_natAbs_eq_one si hsi
  simp [alternatingVertex, signedBasis, hip]
  ring_nf at hsq ⊢
  rw [hsq]
  ring

lemma inwardAlternatingVertex_reservoir_coordinate {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsp : Int.natAbs sp = 1) (k : ℕ) :
    sp * (alternatingVertex y i (-si) p (-sp) k) p =
      sp * y p + k / 2 := by
  have hsq := sq_eq_one_of_natAbs_eq_one sp hsp
  simp [alternatingVertex, signedBasis, Ne.symm hip]
  ring_nf at hsq ⊢
  rw [hsq]
  ring

lemma l1Norm_inwardAlternatingVertex_even {d n : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m t : ℕ)
    (hy : y ∈ sphere d (n + 1))
    (hinward : (m : ℤ) ≤ si * y i)
    (houtward : 0 ≤ sp * y p) (ht : t ≤ m) :
    l1Norm (alternatingVertex y i (-si) p (-sp) (2 * t)) = n + 1 := by
  induction t with
  | zero => simpa [sphere] using hy
  | succ t ih =>
      have htm : t < m := by omega
      have heven := ih (by omega)
      have hin : 1 ≤ si * (alternatingVertex y i (-si) p (-sp) (2 * t)) i := by
        have hcoord := inwardAlternatingVertex_private_coordinate
          y i si p sp hip hsi (2 * t)
        have htZ : (t : ℤ) < m := by exact_mod_cast htm
        have hdiv : (2 * (t : ℤ) + 1) / 2 = t := by omega
        push_cast at hcoord
        rw [hdiv] at hcoord
        nlinarith
      have hodd :
          l1Norm (alternatingVertex y i (-si) p (-sp) (2 * t + 1)) = n := by
        have hform : alternatingVertex y i (-si) p (-sp) (2 * t + 1) =
            alternatingVertex y i (-si) p (-sp) (2 * t) - signedBasis i si := by
          simpa [sub_eq_add_neg] using
            (alternatingVertex_odd_eq_even_add y i (-si) p (-sp) t)
        rw [hform]
        have hmove := l1Norm_sub_signedBasis
          (alternatingVertex y i (-si) p (-sp) (2 * t)) i si hsi hin
        rw [heven] at hmove
        omega
      have hout : 0 ≤ sp *
          (alternatingVertex y i (-si) p (-sp) (2 * t + 1)) p := by
        have hcoord := inwardAlternatingVertex_reservoir_coordinate
          y i si p sp hip hsp (2 * t + 1)
        have hdiv : (2 * (t : ℤ) + 1) / 2 = t := by omega
        push_cast at hcoord
        rw [hdiv] at hcoord
        nlinarith
      have hform : alternatingVertex y i (-si) p (-sp) (2 * (t + 1)) =
          alternatingVertex y i (-si) p (-sp) (2 * t + 1) + signedBasis p sp := by
        simpa [sub_eq_add_neg] using
          (alternatingVertex_even_succ_eq_odd_sub y i (-si) p (-sp) t)
      rw [hform]
      have hmove := l1Norm_add_signedBasis
        (alternatingVertex y i (-si) p (-sp) (2 * t + 1)) p sp hsp hout
      rw [hodd] at hmove
      simpa [Nat.succ_eq_add_one] using hmove

lemma l1Norm_finish_inwardAlternatingPath {d n : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (hy : y ∈ sphere d (n + 1))
    (hinward : (m : ℤ) ≤ si * y i)
    (houtward : 0 ≤ sp * y p) :
    l1Norm (inwardAlternatingPath y i si p sp hip hsi hsp m).finish = n + 1 := by
  rw [inwardAlternatingPath, LatticePath.finish_alternatingPath]
  simpa [inwardAlternatingPath, alternatingVertex_even] using
    l1Norm_inwardAlternatingVertex_even y i si p sp hip hsi hsp m m hy hinward houtward le_rfl

lemma inwardAlternatingPath_finish_private_coordinate {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) :
    si * (inwardAlternatingPath y i si p sp hip hsi hsp m).finish i =
      si * y i - m := by
  rw [inwardAlternatingPath, LatticePath.finish_alternatingPath]
  have hsq := sq_eq_one_of_natAbs_eq_one si hsi
  simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same,
    signedBasis_of_ne hip]
  change si * (y i + (m : ℤ) * -si - 0) = si * y i - m
  calc
    si * (y i + (m : ℤ) * -si - 0) = si * y i - (m : ℤ) * (si * si) := by ring
    _ = si * y i - m := by simp [hsq]

namespace LatticePath

@[simp] lemma start_inwardAlternatingPath {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) :
    (inwardAlternatingPath y i si p sp hip hsi hsp m).start = y := by
  simp [inwardAlternatingPath]

@[simp] lemma edgeLength_inwardAlternatingPath {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) :
    (inwardAlternatingPath y i si p sp hip hsi hsp m).edgeLength = 2 * m := by
  simp [inwardAlternatingPath]

lemma inwardAlternatingPath_coordinate_displacement_le {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (inwardAlternatingPath y i si p sp hip hsi hsp m).vertices)
    (r : Fin d) :
    Int.natAbs (x r - y r) ≤ m := by
  simpa [inwardAlternatingPath] using
    alternatingPath_coordinate_displacement_le y i (-si) p (-sp) hip
      (by simpa using hsi) (by simpa using hsp) m x hx r

lemma inwardAlternatingPath_private_coordinate_le_start {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (inwardAlternatingPath y i si p sp hip hsi hsp m).vertices) :
    si * x i ≤ si * y i := by
  rcases (LatticePath.mem_vertices_alternatingPath_iff
    y i (-si) p (-sp) hip (by simpa) (by simpa) m x).mp (by
      simpa [inwardAlternatingPath] using hx) with ⟨k, hk, hkx⟩
  have hcoord := inwardAlternatingVertex_private_coordinate y i si p sp hip hsi k
  rw [hkx] at hcoord
  have hnonneg : (0 : ℤ) ≤ (k + 1) / 2 := by positivity
  omega

lemma inwardAlternatingPath_reservoir_coordinate_ge_start {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (inwardAlternatingPath y i si p sp hip hsi hsp m).vertices) :
    sp * y p ≤ sp * x p := by
  rcases (LatticePath.mem_vertices_alternatingPath_iff
    y i (-si) p (-sp) hip (by simpa) (by simpa) m x).mp (by
      simpa [inwardAlternatingPath] using hx) with ⟨k, hk, hkx⟩
  have hcoord := inwardAlternatingVertex_reservoir_coordinate
    y i si p sp hip hsp k
  rw [hkx] at hcoord
  have hnonneg : (0 : ℤ) ≤ k / 2 := by positivity
  omega

lemma inwardAlternatingPath_reservoir_coordinate_le_finish {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (inwardAlternatingPath y i si p sp hip hsi hsp m).vertices) :
    sp * x p ≤ sp * (inwardAlternatingPath y i si p sp hip hsi hsp m).finish p := by
  rcases (LatticePath.mem_vertices_alternatingPath_iff
    y i (-si) p (-sp) hip (by simpa) (by simpa) m x).mp (by
      simpa [inwardAlternatingPath] using hx) with ⟨k, hk, hkx⟩
  have hxcoord := inwardAlternatingVertex_reservoir_coordinate
    y i si p sp hip hsp k
  rw [hkx] at hxcoord
  rw [inwardAlternatingPath, LatticePath.finish_alternatingPath]
  have hsq := sq_eq_one_of_natAbs_eq_one sp hsp
  simp only [Pi.add_apply, Pi.sub_apply, signedBasis_of_ne (Ne.symm hip),
    signedBasis_same, sub_zero]
  have hkhalf : k / 2 ≤ m := by omega
  nlinarith

lemma inwardAlternatingPath_other_coordinate {d : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (inwardAlternatingPath y i si p sp hip hsi hsp m).vertices)
    (r : Fin d) (hri : r ≠ i) (hrp : r ≠ p) :
    x r = y r := by
  rcases (LatticePath.mem_vertices_alternatingPath_iff
    y i (-si) p (-sp) hip (by simpa) (by simpa) m x).mp (by
      simpa [inwardAlternatingPath] using hx) with ⟨k, -, rfl⟩
  exact alternatingVertex_apply_of_ne y i (-si) p (-sp) k r hri hrp

@[simp] lemma finish_inwardAlternatingPath {d : ℕ} (y : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) :
    (inwardAlternatingPath y i si p sp hip hsi hsp m).finish =
      y - signedBasis i (m * si) + signedBasis p (m * sp) := by
  simp [inwardAlternatingPath]
  ext j
  by_cases hji : j = i <;> by_cases hjp : j = p <;>
    simp [signedBasis, hji, hjp] <;> ring

lemma inwardAlternatingPath_vertices_on_two_spheres {d n : ℕ}
    (y : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (hy : y ∈ sphere d (n + 1))
    (hinward : (m : ℤ) ≤ si * y i)
    (houtward : 0 ≤ sp * y p) :
    ∀ x ∈ (inwardAlternatingPath y i si p sp hip hsi hsp m).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  have hsiSq := sq_eq_one_of_natAbs_eq_one si hsi
  have hspSq := sq_eq_one_of_natAbs_eq_one sp hsp
  let v := alternatingVertex y i (-si) p (-sp)
  have hnorm : ∀ t : ℕ, t ≤ m →
      l1Norm (v (2 * t)) = n + 1 ∧
        (t < m → l1Norm (v (2 * t + 1)) = n) := by
    intro t
    induction t with
    | zero =>
        intro _
        constructor
        · simpa [v, sphere] using hy
        · intro hm
          have hin : 1 ≤ si * (v 0) i := by
            have hmpos : (1 : ℤ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
            simpa [v] using le_trans hmpos hinward
          have hmove := l1Norm_sub_signedBasis (v 0) i si hsi hin
          have hform : v 1 = v 0 - signedBasis i si := by
            simpa [v, sub_eq_add_neg] using
              (alternatingVertex_odd_eq_even_add y i (-si) p (-sp) 0)
          rw [hform]
          have hynorm : l1Norm y = n + 1 := hy
          simpa [v, hynorm] using hmove
    | succ t ih =>
        intro htm
        have htlt : t < m := by omega
        have hprev := ih (by omega)
        have hout : 0 ≤ sp * (v (2 * t + 1)) p := by
          simp [v, alternatingVertex_odd, signedBasis, Ne.symm hip]
          have htNonneg : (0 : ℤ) ≤ t := by positivity
          nlinarith
        have heven : l1Norm (v (2 * (t + 1))) = n + 1 := by
          have hform : v (2 * (t + 1)) =
              v (2 * t + 1) + signedBasis p sp := by
            simp [v, alternatingVertex_even_succ_eq_odd_sub,
              sub_eq_add_neg]
          rw [hform]
          have hmove := l1Norm_add_signedBasis (v (2 * t + 1)) p sp hsp hout
          rw [hprev.2 htlt] at hmove
          exact hmove
        constructor
        · simpa [Nat.succ_eq_add_one] using heven
        · intro hsucc
          have hin : 1 ≤ si * (v (2 * (t + 1))) i := by
            have htZ : ((t + 1 : ℕ) : ℤ) ≤ m := by exact_mod_cast htm
            simp [v, alternatingVertex_even, signedBasis, hip]
            nlinarith
          have hform : v (2 * (t + 1) + 1) =
              v (2 * (t + 1)) - signedBasis i si := by
            simp [v, alternatingVertex_odd_eq_even_add, sub_eq_add_neg]
          rw [hform]
          have hmove := l1Norm_sub_signedBasis
            (v (2 * (t + 1))) i si hsi hin
          rw [heven] at hmove
          omega
  intro x hx
  rcases (LatticePath.mem_vertices_alternatingPath_iff
    y i (-si) p (-sp) hip (by simpa) (by simpa) m x).mp hx with ⟨k, hk, rfl⟩
  rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · right
    change l1Norm (v k) = n + 1
    rw [show k = 2 * t by omega]
    exact (hnorm t (by omega)).1
  · left
    change l1Norm (v k) = n
    rw [show k = 2 * t + 1 by omega]
    exact (hnorm t (by omega)).2 (by omega)

end LatticePath

end DisjointPaths
