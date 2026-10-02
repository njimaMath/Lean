import Disjoint_paths.Lemmas.CoordinateMoves
import Mathlib.Tactic.Linarith

/-!
# Alternating coordinate paths

This is the basic two-step word used by every fan: move once in a private
signed coordinate and once back through a reservoir coordinate.
-/

namespace DisjointPaths

def alternatingVertex {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ) (k : ℕ) : LatticePoint d :=
  z + signedBasis i (((k + 1) / 2 : ℕ) * si) -
    signedBasis p ((k / 2 : ℕ) * sp)

@[simp] lemma alternatingVertex_zero {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ) :
    alternatingVertex z i si p sp 0 = z := by
  ext j
  simp [alternatingVertex, signedBasis]

lemma alternatingVertex_even {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ) (t : ℕ) :
    alternatingVertex z i si p sp (2 * t) =
      z + signedBasis i (t * si) - signedBasis p (t * sp) := by
  have hhalf : (2 * t) / 2 = t := by omega
  have hhalf' : (2 * t + 1) / 2 = t := by omega
  simp [alternatingVertex, hhalf, hhalf']

lemma alternatingVertex_odd {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ) (t : ℕ) :
    alternatingVertex z i si p sp (2 * t + 1) =
      z + signedBasis i ((t + 1) * si) - signedBasis p (t * sp) := by
  have hhalf : (2 * t + 1) / 2 = t := by omega
  have hhalf' : (2 * t + 1 + 1) / 2 = t + 1 := by omega
  simp [alternatingVertex, hhalf, hhalf']

lemma alternatingVertex_apply_of_ne {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ) (k : ℕ)
    (r : Fin d) (hri : r ≠ i) (hrp : r ≠ p) :
    alternatingVertex z i si p sp k r = z r := by
  simp [alternatingVertex, signedBasis, hri, hrp]

lemma alternatingVertex_private_coordinate {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1) (k : ℕ) :
    si * alternatingVertex z i si p sp k i =
      si * z i + (k + 1) / 2 := by
  have hsq := sq_eq_one_of_natAbs_eq_one si hsi
  simp [alternatingVertex, signedBasis, hip]
  ring_nf at hsq ⊢
  rw [hsq]
  ring

lemma alternatingVertex_reservoir_coordinate {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsp : Int.natAbs sp = 1) (k : ℕ) :
    sp * alternatingVertex z i si p sp k p =
      sp * z p - k / 2 := by
  have hsq := sq_eq_one_of_natAbs_eq_one sp hsp
  simp [alternatingVertex, signedBasis, Ne.symm hip]
  ring_nf at hsq ⊢
  rw [hsq]
  ring

/-- Every coordinate of an alternating path changes by at most the number of
complete pairs already prescribed. -/
lemma alternatingVertex_coordinate_displacement_le {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m k : ℕ) (hk : k ≤ 2 * m) (r : Fin d) :
    Int.natAbs (alternatingVertex z i si p sp k r - z r) ≤ m := by
  by_cases hri : r = i
  · subst r
    have hhalf : (k + 1) / 2 ≤ m := by omega
    simp [alternatingVertex, signedBasis, hip, Int.natAbs_mul, hsi]
    exact_mod_cast hhalf
  · by_cases hrp : r = p
    · subst r
      have hhalf : k / 2 ≤ m := by omega
      simp [alternatingVertex, signedBasis, Ne.symm hip, Int.natAbs_mul, hsp]
      exact_mod_cast hhalf
    · simp [alternatingVertex, signedBasis, hri, hrp]

lemma alternatingVertex_injective {d : ℕ} (z : LatticePoint d)
    {i p : Fin d} (hip : i ≠ p) {si sp : ℤ}
    (hsi : Int.natAbs si = 1) (hsp : Int.natAbs sp = 1) :
    Function.Injective (alternatingVertex z i si p sp) := by
  intro k l hkl
  have hsi0 : si ≠ 0 := by
    intro h
    simp [h] at hsi
  have hsp0 : sp ≠ 0 := by
    intro h
    simp [h] at hsp
  have hi := congrFun hkl i
  have hp := congrFun hkl p
  have hout : (k + 1) / 2 = (l + 1) / 2 := by
    simp [alternatingVertex, signedBasis, hip] at hi
    rcases hi with hi | hi
    · exact_mod_cast hi
    · exact False.elim (hsi0 hi)
  have hin : k / 2 = l / 2 := by
    simp [alternatingVertex, signedBasis, Ne.symm hip] at hp
    rcases hp with hp | hp
    · exact_mod_cast hp
    · exact False.elim (hsp0 hp)
  omega

lemma alternatingVertex_next {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ) (k : ℕ) :
    (Even k ∧ alternatingVertex z i si p sp (k + 1) =
        alternatingVertex z i si p sp k + signedBasis i si) ∨
      (Odd k ∧ alternatingVertex z i si p sp (k + 1) =
        alternatingVertex z i si p sp k - signedBasis p sp) := by
  rcases Nat.even_or_odd k with hk | hk
  · left
    rcases hk with ⟨t, rfl⟩
    refine ⟨⟨t, by omega⟩, ?_⟩
    rw [show t + t = 2 * t by omega]
    rw [show 2 * t + 1 = 2 * t + 1 by rfl,
      alternatingVertex_odd, alternatingVertex_even]
    ext j
    by_cases hji : j = i
    · subst j
      simp [signedBasis]
      ring
    · simp [signedBasis, hji]
  · right
    rcases hk with ⟨t, rfl⟩
    refine ⟨⟨t, by omega⟩, ?_⟩
    rw [show 2 * t + 1 + 1 = 2 * (t + 1) by omega,
      alternatingVertex_even, alternatingVertex_odd]
    ext j
    by_cases hjp : j = p
    · subst j
      simp [signedBasis]
      ring
    · simp [signedBasis, hjp]

lemma alternatingVertex_odd_eq_even_add {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ) (t : ℕ) :
    alternatingVertex z i si p sp (2 * t + 1) =
      alternatingVertex z i si p sp (2 * t) + signedBasis i si := by
  rw [alternatingVertex_odd, alternatingVertex_even]
  ext j
  by_cases hji : j = i
  · subst j
    simp [signedBasis]
    ring
  · simp [signedBasis, hji]

lemma alternatingVertex_even_succ_eq_odd_sub {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ) (t : ℕ) :
    alternatingVertex z i si p sp (2 * (t + 1)) =
      alternatingVertex z i si p sp (2 * t + 1) - signedBasis p sp := by
  rw [alternatingVertex_even, alternatingVertex_odd]
  ext j
  by_cases hjp : j = p
  · subst j
    simp [signedBasis]
    ring
  · simp [signedBasis, hjp]

/-- The path consisting of `m` complete private/reservoir pairs. -/
def alternatingPath {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) : LatticePath d :=
  LatticePath.ofInjectiveFormula (2 * m) (alternatingVertex z i si p sp)
    (alternatingVertex_injective z hip hsi hsp) (by
      intro k _
      rcases alternatingVertex_next z i si p sp k with hk | hk
      · rw [hk.2]
        exact nearestNeighbor_add_signedBasis _ i si hsi
      · rw [hk.2]
        exact nearestNeighbor_sub_signedBasis _ p sp hsp)

namespace LatticePath

lemma mem_vertices_alternatingPath_iff {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) (x : LatticePoint d) :
    x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices ↔
      ∃ k ≤ 2 * m, alternatingVertex z i si p sp k = x := by
  exact mem_vertices_ofInjectiveFormula_iff _ _
    (alternatingVertex_injective z hip hsi hsp) _ x

lemma alternatingPath_private_coordinate_ge_start {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices) :
    si * z i ≤ si * x i := by
  rcases (mem_vertices_alternatingPath_iff
    z i si p sp hip hsi hsp m x).mp hx with ⟨k, -, hkx⟩
  have hcoord := alternatingVertex_private_coordinate z i si p sp hip hsi k
  rw [hkx] at hcoord
  have hnonneg : (0 : ℤ) ≤ (k + 1) / 2 := by positivity
  omega

lemma alternatingPath_reservoir_coordinate_le_start {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices) :
    sp * x p ≤ sp * z p := by
  rcases (mem_vertices_alternatingPath_iff
    z i si p sp hip hsi hsp m x).mp hx with ⟨k, -, hkx⟩
  have hcoord := alternatingVertex_reservoir_coordinate z i si p sp hip hsp k
  rw [hkx] at hcoord
  have hnonneg : (0 : ℤ) ≤ k / 2 := by positivity
  omega

lemma alternatingPath_eq_start_of_private_coordinate_eq {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices)
    (heq : si * x i = si * z i) :
    x = z := by
  rcases (mem_vertices_alternatingPath_iff
    z i si p sp hip hsi hsp m x).mp hx with ⟨k, -, hkx⟩
  have hcoord := alternatingVertex_private_coordinate z i si p sp hip hsi k
  rw [hkx, heq] at hcoord
  have hkzero : k = 0 := by omega
  subst k
  simpa using hkx.symm

lemma alternatingPath_other_coordinate {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices)
    (r : Fin d) (hri : r ≠ i) (hrp : r ≠ p) :
    x r = z r := by
  rcases (mem_vertices_alternatingPath_iff
    z i si p sp hip hsi hsp m x).mp hx with ⟨k, -, rfl⟩
  exact alternatingVertex_apply_of_ne z i si p sp k r hri hrp

@[simp] lemma start_alternatingPath {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) :
    (alternatingPath z i si p sp hip hsi hsp m).start = z := by
  simp [alternatingPath]

@[simp] lemma finish_alternatingPath {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) :
    (alternatingPath z i si p sp hip hsi hsp m).finish =
      z + signedBasis i (m * si) - signedBasis p (m * sp) := by
  simp [alternatingPath, alternatingVertex_even]

lemma alternatingPath_private_coordinate_le_finish {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices) :
    si * x i ≤ si * (alternatingPath z i si p sp hip hsi hsp m).finish i := by
  rcases (mem_vertices_alternatingPath_iff
    z i si p sp hip hsi hsp m x).mp hx with ⟨k, hk, hkx⟩
  have hcoord := alternatingVertex_private_coordinate z i si p sp hip hsi k
  rw [hkx] at hcoord
  rw [finish_alternatingPath]
  have hsq := sq_eq_one_of_natAbs_eq_one si hsi
  simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same, signedBasis_of_ne hip]
  have hhalf : (k + 1) / 2 ≤ m := by omega
  push_cast at hhalf
  nlinarith

lemma alternatingPath_eq_finish_of_private_eq_of_reservoir_le {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d)
    (hx : x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices)
    (hprivate : si * x i =
      si * (alternatingPath z i si p sp hip hsi hsp m).finish i)
    (hreservoir : sp * x p ≤
      sp * (alternatingPath z i si p sp hip hsi hsp m).finish p) :
    x = (alternatingPath z i si p sp hip hsi hsp m).finish := by
  rcases (mem_vertices_alternatingPath_iff
    z i si p sp hip hsi hsp m x).mp hx with ⟨k, hk, hkx⟩
  have hprivateCoord := alternatingVertex_private_coordinate z i si p sp hip hsi k
  have hreservoirCoord := alternatingVertex_reservoir_coordinate z i si p sp hip hsp k
  rw [hkx] at hprivateCoord hreservoirCoord
  have hfinishPrivate :
      si * (alternatingPath z i si p sp hip hsi hsp m).finish i =
        si * z i + m := by
    rw [finish_alternatingPath]
    have hsq := sq_eq_one_of_natAbs_eq_one si hsi
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_same, signedBasis_of_ne hip]
    nlinarith
  have hfinishReservoir :
      sp * (alternatingPath z i si p sp hip hsi hsp m).finish p =
        sp * z p - m := by
    rw [finish_alternatingPath]
    have hsq := sq_eq_one_of_natAbs_eq_one sp hsp
    simp only [Pi.add_apply, Pi.sub_apply, signedBasis_of_ne (Ne.symm hip),
      signedBasis_same, add_zero]
    nlinarith
  have hkfinal : k = 2 * m := by
    rw [hfinishPrivate] at hprivate
    rw [hfinishReservoir] at hreservoir
    omega
  subst k
  rw [← hkx]
  simp [alternatingVertex_even]

@[simp] lemma edgeLength_alternatingPath {d : ℕ} (z : LatticePoint d)
    (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ) :
    (alternatingPath z i si p sp hip hsi hsp m).edgeLength = 2 * m := by
  simp [alternatingPath]

lemma alternatingPath_vertices_on_two_spheres {d n : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (heven : ∀ t ≤ m, l1Norm (alternatingVertex z i si p sp (2 * t)) = n)
    (hodd : ∀ t < m, l1Norm (alternatingVertex z i si p sp (2 * t + 1)) = n + 1) :
    ∀ x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  intro x hx
  rcases (mem_vertices_alternatingPath_iff z i si p sp hip hsi hsp m x).mp hx with
    ⟨k, hk, rfl⟩
  rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · left
    rw [show k = 2 * t by omega]
    exact heven t (by omega)
  · right
    rw [show k = 2 * t + 1 by omega]
    exact hodd t (by omega)

lemma alternatingPath_coordinate_displacement_le {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d) (hx : x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices)
    (r : Fin d) :
    Int.natAbs (x r - z r) ≤ m := by
  rcases (mem_vertices_alternatingPath_iff z i si p sp hip hsi hsp m x).mp hx with
    ⟨k, hk, hkx⟩
  rw [← hkx]
  exact alternatingVertex_coordinate_displacement_le z i si p sp hip hsi hsp m k hk r

lemma alternatingPath_coordinate_lower_bound {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d) (hx : x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices)
    (r : Fin d) :
    z r - m ≤ x r := by
  apply coordinate_sub_le_of_natAbs_sub_le x z r m
  exact alternatingPath_coordinate_displacement_le z i si p sp hip hsi hsp m x hx r

lemma alternatingPath_coordinate_upper_bound {d : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (x : LatticePoint d) (hx : x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices)
    (r : Fin d) :
    x r ≤ z r + m := by
  apply coordinate_le_add_of_natAbs_sub_le x z r m
  exact alternatingPath_coordinate_displacement_le z i si p sp hip hsi hsp m x hx r

lemma alternatingPath_vertices_on_two_spheres_of_signs {d n : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (hz : z ∈ sphere d n)
    (houtward : 0 ≤ si * z i)
    (hreservoir : (m : ℤ) ≤ sp * z p) :
    ∀ x ∈ (alternatingPath z i si p sp hip hsi hsp m).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  have hsiSq := sq_eq_one_of_natAbs_eq_one si hsi
  have hspSq := sq_eq_one_of_natAbs_eq_one sp hsp
  have hnorm : ∀ t : ℕ, t ≤ m →
      l1Norm (alternatingVertex z i si p sp (2 * t)) = n ∧
        (t < m → l1Norm (alternatingVertex z i si p sp (2 * t + 1)) = n + 1) := by
    intro t
    induction t with
    | zero =>
        intro _
        constructor
        · simpa [sphere] using hz
        · intro hm
          rw [alternatingVertex_odd_eq_even_add]
          have hmove := l1Norm_add_signedBasis
            (alternatingVertex z i si p sp 0) i si hsi (by
              simpa using houtward)
          have hzn : l1Norm z = n := hz
          rw [alternatingVertex_zero, hzn] at hmove
          simpa using hmove
    | succ t ih =>
        intro htm
        have htlt : t < m := by omega
        have hprev := ih (by omega)
        have hinward : 1 ≤ sp * (alternatingVertex z i si p sp (2 * t + 1)) p := by
          have htZ : (t : ℤ) < m := by exact_mod_cast htlt
          rw [alternatingVertex_odd]
          simp [signedBasis, Ne.symm hip]
          nlinarith
        have heven :
            l1Norm (alternatingVertex z i si p sp (2 * (t + 1))) = n := by
          rw [alternatingVertex_even_succ_eq_odd_sub]
          have hmove := l1Norm_sub_signedBasis
            (alternatingVertex z i si p sp (2 * t + 1)) p sp hsp hinward
          rw [hprev.2 htlt] at hmove
          omega
        constructor
        · simpa [Nat.succ_eq_add_one] using heven
        · intro hsucc
          rw [alternatingVertex_odd_eq_even_add]
          have hout : 0 ≤ si *
              (alternatingVertex z i si p sp (2 * (t + 1))) i := by
            rw [alternatingVertex_even]
            simp [signedBasis, hip]
            have htNonneg : (0 : ℤ) ≤ (t + 1 : ℕ) := by positivity
            nlinarith
          have hmove := l1Norm_add_signedBasis
            (alternatingVertex z i si p sp (2 * (t + 1))) i si hsi hout
          rw [heven] at hmove
          simpa [Nat.succ_eq_add_one] using hmove
  apply alternatingPath_vertices_on_two_spheres z i si p sp hip hsi hsp m
  · intro t ht
    exact (hnorm t ht).1
  · intro t ht
    exact (hnorm t ht.le).2 ht

lemma finish_alternatingPath_mem_inner_sphere_of_signs {d n : ℕ}
    (z : LatticePoint d) (i : Fin d) (si : ℤ) (p : Fin d) (sp : ℤ)
    (hip : i ≠ p) (hsi : Int.natAbs si = 1)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (hz : z ∈ sphere d n)
    (houtward : 0 ≤ si * z i)
    (hreservoir : (m : ℤ) ≤ sp * z p) :
    (alternatingPath z i si p sp hip hsi hsp m).finish ∈ sphere d n := by
  have hsiSq := sq_eq_one_of_natAbs_eq_one si hsi
  have hspSq := sq_eq_one_of_natAbs_eq_one sp hsp
  have hnorm : ∀ t : ℕ, t ≤ m →
      l1Norm (alternatingVertex z i si p sp (2 * t)) = n ∧
        (t < m → l1Norm (alternatingVertex z i si p sp (2 * t + 1)) = n + 1) := by
    intro t
    induction t with
    | zero =>
        intro _
        constructor
        · simpa [sphere] using hz
        · intro hm
          rw [alternatingVertex_odd_eq_even_add]
          have hmove := l1Norm_add_signedBasis
            (alternatingVertex z i si p sp 0) i si hsi (by
              simpa using houtward)
          have hzn : l1Norm z = n := hz
          rw [alternatingVertex_zero, hzn] at hmove
          simpa using hmove
    | succ t ih =>
        intro htm
        have htlt : t < m := by omega
        have hprev := ih (by omega)
        have hinward : 1 ≤ sp *
            (alternatingVertex z i si p sp (2 * t + 1)) p := by
          have htZ : (t : ℤ) < m := by exact_mod_cast htlt
          rw [alternatingVertex_odd]
          simp [signedBasis, Ne.symm hip]
          nlinarith
        have heven :
            l1Norm (alternatingVertex z i si p sp (2 * (t + 1))) = n := by
          rw [alternatingVertex_even_succ_eq_odd_sub]
          have hmove := l1Norm_sub_signedBasis
            (alternatingVertex z i si p sp (2 * t + 1)) p sp hsp hinward
          rw [hprev.2 htlt] at hmove
          omega
        constructor
        · simpa [Nat.succ_eq_add_one] using heven
        · intro hsucc
          rw [alternatingVertex_odd_eq_even_add]
          have hout : 0 ≤ si *
              (alternatingVertex z i si p sp (2 * (t + 1))) i := by
            rw [alternatingVertex_even]
            simp [signedBasis, hip]
            have htNonneg : (0 : ℤ) ≤ (t + 1 : ℕ) := by positivity
            nlinarith
          have hmove := l1Norm_add_signedBasis
            (alternatingVertex z i si p sp (2 * (t + 1))) i si hsi hout
          rw [heven] at hmove
          simpa [Nat.succ_eq_add_one] using hmove
  have hm := (hnorm m le_rfl).1
  simpa [sphere, finish_alternatingPath, alternatingVertex_even] using hm

end LatticePath

end DisjointPaths
