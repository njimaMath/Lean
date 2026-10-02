import Disjoint_paths.Lemmas.OuterPrivateFan
import Disjoint_paths.Lemmas.Fan

/-!
# Cross-family geometry for the long neighboring branch
-/

namespace DisjointPaths

noncomputable section

open LatticePath

lemma two_coordinate_natAbs_le_l1Dist {d : ℕ}
    (a b : LatticePoint d) (i j : Fin d) (hij : i ≠ j) :
    Int.natAbs (a i - b i) + Int.natAbs (a j - b j) ≤ l1Dist a b := by
  unfold l1Dist l1Norm
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  apply Nat.add_le_add_left
  exact Finset.single_le_sum
    (fun k _ => Nat.zero_le (Int.natAbs (a k - b k)))
    (by simp [hij.symm])

lemma innerFanPath_edgeDisjoint_outerPrivatePath_neighbor
    {d : ℕ} (z y : LatticePoint d) (r : Fin d) (sr : ℤ)
    (hsr : Int.natAbs sr = 1) (m : ℕ)
    (q : InnerFanIndex z r) (u h : Fin d)
    (hyu : y u ≠ 0) (huh : u ≠ h) (hur : u ≠ r) (hhr : h ≠ r)
    (hrsign : coordinateSign (y r) = sr)
    (hrstep : sr * y r = sr * z r + 1)
    (hother : ∀ k, k ≠ r → y k = z k) :
    Disjoint (innerFanPath z r sr hsr m q).edgeSet
      (outerPrivatePath y u h r m hyu huh hur hhr).edgeSet := by
  apply edgeDisjoint_of_vertices_disjoint
  rw [Set.disjoint_left]
  intro x hxi hxo
  have hiR : sr * x r ≤ sr * z r := by
    exact alternatingPath_reservoir_coordinate_le_start
      z q.1.1 (boolSign q.1.2) r sr q.2.2
      (natAbs_boolSign _) hsr m x (by simpa [innerFanPath] using hxi)
  unfold outerPrivatePath at hxo
  dsimp at hxo
  split_ifs at hxo with hlong
  · have hoR := inwardAlternatingPath_reservoir_coordinate_ge_start
      y u (coordinateSign (y u)) r (coordinateSign (y r)) hur
      (natAbs_coordinateSign _) (natAbs_coordinateSign _) m x hxo
    rw [hrsign] at hoR
    omega
  · let a := Int.natAbs (y u)
    let b := m - a
    let first := shortOuterFirst y u (coordinateSign (y u)) h
      (coordinateSign (y h)) huh (natAbs_coordinateSign _)
      (natAbs_coordinateSign _) a
    let second := shortOuterSecond y u (coordinateSign (y u)) h
      (coordinateSign (y h)) r (coordinateSign (y r)) huh hur hhr
      (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (natAbs_coordinateSign _) a b
    change x ∈ first.vertices ++ second.vertices.tail at hxo
    rcases List.mem_append.mp hxo with hxfirst | hxsecond
    · have hxcoord := inwardAlternatingPath_other_coordinate
        y u (coordinateSign (y u)) h (coordinateSign (y h)) huh
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) a x
        (by simpa [first, shortOuterFirst] using hxfirst) r
        (Ne.symm hur) (Ne.symm hhr)
      rw [hxcoord] at hiR
      omega

    · have hxsecond' : x ∈ second.vertices := List.mem_of_mem_tail hxsecond
      have hsecondU := inwardAlternatingPath_reservoir_coordinate_ge_start
        (shortOuterFirst y u (coordinateSign (y u)) h
          (coordinateSign (y h)) huh (natAbs_coordinateSign _)
          (natAbs_coordinateSign _) a).finish
        r (coordinateSign (y r)) u (-coordinateSign (y u))
        (Ne.symm hur) (natAbs_coordinateSign _)
        (by simpa using natAbs_coordinateSign (y u)) b x
        (by simpa [second, shortOuterSecond] using hxsecond')
      have hfirstZero : coordinateSign (y u) *
          (shortOuterFirst y u (coordinateSign (y u)) h
            (coordinateSign (y h)) huh (natAbs_coordinateSign _)
            (natAbs_coordinateSign _) a).finish u = 0 := by
        apply shortOuterFirst_finish_private_zero
        dsimp [a]
        exact coordinateSign_mul_self _
      have houterU : coordinateSign (y u) * x u ≤ 0 := by
        rw [neg_mul] at hsecondU
        nlinarith
      have hyuPositive : 1 ≤ coordinateSign (y u) * y u := by
        rw [coordinateSign_mul_self]
        exact_mod_cast Int.natAbs_pos.mpr hyu
      have hinnerU : coordinateSign (y u) * y u ≤
          coordinateSign (y u) * x u := by
        by_cases hqu : q.1.1 = u
        · have hzu : z u ≠ 0 := by simpa [hother u hur] using hyu
          have hsign : boolSign q.1.2 = coordinateSign (z u) := by
            apply boolSign_eq_coordinateSign_of_outward z u q.1.2 hzu
            simpa [IsOutwardDirection, hqu] using q.2.1
          have hprivate := alternatingPath_private_coordinate_ge_start
            z q.1.1 (boolSign q.1.2) r sr q.2.2
            (natAbs_boolSign _) hsr m x (by simpa [innerFanPath] using hxi)
          rw [hqu, hsign, ← hother u hur] at hprivate
          exact hprivate
        · have hxcoord := alternatingPath_other_coordinate
            z q.1.1 (boolSign q.1.2) r sr q.2.2
            (natAbs_boolSign _) hsr m x (by simpa [innerFanPath] using hxi)
            u (Ne.symm hqu) hur
          rw [hxcoord, hother u hur]
      omega

lemma outerPrivatePath_endpoint_far_innerFanPath_neighbor
    {d : ℕ} (z y : LatticePoint d) (r : Fin d) (sr : ℤ)
    (hsr : Int.natAbs sr = 1) (m : ℕ)
    (q : InnerFanIndex z r) (u h : Fin d)
    (hyu : y u ≠ 0) (huh : u ≠ h) (hur : u ≠ r) (hhr : h ≠ r)
    (hother : ∀ k, k ≠ r → y k = z k)
    (rsep : ℝ) (hrsep : rsep ≤ (m : ℝ)) :
    ∀ x ∈ (innerFanPath z r sr hsr m q).vertices,
      rsep ≤ (l1Dist
        (outerPrivatePath y u h r m hyu huh hur hhr).finish x : ℝ) := by
  let su := coordinateSign (y u)
  have hsu : Int.natAbs (-su) = 1 := by
    simp [su, natAbs_coordinateSign]
  apply endpoint_far_from_vertices_of_signed_coordinate_gap
    (outerPrivatePath y u h r m hyu huh hur hhr)
    (innerFanPath z r sr hsr m q) u (-su) hsu rsep
    (-(su * y u)) m hrsep (by positivity)
  · have hfinish := outerPrivatePath_finish_private_coordinate
      y u h r m hyu huh hur hhr
    have hself := coordinateSign_mul_self (y u)
    dsimp [su] at hfinish hself ⊢
    push_cast
    nlinarith
  · intro x hx
    have hinner : su * y u ≤ su * x u := by
      by_cases hqu : q.1.1 = u
      · have hzu : z u ≠ 0 := by simpa [hother u hur] using hyu
        have hsign : boolSign q.1.2 = coordinateSign (z u) := by
          apply boolSign_eq_coordinateSign_of_outward z u q.1.2 hzu
          simpa [IsOutwardDirection, hqu] using q.2.1
        have hprivate := alternatingPath_private_coordinate_ge_start
          z q.1.1 (boolSign q.1.2) r sr q.2.2
          (natAbs_boolSign _) hsr m x (by simpa [innerFanPath] using hx)
        dsimp [su]
        rw [hqu, hsign, ← hother u hur] at hprivate
        exact hprivate
      · have hxcoord := alternatingPath_other_coordinate
          z q.1.1 (boolSign q.1.2) r sr q.2.2
          (natAbs_boolSign _) hsr m x (by simpa [innerFanPath] using hx)
          u (Ne.symm hqu) hur
        dsimp [su]
        rw [hxcoord, hother u hur]
    dsimp [su] at hinner ⊢
    nlinarith

lemma innerFanPath_endpoint_far_outerPrivatePath_neighbor
    {d : ℕ} (z y : LatticePoint d) (r : Fin d) (sr : ℤ)
    (hsr : Int.natAbs sr = 1) (m : ℕ)
    (q : InnerFanIndex z r) (u h : Fin d)
    (hyu : y u ≠ 0) (huh : u ≠ h) (hur : u ≠ r) (hhr : h ≠ r)
    (hrsign : coordinateSign (y r) = sr)
    (hrstep : sr * y r = sr * z r + 1)
    (hother : ∀ k, k ≠ r → y k = z k)
    (rsep : ℝ) (hrsep : rsep ≤ (m : ℝ)) :
    ∀ x ∈ (outerPrivatePath y u h r m hyu huh hur hhr).vertices,
      rsep ≤ (l1Dist (innerFanPath z r sr hsr m q).finish x : ℝ) := by
  let su := coordinateSign (y u)
  have hsu : Int.natAbs su = 1 := natAbs_coordinateSign _
  have hfinishR : sr * (innerFanPath z r sr hsr m q).finish r =
      sr * z r - m := by
    simp only [innerFanPath, LatticePath.finish_alternatingPath,
      Pi.add_apply, Pi.sub_apply, signedBasis_of_ne (Ne.symm q.2.2),
      signedBasis_same, add_zero, zero_add]
    have hsrsq := sq_eq_one_of_natAbs_eq_one sr hsr
    push_cast
    nlinarith
  unfold outerPrivatePath
  dsimp
  split_ifs with hlong
  · intro x hx
    apply endpoint_far_from_vertices_of_signed_coordinate_gap
      (innerFanPath z r sr hsr m q)
      (inwardAlternatingPath y u (coordinateSign (y u)) r
        (coordinateSign (y r)) hur (natAbs_coordinateSign _)
        (natAbs_coordinateSign _) m)
      r (-sr) (by simpa using hsr) rsep (-sr * z r) m hrsep
      (by positivity)
    · nlinarith [hfinishR]
    · intro w hw
      have hge := inwardAlternatingPath_reservoir_coordinate_ge_start
        y u (coordinateSign (y u)) r (coordinateSign (y r)) hur
        (natAbs_coordinateSign _) (natAbs_coordinateSign _) m w hw
      rw [hrsign] at hge
      nlinarith
    · exact hx
  · intro x hx
    let a := Int.natAbs (y u)
    let b := m - a
    have ham : a ≤ m := by
      dsimp [a]
      omega
    have hab : a + b = m := by
      dsimp [b]
      omega
    let first := shortOuterFirst y u (coordinateSign (y u)) h
      (coordinateSign (y h)) huh (natAbs_coordinateSign _)
      (natAbs_coordinateSign _) a
    let second := shortOuterSecond y u (coordinateSign (y u)) h
      (coordinateSign (y h)) r (coordinateSign (y r)) huh hur hhr
      (natAbs_coordinateSign _) (natAbs_coordinateSign _)
      (natAbs_coordinateSign _) a b
    change x ∈ first.vertices ++ second.vertices.tail at hx
    rcases List.mem_append.mp hx with hxfirst | hxsecond
    · apply endpoint_far_from_vertices_of_signed_coordinate_gap
        (innerFanPath z r sr hsr m q) first r (-sr)
        (by simpa using hsr) rsep (-sr * z r) m hrsep (by positivity)
      · nlinarith [hfinishR]
      · intro w hw
        have hwR := inwardAlternatingPath_other_coordinate
          y u (coordinateSign (y u)) h (coordinateSign (y h)) huh
          (natAbs_coordinateSign _) (natAbs_coordinateSign _) a w
          (by simpa [first, shortOuterFirst] using hw) r
          (Ne.symm hur) (Ne.symm hhr)
        rw [hwR]
        nlinarith [hrstep]
      · exact hxfirst
    · have hxsecond' : x ∈ second.vertices := List.mem_of_mem_tail hxsecond
      have hfirstR : first.finish r = y r := by
        exact inwardAlternatingPath_other_coordinate
          y u (coordinateSign (y u)) h (coordinateSign (y h)) huh
          (natAbs_coordinateSign _) (natAbs_coordinateSign _) a first.finish
          (finish_mem_vertices _) r (Ne.symm hur) (Ne.symm hhr)
      have hfirstZero : su * first.finish u = 0 := by
        apply shortOuterFirst_finish_private_zero
        dsimp [a, su]
        exact coordinateSign_mul_self _
      rcases (mem_vertices_alternatingPath_iff
          first.finish r (-coordinateSign (y r)) u (coordinateSign (y u))
          (Ne.symm hur) (by simpa using natAbs_coordinateSign (y r))
          (natAbs_coordinateSign (y u)) b x).mp (by
            simpa [second, shortOuterSecond, inwardAlternatingPath] using hxsecond') with
        ⟨k, hk, hkx⟩
      have hkR := inwardAlternatingVertex_private_coordinate
        first.finish r (coordinateSign (y r)) u (-coordinateSign (y u))
        (Ne.symm hur) (natAbs_coordinateSign _) k
      have hkU := inwardAlternatingVertex_reservoir_coordinate
        first.finish r (coordinateSign (y r)) u (-coordinateSign (y u))
        (Ne.symm hur) (by simpa using natAbs_coordinateSign (y u)) k
      simp only [neg_neg] at hkR hkU
      rw [hkx, hfirstR, hrsign] at hkR
      rw [hkx] at hkU
      have hkU' : su * x u = -((k / 2 : ℕ) : ℤ) := by
        dsimp [su] at hfirstZero hkU ⊢
        push_cast at hkU ⊢
        nlinarith
      have hkr : (k + 1) / 2 ≤ b := by omega
      have hku : k / 2 ≤ b := by omega
      have hzu : su * z u = (a : ℤ) := by
        dsimp [a, su]
        rw [← hother u hur, coordinateSign_mul_self]
      have hinnerU : (a : ℤ) ≤
          su * (innerFanPath z r sr hsr m q).finish u := by
        by_cases hqu : q.1.1 = u
        · have hzuNonzero : z u ≠ 0 := by simpa [← hother u hur] using hyu
          have hsign : boolSign q.1.2 = coordinateSign (z u) := by
            apply boolSign_eq_coordinateSign_of_outward z u q.1.2 hzuNonzero
            simpa [IsOutwardDirection, hqu] using q.2.1
          have hprivate := alternatingPath_private_coordinate_ge_start
            z q.1.1 (boolSign q.1.2) r sr q.2.2
            (natAbs_boolSign _) hsr m
            (innerFanPath z r sr hsr m q).finish (finish_mem_vertices _)
          dsimp [su]
          rw [hqu, hsign, ← hother u hur] at hprivate
          dsimp [su] at hzu ⊢
          rw [← hother u hur] at hzu
          exact hzu.symm.le.trans hprivate
        · have hcoord := alternatingPath_other_coordinate
            z q.1.1 (boolSign q.1.2) r sr q.2.2
            (natAbs_boolSign _) hsr m
            (innerFanPath z r sr hsr m q).finish (finish_mem_vertices _)
            u (Ne.symm hqu) hur
          rw [hcoord]
          exact hzu.symm.le
      have hAbsR : (m + 1 - (k + 1) / 2 : ℕ) ≤ Int.natAbs
          ((innerFanPath z r sr hsr m q).finish r - x r) := by
        let v := (innerFanPath z r sr hsr m q).finish r
        have hgap : (m : ℤ) + 1 - ((k + 1) / 2 : ℕ) ≤ sr * (x r - v) := by
          dsimp [v]
          rw [mul_sub, hfinishR]
          push_cast at hkR ⊢
          omega
        have hcast : ((m + 1 - (k + 1) / 2 : ℕ) : ℤ) =
            (m : ℤ) + 1 - ((k + 1) / 2 : ℕ) := by
          omega
        rcases Int.natAbs_eq_iff.mp hsr with hsr1 | hsr1
        · have hgap' := hgap
          rw [hsr1] at hgap'
          norm_num at hgap'
          have hxv : 0 ≤ x r - v := by omega
          have habs : (Int.natAbs (v - x r) : ℤ) = x r - v := by
            rw [show v - x r = -(x r - v) by ring, Int.natAbs_neg]
            exact Int.natAbs_of_nonneg hxv
          have hgapCast : ((m + 1 - (k + 1) / 2 : ℕ) : ℤ) ≤
              (Int.natAbs (v - x r) : ℤ) := by
            rw [hcast, habs]
            omega
          exact_mod_cast hgapCast
        · have hgap' := hgap
          rw [hsr1] at hgap'
          norm_num at hgap'
          have hvx : 0 ≤ v - x r := by omega
          have habs : (Int.natAbs (v - x r) : ℤ) = v - x r :=
            Int.natAbs_of_nonneg hvx
          have hgapCast : ((m + 1 - (k + 1) / 2 : ℕ) : ℤ) ≤
              (Int.natAbs (v - x r) : ℤ) := by
            rw [hcast, habs]
            omega
          exact_mod_cast hgapCast
      have hAbsU : a + k / 2 ≤ Int.natAbs
          ((innerFanPath z r sr hsr m q).finish u - x u) := by
        let v := (innerFanPath z r sr hsr m q).finish u
        have hgap : ((a + k / 2 : ℕ) : ℤ) ≤ su * (v - x u) := by
          dsimp [v]
          rw [mul_sub]
          push_cast at hkU' ⊢
          omega
        rcases Int.natAbs_eq_iff.mp hsu with hsu1 | hsu1
        · have hgap' := hgap
          rw [hsu1] at hgap'
          norm_num at hgap'
          have hvx : 0 ≤ v - x u := by omega
          have habs : (Int.natAbs (v - x u) : ℤ) = v - x u :=
            Int.natAbs_of_nonneg hvx
          have hgapCast : ((a + k / 2 : ℕ) : ℤ) ≤
              (Int.natAbs (v - x u) : ℤ) := by
            rw [habs]
            exact hgap'
          exact_mod_cast hgapCast
        · have hgap' := hgap
          rw [hsu1] at hgap'
          norm_num at hgap'
          have hxv : 0 ≤ x u - v := by omega
          have habs : (Int.natAbs (v - x u) : ℤ) = x u - v := by
            rw [show v - x u = -(x u - v) by ring, Int.natAbs_neg]
            exact Int.natAbs_of_nonneg hxv
          have hgapCast : ((a + k / 2 : ℕ) : ℤ) ≤
              (Int.natAbs (v - x u) : ℤ) := by
            rw [habs]
            exact hgap'
          exact_mod_cast hgapCast
      have hsum : m ≤ Int.natAbs
          ((innerFanPath z r sr hsr m q).finish r - x r) +
          Int.natAbs ((innerFanPath z r sr hsr m q).finish u - x u) := by
        have ha : 0 < a := Int.natAbs_pos.mpr hyu
        have harith : m ≤ (m + 1 - (k + 1) / 2) + (a + k / 2) := by
          omega
        exact harith.trans (Nat.add_le_add hAbsR hAbsU)
      have hdist := two_coordinate_natAbs_le_l1Dist
        (innerFanPath z r sr hsr m q).finish x r u hur.symm
      have hmDist : m ≤ l1Dist (innerFanPath z r sr hsr m q).finish x :=
        hsum.trans hdist
      exact hrsep.trans (by exact_mod_cast hmDist)

end

end DisjointPaths
