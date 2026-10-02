import Disjoint_paths.Lemmas.PathConstructor
import Mathlib.Tactic.Linarith

/-!
# Signed coordinate moves and the `ℓ¹` norm

The path constructions move outward in one signed coordinate and inward in a
reservoir coordinate.  These lemmas record the resulting change of norm.
-/

namespace DisjointPaths

lemma sq_eq_one_of_natAbs_eq_one (s : ℤ) (hs : Int.natAbs s = 1) :
    s * s = 1 := by
  rcases Int.natAbs_eq_iff.mp hs with rfl | rfl <;> norm_num

def coordinateSign (a : ℤ) : ℤ := if 0 ≤ a then 1 else -1

@[simp] lemma natAbs_coordinateSign (a : ℤ) :
    Int.natAbs (coordinateSign a) = 1 := by
  by_cases ha : 0 ≤ a <;> simp [coordinateSign, ha]

lemma coordinateSign_mul_self (a : ℤ) :
    coordinateSign a * a = (Int.natAbs a : ℤ) := by
  by_cases ha : 0 ≤ a
  · simp [coordinateSign, ha, Int.ofNat_natAbs_of_nonneg ha]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    have habs : (Int.natAbs a : ℤ) = -a := Int.ofNat_natAbs_of_nonpos ha'
    simp [coordinateSign, ha, habs]

private lemma l1Norm_eq_add_one_of_single_coordinate {d : ℕ}
    (x y : LatticePoint d) (i : Fin d)
    (hsame : ∀ j, j ≠ i → y j = x j)
    (hi : Int.natAbs (y i) = Int.natAbs (x i) + 1) :
    l1Norm y = l1Norm x + 1 := by
  classical
  unfold l1Norm
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hrest :
      ∑ j ∈ Finset.univ.erase i, Int.natAbs (y j) =
        ∑ j ∈ Finset.univ.erase i, Int.natAbs (x j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsame j (Finset.ne_of_mem_erase hj)]
  omega

private lemma l1Norm_add_one_eq_of_single_coordinate {d : ℕ}
    (x y : LatticePoint d) (i : Fin d)
    (hsame : ∀ j, j ≠ i → y j = x j)
    (hi : Int.natAbs (y i) + 1 = Int.natAbs (x i)) :
    l1Norm y + 1 = l1Norm x := by
  classical
  unfold l1Norm
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hrest :
      ∑ j ∈ Finset.univ.erase i, Int.natAbs (y j) =
        ∑ j ∈ Finset.univ.erase i, Int.natAbs (x j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsame j (Finset.ne_of_mem_erase hj)]
  omega

lemma natAbs_add_sign_eq_add_one (a s : ℤ)
    (hs : Int.natAbs s = 1) (ha : 0 ≤ s * a) :
    Int.natAbs (a + s) = Int.natAbs a + 1 := by
  rcases Int.natAbs_eq_iff.mp hs with rfl | rfl
  · have ha0 : 0 ≤ a := by simpa using ha
    change Int.natAbs (a + 1) = Int.natAbs a + 1
    have hleft := Int.ofNat_natAbs_of_nonneg (by omega : 0 ≤ a + 1)
    have hright := Int.ofNat_natAbs_of_nonneg ha0
    omega
  · have ha0 : a ≤ 0 := by simpa using ha
    change Int.natAbs (a - 1) = Int.natAbs a + 1
    have habsLeft : Int.natAbs (a - 1) = Int.natAbs (-a + 1) := by
      rw [show a - 1 = -(-a + 1) by ring, Int.natAbs_neg]
    have habsRight : Int.natAbs a = Int.natAbs (-a) := by simp
    have hleft := Int.ofNat_natAbs_of_nonneg (by omega : 0 ≤ -a + 1)
    have hright := Int.ofNat_natAbs_of_nonneg (by omega : 0 ≤ -a)
    omega

lemma natAbs_sub_sign_add_one_eq (a s : ℤ)
    (hs : Int.natAbs s = 1) (ha : 1 ≤ s * a) :
    Int.natAbs (a - s) + 1 = Int.natAbs a := by
  rcases Int.natAbs_eq_iff.mp hs with rfl | rfl
  · have ha1 : 1 ≤ a := by simpa using ha
    change Int.natAbs (a - 1) + 1 = Int.natAbs a
    have hleft := Int.ofNat_natAbs_of_nonneg (by omega : 0 ≤ a - 1)
    have hright := Int.ofNat_natAbs_of_nonneg (by omega : 0 ≤ a)
    omega
  · have ha1 : a ≤ -1 := by
      norm_num at ha
      omega
    change Int.natAbs (a + 1) + 1 = Int.natAbs a
    have habsLeft : Int.natAbs (a + 1) = Int.natAbs (-a - 1) := by
      rw [show a + 1 = -(-a - 1) by ring, Int.natAbs_neg]
    have habsRight : Int.natAbs a = Int.natAbs (-a) := by simp
    have hleft := Int.ofNat_natAbs_of_nonneg (by omega : 0 ≤ -a - 1)
    have hright := Int.ofNat_natAbs_of_nonneg (by omega : 0 ≤ -a)
    omega

lemma l1Norm_add_signedBasis {d : ℕ} (x : LatticePoint d)
    (i : Fin d) (s : ℤ) (hs : Int.natAbs s = 1)
    (houtward : 0 ≤ s * x i) :
    l1Norm (x + signedBasis i s) = l1Norm x + 1 := by
  apply l1Norm_eq_add_one_of_single_coordinate x _ i
  · intro j hji
    simp [signedBasis, hji]
  · simp [signedBasis, natAbs_add_sign_eq_add_one (x i) s hs houtward]

lemma l1Norm_sub_signedBasis {d : ℕ} (x : LatticePoint d)
    (i : Fin d) (s : ℤ) (hs : Int.natAbs s = 1)
    (hinward : 1 ≤ s * x i) :
    l1Norm (x - signedBasis i s) + 1 = l1Norm x := by
  apply l1Norm_add_one_eq_of_single_coordinate x _ i
  · intro j hji
    simp [signedBasis, hji]
  · simp [signedBasis, natAbs_sub_sign_add_one_eq (x i) s hs hinward]

end DisjointPaths
