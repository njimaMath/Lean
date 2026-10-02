import Disjoint_paths.Lemmas.OuterFanLong
import Mathlib.Data.Fintype.Card

/-!
# Counting a long-coordinate outer fan
-/

namespace DisjointPaths

noncomputable section

noncomputable instance longOuterIndexFintype {d : ℕ}
    (y : LatticePoint d) (p : Fin d) (m : ℕ) :
    Fintype (LongOuterIndex y p m) := by
  classical
  exact Fintype.ofFinset
    (Finset.univ.filter fun i : Fin d =>
      i ≠ p ∧ (m : ℤ) ≤ coordinateSign (y i) * y i) (by
        intro i
        change i ∈ Finset.univ.filter (fun i : Fin d =>
            i ≠ p ∧ (m : ℤ) ≤ coordinateSign (y i) * y i) ↔
          i ≠ p ∧ (m : ℤ) ≤ coordinateSign (y i) * y i
        simp)

def SupportExceptIndex {d : ℕ} (y : LatticePoint d) (p : Fin d) :=
  {i : Fin d // y i ≠ 0 ∧ i ≠ p}

noncomputable instance supportExceptIndexFintype {d : ℕ}
    (y : LatticePoint d) (p : Fin d) : Fintype (SupportExceptIndex y p) := by
  classical
  exact Fintype.ofFinset
    (Finset.univ.filter fun i : Fin d => y i ≠ 0 ∧ i ≠ p) (by
      intro i
      change i ∈ Finset.univ.filter (fun i : Fin d => y i ≠ 0 ∧ i ≠ p) ↔
        y i ≠ 0 ∧ i ≠ p
      simp)

def longOuterIndexEquivSupportExcept {d : ℕ}
    (y : LatticePoint d) (p : Fin d) (m : ℕ) (hm : 1 ≤ m)
    (hall : ∀ i, i ≠ p → y i ≠ 0 →
      (m : ℤ) ≤ coordinateSign (y i) * y i) :
    LongOuterIndex y p m ≃ SupportExceptIndex y p where
  toFun q := ⟨q.1, by
    constructor
    · intro hzero
      have hlong := q.2.2
      rw [coordinateSign_mul_self, hzero] at hlong
      norm_num at hlong
      omega
    · exact q.2.1⟩
  invFun q := ⟨q.1, q.2.2, hall q.1 q.2.2 q.2.1⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

lemma card_supportExceptIndex {d : ℕ} (y : LatticePoint d) (p : Fin d)
    (hp : y p ≠ 0) :
    Fintype.card (SupportExceptIndex y p) = supportCard y - 1 := by
  classical
  change Fintype.card {i : Fin d // y i ≠ 0 ∧ i ≠ p} = supportCard y - 1
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter (fun i : Fin d => y i ≠ 0 ∧ i ≠ p) =
        (Finset.univ.filter fun i : Fin d => y i ≠ 0).erase p := by
    ext i
    simp [and_comm]
  rw [hfilter, Finset.card_erase_of_mem]
  · rfl
  · simp [hp]

lemma card_longOuterIndex {d : ℕ}
    (y : LatticePoint d) (p : Fin d) (m : ℕ) (hm : 1 ≤ m)
    (hp : y p ≠ 0)
    (hall : ∀ i, i ≠ p → y i ≠ 0 →
      (m : ℤ) ≤ coordinateSign (y i) * y i) :
    Fintype.card (LongOuterIndex y p m) = supportCard y - 1 := by
  rw [Fintype.card_congr (longOuterIndexEquivSupportExcept y p m hm hall),
    card_supportExceptIndex y p hp]

end

end DisjointPaths
