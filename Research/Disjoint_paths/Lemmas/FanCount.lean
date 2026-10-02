import Disjoint_paths.Lemmas.Fan
import Mathlib.Data.Fintype.Sum

/-!
# Counting fan directions

The cardinality calculation is separated from the geometric fan properties.
For each non-reservoir coordinate there is one outward sign, with one extra
choice exactly when that coordinate is zero.
-/

namespace DisjointPaths

noncomputable section

def OutwardSigns {d : ℕ} (z : LatticePoint d) (i : Fin d) :=
  {b : Bool // 0 ≤ boolSign b * z i}

noncomputable instance outwardSignsFintype {d : ℕ}
    (z : LatticePoint d) (i : Fin d) : Fintype (OutwardSigns z i) := by
  classical
  exact Fintype.ofFinset
    (Finset.univ.filter fun b : Bool => 0 ≤ boolSign b * z i) (by
    intro b
    change b ∈ Finset.univ.filter (fun b : Bool => 0 ≤ boolSign b * z i) ↔
      0 ≤ boolSign b * z i
    simp)

noncomputable instance innerFanIndexFintype {d : ℕ}
    (z : LatticePoint d) (p : Fin d) : Fintype (InnerFanIndex z p) := by
  classical
  exact Fintype.ofFinset
    (Finset.univ.filter fun q : Fin d × Bool => IsOutwardDirection z q ∧ q.1 ≠ p) (by
      intro q
      change q ∈ Finset.univ.filter
          (fun q : Fin d × Bool => IsOutwardDirection z q ∧ q.1 ≠ p) ↔
        IsOutwardDirection z q ∧ q.1 ≠ p
      simp)

def innerFanIndexEquivSigma {d : ℕ} (z : LatticePoint d) (p : Fin d) :
    InnerFanIndex z p ≃ Σ i : {i : Fin d // i ≠ p}, OutwardSigns z i where
  toFun q := ⟨⟨q.1.1, q.2.2⟩, ⟨q.1.2, q.2.1⟩⟩
  invFun q := ⟨(q.1.1, q.2.1), q.2.2, q.1.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q with | mk i b => cases i; cases b; rfl

lemma card_outwardSigns {d : ℕ} (z : LatticePoint d) (i : Fin d) :
    Fintype.card (OutwardSigns z i) = if z i = 0 then 2 else 1 := by
  classical
  change Fintype.card {b : Bool // 0 ≤ boolSign b * z i} =
    if z i = 0 then 2 else 1
  rw [Fintype.card_subtype]
  by_cases hz : z i = 0
  · simp [boolSign, hz]
  · rcases lt_or_gt_of_ne hz with hneg | hpos
    · have hfilter :
          Finset.univ.filter (fun b : Bool => 0 ≤ boolSign b * z i) = {false} := by
        ext b
        cases b <;> simp [boolSign] <;> omega
      rw [hfilter]
      simp [hz]
    · have hfilter :
          Finset.univ.filter (fun b : Bool => 0 ≤ boolSign b * z i) = {true} := by
        ext b
        cases b <;> simp [boolSign] <;> omega
      rw [hfilter]
      simp [hz]

lemma card_innerFanIndex_as_sum {d : ℕ} (z : LatticePoint d) (p : Fin d) :
    Fintype.card (InnerFanIndex z p) =
      ∑ i : {i : Fin d // i ≠ p}, if z i.1 = 0 then 2 else 1 := by
  rw [Fintype.card_congr (innerFanIndexEquivSigma z p), Fintype.card_sigma]
  simp_rw [card_outwardSigns]

lemma sum_outward_sign_counts {d : ℕ} (z : LatticePoint d) :
    (∑ i : Fin d, if z i = 0 then 2 else 1) =
      d + (Finset.univ.filter fun i => z i = 0).card := by
  classical
  have hindicator :
      (∑ i : Fin d, if z i = 0 then 1 else 0) =
        (Finset.univ.filter fun i => z i = 0).card := by
    calc
      (∑ i : Fin d, if z i = 0 then 1 else 0) =
          ∑ i ∈ Finset.univ.filter (fun i => z i = 0), 1 := by
            rw [Finset.sum_filter]
      _ = (Finset.univ.filter fun i => z i = 0).card := by simp
  calc
    (∑ i : Fin d, if z i = 0 then 2 else 1) =
        ∑ i : Fin d, (1 + if z i = 0 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          split <;> simp_all
    _ = d + (Finset.univ.filter fun i => z i = 0).card := by
      rw [Finset.sum_add_distrib]
      simpa using congrArg (fun k => d + k) hindicator

lemma supportCard_add_zeroCard {d : ℕ} (z : LatticePoint d) :
    supportCard z + (Finset.univ.filter fun i => z i = 0).card = d := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : Fin d => z i ≠ 0)
  simpa [supportCard] using h

lemma card_innerFanIndex {d : ℕ} (z : LatticePoint d) (p : Fin d)
    (hp : z p ≠ 0) :
    Fintype.card (InnerFanIndex z p) = 2 * d - supportCard z - 1 := by
  rw [card_innerFanIndex_as_sum]
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne
    (fun i : Fin d => if z i = 0 then 2 else 1) p
  have htotal := sum_outward_sign_counts z
  have hzero := supportCard_add_zeroCard z
  simp [hp] at hsplit
  rw [htotal] at hsplit
  have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by
    intro hd0
    exact Fin.elim0 (hd0 ▸ p))
  have hsum :
      (∑ i : {i : Fin d // i ≠ p}, if z i.1 = 0 then 2 else 1) + 1 =
        d + (Finset.univ.filter fun i => z i = 0).card := by
    simpa [add_comm] using hsplit.symm
  have htotalFormula :
      2 * d - supportCard z =
        d + (Finset.univ.filter fun i => z i = 0).card := by omega
  rw [htotalFormula]
  omega

end

end DisjointPaths
