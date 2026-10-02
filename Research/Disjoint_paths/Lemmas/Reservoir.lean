import Disjoint_paths.Lemmas.FanCount
import Disjoint_paths.Lemmas.Scale
import Mathlib.Data.Finset.Max

/-!
# A large reservoir coordinate

On an `ℓ¹` sphere, a maximal coordinate has absolute value at least the
average.  Its coordinate sign supplies the inward direction used by a fan.
-/

namespace DisjointPaths

lemma exists_third_coordinate {d : ℕ} (hd : 3 ≤ d)
    (i p : Fin d) (hip : i ≠ p) :
    ∃ h : Fin d, h ≠ i ∧ h ≠ p := by
  classical
  let s : Finset (Fin d) := (Finset.univ.erase i).erase p
  have hcard : s.card = d - 2 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hip]),
      Finset.card_erase_of_mem (by simp)]
    simp
    omega
  have hnonempty : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hzero
    have : s.card = 0 := by simp [hzero]
    rw [hcard] at this
    omega
  rcases hnonempty with ⟨h, hh⟩
  refine ⟨h, ?_, ?_⟩
  · intro hhi
    subst h
    simp [s] at hh
  · intro hhp
    subst h
    simp [s] at hh

noncomputable def thirdCoordinate {d : ℕ} (hd : 3 ≤ d)
    (i p : Fin d) (hip : i ≠ p) : Fin d :=
  Classical.choose (exists_third_coordinate hd i p hip)

lemma thirdCoordinate_ne_left {d : ℕ} (hd : 3 ≤ d)
    (i p : Fin d) (hip : i ≠ p) :
    thirdCoordinate hd i p hip ≠ i :=
  (Classical.choose_spec (exists_third_coordinate hd i p hip)).1

lemma thirdCoordinate_ne_right {d : ℕ} (hd : 3 ≤ d)
    (i p : Fin d) (hip : i ≠ p) :
    thirdCoordinate hd i p hip ≠ p :=
  (Classical.choose_spec (exists_third_coordinate hd i p hip)).2

lemma exists_coordinate_with_norm_le_mul_natAbs {d n : ℕ}
    (hd : 1 ≤ d) (z : LatticePoint d) (hz : z ∈ sphere d n) :
    ∃ p : Fin d, n ≤ d * Int.natAbs (z p) := by
  classical
  have huniv : (Finset.univ : Finset (Fin d)).Nonempty := by
    exact ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun i => Int.natAbs (z i)) huniv
  refine ⟨p, ?_⟩
  have hsum := Finset.sum_le_card_nsmul Finset.univ
    (fun i => Int.natAbs (z i)) (Int.natAbs (z p)) (by
      intro i _
      exact hp i (Finset.mem_univ i))
  have hznorm : l1Norm z = n := hz
  unfold l1Norm at hznorm
  rw [hznorm] at hsum
  simpa [nsmul_eq_mul] using hsum

lemma exists_reservoir_coordinate {d n m : ℕ} (hd : 1 ≤ d)
    (z : LatticePoint d) (hz : z ∈ sphere d n)
    (hm : d * m ≤ n) :
    ∃ p : Fin d,
      (m : ℤ) ≤ coordinateSign (z p) * z p := by
  obtain ⟨p, hp⟩ := exists_coordinate_with_norm_le_mul_natAbs hd z hz
  refine ⟨p, ?_⟩
  rw [coordinateSign_mul_self]
  have hmabs : m ≤ Int.natAbs (z p) := by
    have hdpos : 0 < d := Nat.zero_lt_of_lt hd
    exact Nat.le_of_mul_le_mul_left (hm.trans hp) hdpos
  exact_mod_cast hmabs

end DisjointPaths
