import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

open scoped BigOperators
open Finset

namespace ChemicalLDP
namespace Lemma54

/--
`proj i` is the coordinate projection that forgets the `i`-th coordinate.

We formulate Lemma 5.4 for tuples indexed by `Fin (n + 3)`, which is equivalent to the usual
statement under the assumption `d ≥ 3`.
-/
def proj {n : ℕ} (i : Fin (n + 3)) (x : Fin (n + 3) → ℤ) : Fin (n + 2) → ℤ :=
  i.removeNth x

lemma coord_eq_of_proj_eq {n : ℕ} {i : Fin (n + 3)} {x y : Fin (n + 3) → ℤ}
    (h : proj i x = proj i y) {j : Fin (n + 3)} (hj : j ≠ i) : x j = y j := by
  rcases Fin.exists_succAbove_eq hj with ⟨k, rfl⟩
  simpa [proj] using congrFun h k

theorem exists_large_projection_strong {n : ℕ} (s : Finset (Fin (n + 3) → ℤ)) :
    ∃ i : Fin (n + 3), ((s.image (proj i)).card : ℝ) ≥ (s.card : ℝ) ^ (2 / 3 : ℝ) := by
  let p0 : Finset (Fin (n + 2) → ℤ) := s.image (proj (0 : Fin (n + 3)))
  let p1 : Finset (Fin (n + 2) → ℤ) := s.image (proj (1 : Fin (n + 3)))
  let p2 : Finset (Fin (n + 2) → ℤ) := s.image (proj (2 : Fin (n + 3)))
  let fiber0 : (Fin (n + 2) → ℤ) → Finset (Fin (n + 3) → ℤ) :=
    fun z => s.filter fun x => proj (0 : Fin (n + 3)) x = z
  let q : Finset ((Fin (n + 3) → ℤ) × (Fin (n + 3) → ℤ)) :=
    (s ×ˢ s).filter fun xy => proj (0 : Fin (n + 3)) xy.1 = proj (0 : Fin (n + 3)) xy.2

  have hs_card : s.card = ∑ z ∈ p0, (fiber0 z).card := by
    dsimp [p0, fiber0]
    simpa [proj] using
      (Finset.card_eq_sum_card_fiberwise
        (f := proj (0 : Fin (n + 3)))
        (s := s)
        (t := s.image (proj (0 : Fin (n + 3))))
        (fun x hx => Finset.mem_image_of_mem _ hx))

  have hs_cardR : (s.card : ℝ) = ∑ z ∈ p0, ((fiber0 z).card : ℝ) := by
    exact_mod_cast hs_card

  have hs_sq :
      (s.card : ℝ) ^ 2 ≤ (p0.card : ℝ) * ∑ z ∈ p0, (((fiber0 z).card : ℝ) ^ 2) := by
    calc
      (s.card : ℝ) ^ 2 = (∑ z ∈ p0, ((fiber0 z).card : ℝ)) ^ 2 := by rw [hs_cardR]
      _ ≤ (p0.card : ℝ) * ∑ z ∈ p0, (((fiber0 z).card : ℝ) ^ 2) := by
        simpa using
          (sq_sum_le_card_mul_sum_sq (s := p0) (f := fun z => ((fiber0 z).card : ℝ)))

  have hq_sum : q.card = ∑ z ∈ p0, (fiber0 z).card ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun xy => proj (0 : Fin (n + 3)) xy.1)
      (s := q)
      (t := p0)]
    · refine Finset.sum_congr rfl ?_
      intro z hz
      have hset :
          {xy ∈ q | proj (0 : Fin (n + 3)) xy.1 = z} = (fiber0 z) ×ˢ (fiber0 z) := by
        ext xy
        constructor
        · intro h
          simp [q, fiber0] at h ⊢
          aesop
        · intro h
          simp [q, fiber0] at h ⊢
          aesop
      calc
        #{xy ∈ q | proj (0 : Fin (n + 3)) xy.1 = z}
            = #((fiber0 z) ×ˢ (fiber0 z)) := by rw [hset]
        _ = (fiber0 z).card * (fiber0 z).card := by rw [Finset.card_product]
        _ = (fiber0 z).card ^ 2 := by rw [sq]
    · intro xy hxy
      simp [q, p0] at hxy ⊢
      exact ⟨xy.1, hxy.1.1, rfl⟩

  have hq_card :
      q.card ≤ p2.card * p1.card := by
    calc
      q.card ≤ #((p2 ×ˢ p1)) := by
        refine Finset.card_le_card_of_injOn
          (fun xy => (proj (2 : Fin (n + 3)) xy.1, proj (1 : Fin (n + 3)) xy.2)) ?_ ?_
        · intro xy hxy
          simp [q, p1, p2] at hxy ⊢
          exact ⟨⟨xy.1, hxy.1.1, rfl⟩, ⟨xy.2, hxy.1.2, rfl⟩⟩
        · intro xy hxy zw hzw hEq
          simp [q] at hxy hzw
          rcases Prod.mk.inj hEq with ⟨h2, h1⟩
          have hlt1 : 1 < n + 3 := by omega
          have hlt2 : 2 < n + 3 := by omega
          have h20 : (2 : Fin (n + 3)) ≠ (0 : Fin (n + 3)) := by
            intro h
            have hval := congrArg Fin.val h
            simp [Nat.mod_eq_of_lt hlt2] at hval
          have h21 : (2 : Fin (n + 3)) ≠ (1 : Fin (n + 3)) := by
            intro h
            have hval := congrArg Fin.val h
            simp [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hval
          have h10 : (1 : Fin (n + 3)) ≠ (0 : Fin (n + 3)) := by
            intro h
            have hval := congrArg Fin.val h
            simp [Nat.mod_eq_of_lt hlt1] at hval
          have h12 : (1 : Fin (n + 3)) ≠ (2 : Fin (n + 3)) := by
            intro h
            have hval := congrArg Fin.val h
            simp [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hval
          have hx2 : xy.1 (2 : Fin (n + 3)) = zw.1 (2 : Fin (n + 3)) := by
            calc
              xy.1 (2 : Fin (n + 3)) = xy.2 (2 : Fin (n + 3)) := by
                exact coord_eq_of_proj_eq hxy.2 h20
              _ = zw.2 (2 : Fin (n + 3)) := by
                exact coord_eq_of_proj_eq h1 h21
              _ = zw.1 (2 : Fin (n + 3)) := by
                symm
                exact coord_eq_of_proj_eq hzw.2 h20
          have hy1 : xy.2 (1 : Fin (n + 3)) = zw.2 (1 : Fin (n + 3)) := by
            calc
              xy.2 (1 : Fin (n + 3)) = xy.1 (1 : Fin (n + 3)) := by
                symm
                exact coord_eq_of_proj_eq hxy.2 h10
              _ = zw.1 (1 : Fin (n + 3)) := by
                exact coord_eq_of_proj_eq h2 h12
              _ = zw.2 (1 : Fin (n + 3)) := by
                exact coord_eq_of_proj_eq hzw.2 h10
          have hx : xy.1 = zw.1 := by
            calc
              xy.1
                  = (2 : Fin (n + 3)).insertNth (xy.1 (2 : Fin (n + 3)))
                      (proj (2 : Fin (n + 3)) xy.1) := by
                        simp [proj]
              _ = (2 : Fin (n + 3)).insertNth (zw.1 (2 : Fin (n + 3)))
                    (proj (2 : Fin (n + 3)) zw.1) := by rw [hx2, h2]
              _ = zw.1 := by simp [proj]
          have hy : xy.2 = zw.2 := by
            calc
              xy.2
                  = (1 : Fin (n + 3)).insertNth (xy.2 (1 : Fin (n + 3)))
                      (proj (1 : Fin (n + 3)) xy.2) := by
                        simp [proj]
              _ = (1 : Fin (n + 3)).insertNth (zw.2 (1 : Fin (n + 3)))
                    (proj (1 : Fin (n + 3)) zw.2) := by rw [hy1, h1]
              _ = zw.2 := by simp [proj]
          exact Prod.ext hx hy
      _ = p2.card * p1.card := by rw [Finset.card_product]

  have hq_sumR : (q.card : ℝ) = ∑ z ∈ p0, (((fiber0 z).card : ℝ) ^ 2) := by
    exact_mod_cast hq_sum

  have hprod :
      (s.card : ℝ) ^ 2 ≤ (p0.card : ℝ) * (p1.card : ℝ) * (p2.card : ℝ) := by
    calc
      (s.card : ℝ) ^ 2
          ≤ (p0.card : ℝ) * ∑ z ∈ p0, (((fiber0 z).card : ℝ) ^ 2) := hs_sq
      _ = (p0.card : ℝ) * (q.card : ℝ) := by rw [← hq_sumR]
      _ ≤ (p0.card : ℝ) * ((p2.card : ℝ) * (p1.card : ℝ)) := by
        gcongr
        exact_mod_cast hq_card
      _ = (p0.card : ℝ) * (p1.card : ℝ) * (p2.card : ℝ) := by ring

  let a : ℝ := p0.card
  let b : ℝ := p1.card
  let c : ℝ := p2.card
  let m : ℝ := max a (max b c)
  let t : ℝ := (s.card : ℝ) ^ (2 / 3 : ℝ)

  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    positivity
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity

  have ha_le : a ≤ m := by
    dsimp [m]
    exact le_max_left _ _
  have hb_le : b ≤ m := by
    dsimp [m]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hc_le : c ≤ m := by
    dsimp [m]
    exact le_trans (le_max_right _ _) (le_max_right _ _)

  have hmax :
      (s.card : ℝ) ^ 2 ≤ m ^ 3 := by
    have hab_le : a * b ≤ m * m := by
      exact mul_le_mul ha_le hb_le hb_nonneg hm_nonneg
    have habc_le : a * b * c ≤ (m * m) * m := by
      exact mul_le_mul hab_le hc_le hc_nonneg (mul_nonneg hm_nonneg hm_nonneg)
    calc
      (s.card : ℝ) ^ 2 ≤ a * b * c := by
        simpa [a, b, c, mul_assoc] using hprod
      _ ≤ (m * m) * m := habc_le
      _ = m ^ 3 := by ring

  have ht_le_m : t ≤ m := by
    have hroot :
        ((s.card : ℝ) ^ 2) ^ (1 / 3 : ℝ) ≤ (m ^ 3) ^ (1 / 3 : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) hmax (by positivity)
    calc
      t = ((s.card : ℝ) ^ 2) ^ (1 / 3 : ℝ) := by
        dsimp [t]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ (m ^ 3) ^ (1 / 3 : ℝ) := hroot
      _ = m := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hm_nonneg]
        norm_num

  by_cases h0 : t ≤ a
  · refine ⟨0, ?_⟩
    simpa [t, a, p0] using h0
  have hbc : t ≤ max b c := by
    by_contra hbc
    have hmax_lt : max a (max b c) < t := by
      exact max_lt (lt_of_not_ge h0) (lt_of_not_ge hbc)
    exact (not_lt_of_ge ht_le_m) hmax_lt
  by_cases h1 : t ≤ b
  · refine ⟨1, ?_⟩
    simpa [t, b, p1] using h1
  have h2 : t ≤ c := by
    by_contra h2
    have hbc_lt : max b c < t := by
      exact max_lt (lt_of_not_ge h1) (lt_of_not_ge h2)
    exact (not_lt_of_ge hbc) hbc_lt
  refine ⟨2, ?_⟩
  simpa [t, c, p2] using h2

theorem exists_large_projection {n : ℕ} (s : Finset (Fin (n + 3) → ℤ)) :
    ∃ i : Fin (n + 3), ((s.image (proj i)).card : ℝ) ≥ (1 / 2 : ℝ) * (s.card : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨i, hi⟩ := exists_large_projection_strong s
  refine ⟨i, ?_⟩
  have ht_nonneg : 0 ≤ (s.card : ℝ) ^ (2 / 3 : ℝ) := by positivity
  linarith

end Lemma54
end ChemicalLDP
