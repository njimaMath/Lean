import Mathlib

namespace Numcheck

noncomputable section

def F (x y : ℝ) : ℝ :=
  x ^ 2 + 6 * x * y + 6 * y ^ 2 - x - 4 * y

def q (x y : ℝ) : ℝ :=
  x ^ 2 + x * y - 3 * x - 3 * y + 2

def disc (y : ℝ) : ℝ :=
  y ^ 2 + 6 * y + 1

def rMinus (y : ℝ) : ℝ :=
  (3 - y - Real.sqrt (disc y)) / 2

def rPlus (y : ℝ) : ℝ :=
  (3 - y + Real.sqrt (disc y)) / 2

set_option maxHeartbeats 2000000 in
theorem F_neg_of_constraints {x y : ℝ}
    (hx : 0 ≤ x) (hy0 : 0 < y) (hy : y < (2 : ℝ) / 3)
    (h₁ : 1 ≤ x + 2 * y)
    (h₂ : 0 ≤ q x y)
    (h₃ : x + y < 1) :
    F x y < 0 := by
  have hy1 : 0 < y + 1 := by linarith
  have hdisc : 0 ≤ disc y := by
    -- Unfold `disc`; then `nlinarith` can use `y > 0` directly.
    simp [disc]
    nlinarith [hy0]

  have hsqrt_gt : y + 1 < Real.sqrt (disc y) := by
    have hlt : (y + 1) ^ 2 < disc y := by
      simp [disc]
      nlinarith [hy0]
    have hsqrt : Real.sqrt ((y + 1) ^ 2) < Real.sqrt (disc y) :=
      Real.sqrt_lt_sqrt (sq_nonneg (y + 1)) hlt
    simpa [Real.sqrt_sq hy1.le] using hsqrt

  have hrPlus_gt2 : (2 : ℝ) < rPlus y := by
    -- `2 < (3 - y + √(disc y)) / 2` ↔ `y + 1 < √(disc y)`.
    simp [rPlus]
    nlinarith [hsqrt_gt]

  have hx_lt1 : x < 1 := by nlinarith [h₃, hy0]
  have hx_lt_rPlus : x < rPlus y := lt_trans hx_lt1 (lt_trans (by linarith) hrPlus_gt2)

  have hr_sum : rMinus y + rPlus y = 3 - y := by
    simp [rMinus, rPlus, sub_eq_add_neg, div_eq_mul_inv]
    ring

  have hr_prod : rMinus y * rPlus y = 2 - 3 * y := by
    -- Use difference of squares, then `(√(disc y))^2 = disc y` since `disc y ≥ 0`.
    have hsq : Real.sqrt (disc y) ^ 2 = disc y := Real.sq_sqrt hdisc
    have hmul : rMinus y * rPlus y = ((3 - y) ^ 2 - (Real.sqrt (disc y)) ^ 2) / 4 := by
      simp [rMinus, rPlus]
      ring
    calc
      rMinus y * rPlus y = ((3 - y) ^ 2 - (Real.sqrt (disc y)) ^ 2) / 4 := hmul
      _ = ((3 - y) ^ 2 - disc y) / 4 := by simp [hsq]
      _ = 2 - 3 * y := by
        simp [disc]
        ring

  have hq_factor (x0 : ℝ) :
      (x0 - rMinus y) * (x0 - rPlus y) = q x0 y := by
    calc
      (x0 - rMinus y) * (x0 - rPlus y)
          = x0 ^ 2 - (rMinus y + rPlus y) * x0 + (rMinus y * rPlus y) := by ring
      _ = x0 ^ 2 - (3 - y) * x0 + (2 - 3 * y) := by simp [hr_sum, hr_prod]
      _ = q x0 y := by
        simp [q]
        ring

  have hprod_nonneg : 0 ≤ (x - rMinus y) * (x - rPlus y) := by
    -- Rewrite the quadratic constraint using the factorization.
    simpa [hq_factor x] using h₂

  have hx_le_rMinus : x ≤ rMinus y := by
    have hneg : x - rPlus y < 0 := sub_neg.2 hx_lt_rPlus
    have hnonpos : x - rMinus y ≤ 0 := by
      by_contra hpos
      have hpos' : 0 < x - rMinus y := lt_of_not_ge hpos
      have : (x - rMinus y) * (x - rPlus y) < 0 := mul_neg_of_pos_of_neg hpos' hneg
      exact (not_lt_of_ge hprod_nonneg) this
    exact sub_nonpos.1 hnonpos

  set a : ℝ := max 0 (1 - 2 * y) with ha_def

  have ha_le : a ≤ x := by
    have h₁' : 1 - 2 * y ≤ x := by linarith [h₁]
    exact (max_le_iff).2 ⟨hx, h₁'⟩

  have hx_mem : x ∈ Set.Icc a (rMinus y) := ⟨ha_le, hx_le_rMinus⟩

  have hFa : F a y < 0 := by
    by_cases hy_half : y ≤ (1 : ℝ) / 2
    ·
      have ha : a = 1 - 2 * y := by
        have hnonneg : 0 ≤ 1 - 2 * y := by nlinarith [hy_half]
        simp [ha_def, max_eq_right hnonneg]
      have hF : F (1 - 2 * y) y = -2 * y ^ 2 := by
        simp [F]
        ring
      have hneg : -2 * y ^ 2 < 0 := by nlinarith [hy0]
      simpa [ha, hF] using hneg
    ·
      have ha : a = 0 := by
        have hnonpos : 1 - 2 * y ≤ 0 := by nlinarith [lt_of_not_ge hy_half]
        simp [ha_def, max_eq_left hnonpos]
      have : F 0 y < 0 := by
        simp [F]
        nlinarith [hy0, hy]
      simpa [ha] using this

  have hFb : F (rMinus y) y < 0 := by
    have hq_rMinus : q (rMinus y) y = 0 := by
      have : (rMinus y - rMinus y) * (rMinus y - rPlus y) = q (rMinus y) y :=
        hq_factor (rMinus y)
      simpa using this.symm

    have hF_decomp (x0 : ℝ) :
        F x0 y = q x0 y + (x0 * (5 * y + 2) + (6 * y ^ 2 - y - 2)) := by
      simp [F, q]
      ring

    have hFr :
        F (rMinus y) y =
          ((7 * y ^ 2 + 11 * y + 2) - (5 * y + 2) * Real.sqrt (disc y)) / 2 := by
      have hlin : F (rMinus y) y = (rMinus y) * (5 * y + 2) + (6 * y ^ 2 - y - 2) := by
        simp [hF_decomp, hq_rMinus]
      calc
        F (rMinus y) y = (rMinus y) * (5 * y + 2) + (6 * y ^ 2 - y - 2) := hlin
        _ =
            ((7 * y ^ 2 + 11 * y + 2) - (5 * y + 2) * Real.sqrt (disc y)) / 2 := by
          simp [rMinus]
          ring

    have hA_pos : 0 < 5 * y + 2 := by nlinarith [hy0]
    have hB_pos : 0 < 7 * y ^ 2 + 11 * y + 2 := by nlinarith [hy0]

    have hsq_lt :
        (7 * y ^ 2 + 11 * y + 2) ^ 2 < ((5 * y + 2) * Real.sqrt (disc y)) ^ 2 := by
      have hdiff :
          (5 * y + 2) ^ 2 * disc y - (7 * y ^ 2 + 11 * y + 2) ^ 2 = 8 * y ^ 3 * (2 - 3 * y) := by
        simp [disc]
        ring
      have hpos : 0 < (5 * y + 2) ^ 2 * disc y - (7 * y ^ 2 + 11 * y + 2) ^ 2 := by
        have hy3 : 0 < y ^ 3 := pow_pos hy0 3
        have h2 : 0 < 2 - 3 * y := by nlinarith [hy]
        have h8 : 0 < (8 : ℝ) := by norm_num
        have : 0 < 8 * y ^ 3 * (2 - 3 * y) := by nlinarith [hy3, h2, h8]
        simpa [hdiff] using this
      have hineq : (7 * y ^ 2 + 11 * y + 2) ^ 2 < (5 * y + 2) ^ 2 * disc y := by
        nlinarith [hpos]
      have : ((5 * y + 2) * Real.sqrt (disc y)) ^ 2 = (5 * y + 2) ^ 2 * disc y := by
        calc
          ((5 * y + 2) * Real.sqrt (disc y)) ^ 2 =
              (5 * y + 2) ^ 2 * (Real.sqrt (disc y)) ^ 2 := by ring
          _ = (5 * y + 2) ^ 2 * disc y := by simp [Real.sq_sqrt hdisc]
      simpa [this] using hineq

    have hlt :
        (7 * y ^ 2 + 11 * y + 2) < (5 * y + 2) * Real.sqrt (disc y) := by
      have hB0 : 0 ≤ 7 * y ^ 2 + 11 * y + 2 := le_of_lt hB_pos
      have hA0 : 0 ≤ (5 * y + 2) * Real.sqrt (disc y) :=
        mul_nonneg (le_of_lt hA_pos) (Real.sqrt_nonneg _)
      exact (sq_lt_sq₀ hB0 hA0).1 hsq_lt

    have hnum_lt : (7 * y ^ 2 + 11 * y + 2) - (5 * y + 2) * Real.sqrt (disc y) < 0 :=
      sub_lt_zero.2 hlt

    have : ((7 * y ^ 2 + 11 * y + 2) - (5 * y + 2) * Real.sqrt (disc y)) / 2 < 0 := by
      have h2 : 0 < (2 : ℝ) := by norm_num
      have := div_lt_div_of_pos_right hnum_lt h2
      simpa using this
    simpa [hFr] using this

  -- Convexity of `x ↦ F x y` gives `F x y ≤ max (F a y) (F (rMinus y) y)`.
  have hconv_sq : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 : ℕ)) := by
    simpa using (Even.convexOn_pow (𝕜 := ℝ) (n := (2 : ℕ)) (by decide : Even (2 : ℕ)))

  have hconv_lin : ConvexOn ℝ Set.univ fun x : ℝ => (6 * y - 1) * x := by
    refine ⟨convex_univ, ?_⟩
    intro x₁ _ x₂ _ α β _ _ _
    have : (6 * y - 1) * (α * x₁ + β * x₂) = α * ((6 * y - 1) * x₁) + β * ((6 * y - 1) * x₂) := by
      ring
    simp [smul_eq_mul, this]

  have hconv_const : ConvexOn ℝ Set.univ fun _ : ℝ => 6 * y ^ 2 - 4 * y :=
    convexOn_const _ convex_univ

  have hconv_F_aux :
      ConvexOn ℝ Set.univ
        ((fun x : ℝ => x ^ 2) + ((fun x : ℝ => (6 * y - 1) * x) + fun _ : ℝ => 6 * y ^ 2 - 4 * y)) :=
    hconv_sq.add (hconv_lin.add hconv_const)

  have hconv_F' :
      ConvexOn ℝ Set.univ fun x : ℝ => x ^ 2 + (6 * y - 1) * x + (6 * y ^ 2 - 4 * y) := by
    refine hconv_F_aux.congr ?_
    intro x0 _
    simp [Pi.add_apply, add_assoc]

  have hconv_F : ConvexOn ℝ Set.univ fun x0 : ℝ => F x0 y := by
    refine hconv_F'.congr ?_
    intro x0 _
    simp [F]
    ring

  have hF_le :
      F x y ≤ max (F a y) (F (rMinus y) y) := by
    have hF_le' :
        (fun x0 : ℝ => F x0 y) x ≤
          max ((fun x0 : ℝ => F x0 y) a) ((fun x0 : ℝ => F x0 y) (rMinus y)) := by
      exact
        ConvexOn.le_max_of_mem_Icc (𝕜 := ℝ) (β := ℝ) (s := (Set.univ : Set ℝ))
          (f := fun x0 : ℝ => F x0 y) (hf := hconv_F) (x := a) (y := rMinus y) (z := x)
          (hx := by simp) (hy := by simp) hx_mem
    simpa using hF_le'

  have hmax_lt : max (F a y) (F (rMinus y) y) < 0 := (max_lt_iff).2 ⟨hFa, hFb⟩

  exact lt_of_le_of_lt hF_le hmax_lt

end
end Numcheck
