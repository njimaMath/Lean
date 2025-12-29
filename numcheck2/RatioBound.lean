import Mathlib

namespace Numcheck2

noncomputable section

open scoped Polynomial

def C (r : ℝ) : ℝ := 19 * r ^ 3 - 101 * r ^ 2 + 109 * r - 35

def Cp (r : ℝ) : ℝ := 57 * r ^ 2 - 202 * r + 109

def P (r : ℝ) : ℝ := (r ^ 2 - 6 * r + 6) ^ 2 - 18 * r * (4 - r) * (1 - r) ^ 2

def r0 : ℝ := (202 - Real.sqrt (15952 : ℝ)) / 114

def Cpoly : ℝ[X] :=
  19 * Polynomial.X ^ 3 - 101 * Polynomial.X ^ 2 + 109 * Polynomial.X - 35

lemma C_eq_eval : C = fun r : ℝ => Cpoly.eval r := by
  funext r
  simp [C, Cpoly]

lemma P_eq (r : ℝ) : P r = 1 + (r - 1) * C r := by
  simp [P, C]
  ring

lemma deriv_C (x : ℝ) : deriv C x = Cp x := by
  rw [C_eq_eval]
  have h : deriv (fun r : ℝ => Cpoly.eval r) x = Cpoly.derivative.eval x := by
    change deriv (fun r => Polynomial.eval r Cpoly) x = Polynomial.eval x Cpoly.derivative
    exact Polynomial.deriv (p := Cpoly) (x := x)
  calc
    deriv (fun r : ℝ => Cpoly.eval r) x = Cpoly.derivative.eval x := h
    _ = Cp x := by
      simp [Cpoly, Cp]
      ring

lemma deriv2_C (x : ℝ) : (deriv^[2] C) x = 114 * x - 202 := by
  rw [C_eq_eval]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  have hfun : deriv (fun r : ℝ => Cpoly.eval r) = fun r : ℝ => Cpoly.derivative.eval r := by
    funext r
    change deriv (fun r => Polynomial.eval r Cpoly) r = Polynomial.eval r Cpoly.derivative
    exact Polynomial.deriv (p := Cpoly) (x := r)
  rw [hfun]
  have h : deriv (fun r : ℝ => Cpoly.derivative.eval r) x = Cpoly.derivative.derivative.eval x := by
    change deriv (fun r => Polynomial.eval r Cpoly.derivative) x =
        Polynomial.eval x Cpoly.derivative.derivative
    exact Polynomial.deriv (p := Cpoly.derivative) (x := x)
  calc
    deriv (fun r : ℝ => Cpoly.derivative.eval r) x = Cpoly.derivative.derivative.eval x := h
    _ = 114 * x - 202 := by
      simp [Cpoly]
      ring_nf

lemma sqrt15952_lt127 : Real.sqrt (15952 : ℝ) < 127 := by
  have h0 : 0 ≤ (15952 : ℝ) := by norm_num
  have h : (15952 : ℝ) < (127 : ℝ) ^ 2 := by norm_num
  have hs := Real.sqrt_lt_sqrt h0 h
  simpa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (127 : ℝ))] using hs

lemma sqrt15952_gt88 : (88 : ℝ) < Real.sqrt (15952 : ℝ) := by
  have h0 : 0 ≤ (88 : ℝ) := by norm_num
  have h : (88 : ℝ) ^ 2 < (15952 : ℝ) := by norm_num
  have hs := Real.sqrt_lt_sqrt (sq_nonneg (88 : ℝ)) h
  simpa [Real.sqrt_sq h0] using hs

lemma r0_gt_25_38 : (25 : ℝ) / 38 < r0 := by
  have hs : Real.sqrt (15952 : ℝ) < 127 := sqrt15952_lt127
  simp [r0]
  nlinarith [hs]

lemma r0_lt_one : r0 < 1 := by
  have hs : (88 : ℝ) < Real.sqrt (15952 : ℝ) := sqrt15952_gt88
  simp [r0]
  nlinarith [hs]

lemma Cp_r0_eq_zero : Cp r0 = 0 := by
  have hD : 0 ≤ (15952 : ℝ) := by norm_num
  have hs : (Real.sqrt (15952 : ℝ)) ^ 2 = (15952 : ℝ) := Real.sq_sqrt hD
  simp [Cp, r0]
  ring_nf
  simp [hs]
  ring

lemma C_r0_eq (hCp : Cp r0 = 0) : C r0 = (5024 - 7976 * r0) / 171 := by
  have hr0sq : r0 ^ 2 = (202 * r0 - 109) / 57 := by
    have : 57 * r0 ^ 2 - 202 * r0 + 109 = 0 := by simpa [Cp] using hCp
    nlinarith
  have hr0cube : r0 ^ 3 = (34591 * r0 - 22018) / 3249 := by
    calc
      r0 ^ 3 = r0 * r0 ^ 2 := by ring
      _ = r0 * ((202 * r0 - 109) / 57) := by simp [hr0sq]
      _ = (r0 * (202 * r0 - 109)) / 57 := by ring
      _ = (202 * r0 ^ 2 - 109 * r0) / 57 := by ring
      _ = (202 * ((202 * r0 - 109) / 57) - 109 * r0) / 57 := by simp [hr0sq]
      _ = (34591 * r0 - 22018) / 3249 := by ring
  simp [C, hr0sq, hr0cube]
  ring

lemma C_r0_neg : C r0 < 0 := by
  have hr0 : (25 : ℝ) / 38 < r0 := r0_gt_25_38
  have hCeq : C r0 = (5024 - 7976 * r0) / 171 := C_r0_eq (hCp := Cp_r0_eq_zero)
  have hnum : 5024 - 7976 * r0 < 0 := by
    nlinarith [hr0]
  have hden : (0 : ℝ) < 171 := by norm_num
  have : (5024 - 7976 * r0) / 171 < 0 := div_neg_of_neg_of_pos hnum hden
  simpa [hCeq] using this

set_option maxHeartbeats 2000000 in
lemma C_neg_on_Icc {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) : C r < 0 := by
  have hcont : Continuous C := by
    change Continuous (fun r : ℝ => C r)
    simp [C]
    continuity
  have hconcave : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) C := by
    refine strictConcaveOn_of_deriv2_neg' (D := Set.Icc (0 : ℝ) 1) (convex_Icc 0 1)
      (hcont.continuousOn) ?_
    intro x hx
    have : (114 : ℝ) * x - 202 < 0 := by nlinarith [hx.2]
    simpa [deriv2_C] using this
  have hderiv0 : deriv C r0 = 0 := by
    calc
      deriv C r0 = Cp r0 := deriv_C r0
      _ = 0 := Cp_r0_eq_zero
  have hderiv2_neg : deriv (deriv C) r0 < 0 := by
    have h' : (deriv^[2] C) r0 = 114 * r0 - 202 := deriv2_C r0
    have h'' : deriv (deriv C) r0 = 114 * r0 - 202 := by
      simpa [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply] using h'
    have hr0lt1 : r0 < 1 := r0_lt_one
    have : 114 * r0 - 202 < 0 := by nlinarith [hr0lt1]
    simpa [h''] using this
  have hLocalMax : IsLocalMax C r0 :=
    isLocalMax_of_deriv_deriv_neg hderiv2_neg hderiv0 hcont.continuousAt
  have hr0_mem : r0 ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) < r0 := lt_trans (by norm_num : (0 : ℝ) < (25 : ℝ) / 38) r0_gt_25_38
      exact le_of_lt this
    · exact le_of_lt r0_lt_one
  have hMaxOn : IsMaxOn C (Set.Icc (0 : ℝ) 1) r0 :=
    IsMaxOn.of_isLocalMaxOn_of_concaveOn (a_in_s := hr0_mem) (h_localmax := hLocalMax.on _)
      (h_conc := hconcave.concaveOn)
  have hMax : ∀ x ∈ Set.Icc (0 : ℝ) 1, C x ≤ C r0 := by
    simpa [IsMaxOn, IsMaxFilter, Filter.eventually_principal] using hMaxOn
  have hle : C r ≤ C r0 := hMax r hr
  exact lt_of_le_of_lt hle C_r0_neg

set_option maxHeartbeats 2000000 in
theorem ratio_bound {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    r * (4 - r) * (1 - r) ^ 2 / (r ^ 2 - 6 * r + 6) ^ 2 ≤ (1 : ℝ) / 18 := by
  have hq_pos : 0 < r ^ 2 - 6 * r + 6 := by
    have hlin : 0 < 6 * (1 - r) := by nlinarith [hr1]
    have hsq : 0 ≤ r ^ 2 := sq_nonneg r
    have : r ^ 2 - 6 * r + 6 = r ^ 2 + 6 * (1 - r) := by ring
    -- r^2 ≥ 0 and 6*(1-r) > 0.
    have : 0 < r ^ 2 - 6 * r + 6 := by
      simpa [this] using (add_pos_of_nonneg_of_pos hsq hlin)
    exact this
  have hden_pos : 0 < (r ^ 2 - 6 * r + 6) ^ 2 := sq_pos_of_pos hq_pos

  have hrIcc : r ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hr0, le_of_lt hr1⟩
  have hCneg : C r < 0 := C_neg_on_Icc hrIcc
  have hrm1 : r - 1 < 0 := by linarith [hr1]
  have hprod_pos : 0 < (r - 1) * C r := mul_pos_of_neg_of_neg hrm1 hCneg

  have hPgt1 : 1 < P r := by
    have : 1 < 1 + (r - 1) * C r := by linarith [hprod_pos]
    simpa [P_eq] using this
  have hPpos : 0 < P r := lt_trans (by norm_num : (0 : ℝ) < 1) hPgt1

  have h18lt : 18 * r * (4 - r) * (1 - r) ^ 2 < (r ^ 2 - 6 * r + 6) ^ 2 := by
    -- P r = denom - 18*....
    have : 0 < (r ^ 2 - 6 * r + 6) ^ 2 - 18 * r * (4 - r) * (1 - r) ^ 2 := by
      simpa [P] using hPpos
    nlinarith

  have hnum_le : r * (4 - r) * (1 - r) ^ 2 ≤ (1 : ℝ) / 18 * (r ^ 2 - 6 * r + 6) ^ 2 := by
    have : r * (4 - r) * (1 - r) ^ 2 < (1 : ℝ) / 18 * (r ^ 2 - 6 * r + 6) ^ 2 := by
      nlinarith [h18lt]
    exact le_of_lt this

  -- Divide by the positive denominator.
  exact (div_le_iff₀ hden_pos).2 hnum_le

end
end Numcheck2
