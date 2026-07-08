import Mathlib
import perceptronFixed.decreasing_g.decreasing_g
import perceptronFixed.rational_function_bound.RatioBound

open scoped BigOperators Topology NNReal
open MeasureTheory

namespace UniformBoundOfG

noncomputable section

/-!
This file follows the blueprint `uniform_bound_of_g/blueprint.txt`.

Goal: prove the uniform bound `g u ≤ 1/18` on the negative half-line `u ≤ 0`,
where `g` is the auxiliary function built from the inverse Mills ratio.

We reuse analytic computations from `perceptronFixed.decreasing_g.decreasing_g` and the
rational-function bound from `perceptronFixed.rational_function_bound.RatioBound`.
-/

/-! ## Definitions (matching `main.tex`)

We alias the definitions already used in `DecreasingG` so we can reuse its lemmas.
-/

abbrev φ (u : ℝ) : ℝ := DecreasingG.φ u
abbrev Φbar (u : ℝ) : ℝ := DecreasingG.Φbar u
abbrev E (u : ℝ) : ℝ := DecreasingG.E u
abbrev d (u : ℝ) : ℝ := DecreasingG.d u
abbrev g (u : ℝ) : ℝ := DecreasingG.g u
abbrev H (u : ℝ) : ℝ := DecreasingG.H u

/-! ## Analytic facts -/

lemma Φbar_pos (u : ℝ) : 0 < Φbar u := by
  simpa [Φbar] using DecreasingG.Φbar_pos u

lemma E_pos (u : ℝ) : 0 < E u := by
  simpa [E] using DecreasingG.E_pos u

lemma d_pos (u : ℝ) : 0 < d u := by
  simpa [d] using DecreasingG.d_pos u

lemma φ_pos (u : ℝ) : 0 < φ u := by
  -- Uses the closed form for the Gaussian density.
  have hnum : 0 < Real.exp (-(u ^ 2) / 2) := Real.exp_pos _
  have hden : 0 < Real.sqrt (2 * Real.pi) := by
    have h2pi : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    exact Real.sqrt_pos.2 h2pi
  simpa [φ, DecreasingG.φ] using div_pos hnum hden

lemma Φbar_continuous : Continuous Φbar := by
  -- We use that `deriv Φbar u = -φ u` and `φ u ≠ 0`, hence `Φbar` is differentiable everywhere.
  refine (continuous_iff_continuousAt.2 fun u => ?_)
  have hderiv : deriv Φbar u = -φ u := by
    simpa [Φbar, φ] using DecreasingG.deriv_Φbar u
  have hne : deriv Φbar u ≠ 0 := by
    have hneg : -φ u < 0 := by nlinarith [φ_pos u]
    exact by simpa [hderiv] using (ne_of_lt hneg)
  exact (differentiableAt_of_deriv_ne_zero hne).continuousAt

lemma φ_continuous : Continuous φ := by
  -- `φ(u) = exp(-u^2/2) / sqrt(2π)` is continuous.
  unfold φ DecreasingG.φ
  fun_prop

lemma E_continuous : Continuous E := by
  -- `E = φ / Φbar`, with `Φbar` nowhere vanishing.
  have hΦbar_ne : ∀ u, Φbar u ≠ 0 := fun u => (Φbar_pos u).ne'
  -- unfold the alias so `Continuous.div` applies.
  simpa [E, DecreasingG.E] using (φ_continuous.div Φbar_continuous hΦbar_ne)

lemma g_continuous : Continuous g := by
  -- `g` is a polynomial expression in `u` and `E(u)`.
  have hE : Continuous (fun u : ℝ => DecreasingG.E u) := by
    simpa [E] using (E_continuous : Continuous E)
  unfold g DecreasingG.g
  fun_prop [hE]

lemma E_deriv (u : ℝ) : deriv E u = (E u) ^ 2 - u * E u := by
  simpa [E] using DecreasingG.deriv_E u

lemma g_eq_quartic (u : ℝ) :
    g u = (E u) ^ 2 * (3 * (E u) ^ 2 - 4 * u * E u + u ^ 2 - 2) := by
  rfl

lemma g_deriv_eq (u : ℝ) : deriv g u = 2 * (E u) ^ 2 * H u := by
  simpa [g, E, H] using DecreasingG.g_deriv_eq u

lemma g_tendsto_zero_atBot : Filter.Tendsto g Filter.atBot (𝓝 0) := by
  -- Strategy: show `E u → 0` and `(u * E u) → 0` as `u → -∞`, then expand `g`.
  have hΦbar0_pos : 0 < Φbar 0 := Φbar_pos 0

  have hφ_integrable : Integrable φ (volume : Measure ℝ) := by
    -- `φ` is the standard Gaussian density, hence integrable.
    have hφ_eq : φ = ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : NNReal) := by
      funext x
      simp [φ, DecreasingG.φ, ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv, mul_assoc, mul_comm,
        mul_left_comm]
    simpa [hφ_eq] using ProbabilityTheory.integrable_gaussianPDFReal (μ := (0 : ℝ)) (v := (1 : NNReal))

  have Φbar0_le_Φbar {u : ℝ} (hu : u ≤ 0) : Φbar 0 ≤ Φbar u := by
    -- Since `u ≤ 0`, we have `Ici 0 ⊆ Ici u`, hence the tail integral is larger.
    have hst : (Set.Ici (0 : ℝ) : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Ici u := by
      refine ae_of_all _ (fun x hx => ?_)
      exact le_trans hu hx
    have hfi : IntegrableOn φ (Set.Ici u) (volume : Measure ℝ) := hφ_integrable.integrableOn
    have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ici u)] φ := by
      refine ae_of_all _ (fun x => (φ_pos x).le)
    have hle :=
      MeasureTheory.setIntegral_mono_set (μ := (volume : Measure ℝ)) (f := φ)
        (s := Set.Ici (0 : ℝ)) (t := Set.Ici u) hfi hnonneg hst
    simpa [Φbar, DecreasingG.Φbar] using hle

  have hE_le {u : ℝ} (hu : u ≤ 0) : E u ≤ φ u / Φbar 0 := by
    have hΦ : Φbar 0 ≤ Φbar u := Φbar0_le_Φbar hu
    have hφ_nonneg : 0 ≤ φ u := (φ_pos u).le
    have h := div_le_div_of_nonneg_left hφ_nonneg hΦbar0_pos hΦ
    simpa [E, DecreasingG.E] using h

  have hφ_tendsto : Filter.Tendsto φ Filter.atBot (𝓝 0) := by
    -- `φ(u) = exp(-u^2/2)/sqrt(2π)` tends to 0 as `u → -∞`.
    have hpow : Filter.Tendsto (fun u : ℝ => u ^ 2) Filter.atBot Filter.atTop := by
      have hneg : Filter.Tendsto (fun u : ℝ => -u) Filter.atBot Filter.atTop :=
        Filter.tendsto_neg_atBot_atTop
      have hpow' : Filter.Tendsto (fun u : ℝ => u ^ 2) Filter.atTop Filter.atTop := by
        simpa using (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
      -- `( -u )^2 = u^2`
      exact (hpow'.comp hneg).congr' (Filter.Eventually.of_forall fun u => by simp)
    have hneg : Filter.Tendsto (fun u : ℝ => -(u ^ 2)) Filter.atBot Filter.atBot :=
      (Filter.tendsto_neg_atTop_atBot).comp hpow
    have hdiv : Filter.Tendsto (fun u : ℝ => -(u ^ 2) / (2 : ℝ)) Filter.atBot Filter.atBot :=
      hneg.atBot_div_const (by norm_num)
    have hexp : Filter.Tendsto (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) Filter.atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hdiv
    change
      Filter.Tendsto (fun u : ℝ => Real.exp (-(u ^ 2) / 2) / Real.sqrt (2 * Real.pi)) Filter.atBot
        (𝓝 0)
    simpa using (hexp.div_const (Real.sqrt (2 * Real.pi)))

  have hE_tendsto : Filter.Tendsto E Filter.atBot (𝓝 0) := by
    -- `0 ≤ E u ≤ φ u / Φbar 0` eventually at `-∞`.
    have hbound : ∀ᶠ u in Filter.atBot, ‖E u‖ ≤ φ u / Φbar 0 := by
      filter_upwards [Filter.eventually_le_atBot (a := (0 : ℝ))] with u hu
      have hle : E u ≤ φ u / Φbar 0 := hE_le hu
      have hE0 : 0 ≤ E u := (E_pos u).le
      simpa [Real.norm_eq_abs, abs_of_nonneg hE0] using hle
    have hφ_div : Filter.Tendsto (fun u => φ u / Φbar 0) Filter.atBot (𝓝 0) := by
      simpa using (hφ_tendsto.div_const (Φbar 0))
    exact squeeze_zero_norm' hbound hφ_div

  have hnorm_mul_φ : Filter.Tendsto (fun u : ℝ => ‖u‖ * φ u) Filter.atBot (𝓝 0) := by
    -- bound by `(u^2/2) * φ u`, which tends to 0.
    have ht : Filter.Tendsto (fun u : ℝ => u ^ 2 / (2 : ℝ)) Filter.atBot Filter.atTop := by
      have hpow : Filter.Tendsto (fun u : ℝ => u ^ 2) Filter.atBot Filter.atTop := by
        have hneg : Filter.Tendsto (fun u : ℝ => -u) Filter.atBot Filter.atTop :=
          Filter.tendsto_neg_atBot_atTop
        have hpow' : Filter.Tendsto (fun u : ℝ => u ^ 2) Filter.atTop Filter.atTop := by
          simpa using (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
        exact (hpow'.comp hneg).congr' (Filter.Eventually.of_forall fun u => by simp)
      simpa [div_eq_mul_inv, mul_assoc] using hpow.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    have hmain :
        Filter.Tendsto (fun u : ℝ => (u ^ 2 / (2 : ℝ)) * Real.exp (-(u ^ 2 / (2 : ℝ))))
          Filter.atBot (𝓝 0) := by
      -- Compose `x ↦ x * exp(-x)` with `x = u^2/2`.
      simpa [pow_one] using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ht
    have hmain' :
        Filter.Tendsto (fun u : ℝ => (u ^ 2 / (2 : ℝ)) * φ u) Filter.atBot (𝓝 0) := by
      -- Convert the `exp` form to `φ`.
      have : (fun u : ℝ => (u ^ 2 / (2 : ℝ)) * φ u) =
          (fun u : ℝ => ((u ^ 2 / (2 : ℝ)) * Real.exp (-(u ^ 2 / (2 : ℝ)))) / Real.sqrt (2 * Real.pi)) := by
        funext u
        simp [φ, DecreasingG.φ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      simpa [this] using hmain.div_const (Real.sqrt (2 * Real.pi))
    have hbound : ∀ᶠ u in Filter.atBot, ‖‖u‖ * φ u‖ ≤ (u ^ 2 / (2 : ℝ)) * φ u := by
      filter_upwards [Filter.eventually_le_atBot (a := (-2 : ℝ))] with u hu
      have hu0 : u ≤ 0 := le_trans hu (by norm_num)
      have hφ0 : 0 ≤ φ u := (φ_pos u).le
      have hφ_abs : |φ u| = φ u := abs_of_nonneg hφ0
      have hnorm_u : ‖u‖ = -u := by
        simpa [Real.norm_eq_abs, abs_of_nonpos hu0] using (rfl : (‖u‖ : ℝ) = ‖u‖)
      have hineq : (-u) ≤ u ^ 2 / (2 : ℝ) := by
        -- for `u ≤ -2`, we have `-u ≥ 2` and thus `-u ≤ u^2 / 2`.
        have : (2 : ℝ) ≤ -u := by linarith
        nlinarith
      have hnorm_le : ‖u‖ ≤ u ^ 2 / (2 : ℝ) := by simpa [hnorm_u] using hineq
      calc
        ‖‖u‖ * φ u‖ = ‖u‖ * ‖φ u‖ := by simpa [norm_mul]
        _ = ‖u‖ * φ u := by simp [Real.norm_eq_abs, hφ_abs]
        _ ≤ (u ^ 2 / (2 : ℝ)) * φ u := mul_le_mul_of_nonneg_right hnorm_le hφ0
    exact squeeze_zero_norm' hbound hmain'

  have huE_tendsto : Filter.Tendsto (fun u : ℝ => u * E u) Filter.atBot (𝓝 0) := by
    -- Use `‖u * E u‖ ≤ ‖u‖ * (φ u / Φbar 0)` eventually.
    have hbound : ∀ᶠ u in Filter.atBot, ‖u * E u‖ ≤ (‖u‖ * φ u) / Φbar 0 := by
      filter_upwards [Filter.eventually_le_atBot (a := (0 : ℝ))] with u hu
      have hle : E u ≤ φ u / Φbar 0 := hE_le hu
      have hE0 : 0 ≤ E u := (E_pos u).le
      have hE_le_norm : ‖E u‖ ≤ φ u / Φbar 0 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hE0] using hle
      calc
        ‖u * E u‖ = ‖u‖ * ‖E u‖ := by simpa [norm_mul]
        _ ≤ ‖u‖ * (φ u / Φbar 0) := mul_le_mul_of_nonneg_left hE_le_norm (by positivity : 0 ≤ ‖u‖)
        _ = (‖u‖ * φ u) / Φbar 0 := by simp [mul_div_assoc, mul_assoc, mul_left_comm, mul_comm]
    have hdiv : Filter.Tendsto (fun u : ℝ => (‖u‖ * φ u) / Φbar 0) Filter.atBot (𝓝 0) := by
      simpa using (hnorm_mul_φ.div_const (Φbar 0))
    exact squeeze_zero_norm' hbound hdiv

  -- Now expand `g` in terms of `E` and `u * E`.
  have hE2 : Filter.Tendsto (fun u : ℝ => (E u) ^ 2) Filter.atBot (𝓝 0) := by
    simpa [pow_two] using (hE_tendsto.mul hE_tendsto)
  have hE4 : Filter.Tendsto (fun u : ℝ => (E u) ^ 4) Filter.atBot (𝓝 0) := by
    simpa using (hE_tendsto.pow 4)
  have huE2 : Filter.Tendsto (fun u : ℝ => (u * E u) ^ 2) Filter.atBot (𝓝 0) := by
    simpa [pow_two] using (huE_tendsto.mul huE_tendsto)
  have huE_mul_E2 : Filter.Tendsto (fun u : ℝ => (u * E u) * (E u) ^ 2) Filter.atBot (𝓝 0) := by
    simpa using (huE_tendsto.mul hE2)

  -- g(u) = 3E^4 - 4 (uE) E^2 + (uE)^2 - 2E^2
  have hterm1 : Filter.Tendsto (fun u : ℝ => (3 : ℝ) * (E u) ^ 4) Filter.atBot (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (b := (3 : ℝ)) hE4)
  have hterm2 : Filter.Tendsto (fun u : ℝ => (-4 : ℝ) * ((u * E u) * (E u) ^ 2)) Filter.atBot (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (b := (-4 : ℝ)) huE_mul_E2)
  have hterm3 : Filter.Tendsto (fun u : ℝ => (u * E u) ^ 2) Filter.atBot (𝓝 0) := huE2
  have hterm4 : Filter.Tendsto (fun u : ℝ => (-2 : ℝ) * (E u) ^ 2) Filter.atBot (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (b := (-2 : ℝ)) hE2)

  have hg_expanded :
      (fun u : ℝ =>
          (3 : ℝ) * (E u) ^ 4 +
            (-4 : ℝ) * ((u * E u) * (E u) ^ 2) +
              (u * E u) ^ 2 +
                (-2 : ℝ) * (E u) ^ 2) = g := by
    funext u
    simp [g, DecreasingG.g, pow_two, mul_assoc, mul_left_comm, mul_comm]
    ring

  -- Conclude using the expanded form and the termwise limits.
  have hsum :
      Filter.Tendsto
        (fun u : ℝ =>
            (3 : ℝ) * (E u) ^ 4 +
              (-4 : ℝ) * ((u * E u) * (E u) ^ 2) +
                (u * E u) ^ 2 +
                  (-2 : ℝ) * (E u) ^ 2) Filter.atBot (𝓝 0) := by
    simpa using (((hterm1.add hterm2).add hterm3).add hterm4)
  -- Rewrite `g` to the expanded form to apply the termwise limit.
  refine (hsum.congr' (Filter.Eventually.of_forall fun u => ?_))
  have hg_u :=
    congrArg (fun f : ℝ → ℝ => f u) hg_expanded
  -- Normalize the algebraic form of the expanded polynomial.
  simpa [mul_assoc, mul_left_comm, mul_comm] using hg_u

lemma g_zero_neg : g 0 < 0 := by
  -- In `main.tex`, one computes `g(0)=12/π^2-4/π<0`.
  have hg0 : g 0 = 12 / Real.pi ^ 2 - 4 / Real.pi := by
    simpa [g] using DecreasingG.g0_eq
  have hpi3 : (3 : ℝ) < Real.pi := by simpa using Real.pi_gt_three
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hden : 0 < (Real.pi : ℝ) ^ 2 := sq_pos_of_pos Real.pi_pos
  have hnum : 12 - 4 * (Real.pi : ℝ) < 0 := by nlinarith [hpi3]
  have : (12 / Real.pi ^ 2 - 4 / Real.pi) < 0 := by
    -- Rewrite as `(12 - 4π)/π^2`.
    have :
        12 / Real.pi ^ 2 - 4 / Real.pi = (12 - 4 * Real.pi) / Real.pi ^ 2 := by
      field_simp [hpi_ne]
    rw [this]
    exact div_neg_of_neg_of_pos hnum hden
  simpa [hg0] using this

/-! ## Existence of an interior maximizer and critical point -/

lemma exists_interior_maximizer_of_exists_pos
    (hpos : ∃ u, u ≤ (0 : ℝ) ∧ 0 < g u) :
    ∃ uStar, uStar < 0 ∧ (∀ u, u ≤ (0 : ℝ) → g u ≤ g uStar) ∧ deriv g uStar = 0 := by
  /-
  Blueprint idea:
    - Let S = sup_{u≤0} g(u). If S > 0, use `g(0) < 0` and `g(u) → 0` as u→-∞
      to show S is attained at an interior maximizer u⋆ < 0.
    - At an interior maximizer, `deriv g u⋆ = 0`.
  -/
  classical
  rcases hpos with ⟨v, hv0, hvpos⟩
  have hvpos' : 0 < g v := hvpos
  have hεpos : 0 < g v / 2 := by nlinarith

  -- Tail control from `g(u) → 0` as `u → -∞`.
  have hnorm_tendsto : Filter.Tendsto (fun u : ℝ => ‖g u‖) Filter.atBot (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).1 g_tendsto_zero_atBot
  have hIio : Set.Iio (g v / 2) ∈ (𝓝 (0 : ℝ)) := Iio_mem_nhds hεpos
  have h_event : ∀ᶠ u in Filter.atBot, ‖g u‖ < g v / 2 := by
    simpa [Set.mem_Iio] using (hnorm_tendsto.eventually hIio)
  rcases (Filter.eventually_atBot.mp h_event) with ⟨a, ha⟩

  have hav : a < v := by
    by_contra hle
    have hv_le : v ≤ a := le_of_not_gt hle
    have : ‖g v‖ < g v / 2 := ha v hv_le
    have hnorm : ‖g v‖ = g v := by
      have : 0 ≤ g v := (le_of_lt hvpos')
      simpa [Real.norm_eq_abs, abs_of_nonneg this] using rfl
    nlinarith [this, hnorm]

  have ha0 : a < 0 := lt_of_lt_of_le hav hv0

  -- Maximize on the compact interval `[a, 0]`.
  have hcomp : IsCompact (Set.Icc a (0 : ℝ)) := isCompact_Icc
  have hne : (Set.Icc a (0 : ℝ)).Nonempty := ⟨0, by exact ⟨le_of_lt ha0, le_rfl⟩⟩
  obtain ⟨uStar, huStar_mem, huStar_max⟩ :=
    hcomp.exists_isMaxOn hne (g_continuous.continuousOn)
  have huStar_le0 : uStar ≤ 0 := huStar_mem.2
  have ha_le_uStar : a ≤ uStar := huStar_mem.1

  -- `v ∈ [a,0]`, so the maximum value is at least `g v > 0`.
  have hv_mem : v ∈ Set.Icc a (0 : ℝ) := ⟨le_of_lt hav, hv0⟩
  have huStar_max' : ∀ x ∈ Set.Icc a (0 : ℝ), g x ≤ g uStar := by
    simpa [IsMaxOn, IsMaxFilter, Filter.eventually_principal] using huStar_max
  have hgv_le : g v ≤ g uStar := huStar_max' v hv_mem
  have huStar_gpos : 0 < g uStar := lt_of_lt_of_le hvpos' hgv_le
  have huStar_ne0 : uStar ≠ 0 := by
    intro h
    have hpos0 : 0 < g 0 := by simpa [h] using huStar_gpos
    exact (lt_asymm hpos0 g_zero_neg)
  have huStar_lt0 : uStar < 0 := lt_of_le_of_ne huStar_le0 huStar_ne0

  -- Exclude the left endpoint to get an interior point.
  have huStar_ne_a : uStar ≠ a := by
    intro h
    have hna : ‖g a‖ < g v / 2 := ha a le_rfl
    have hga : g a < g v / 2 := by
      have hle : g a ≤ ‖g a‖ := by
        simpa [Real.norm_eq_abs] using (le_abs_self (g a))
      exact lt_of_le_of_lt hle hna
    have : g v ≤ g a := by simpa [h] using hgv_le
    nlinarith [hga, this]
  have ha_lt_uStar : a < uStar := lt_of_le_of_ne ha_le_uStar (Ne.symm huStar_ne_a)

  have hnhds : Set.Icc a (0 : ℝ) ∈ 𝓝 uStar := Icc_mem_nhds ha_lt_uStar huStar_lt0
  have hlocal : IsLocalMax g uStar := huStar_max.isLocalMax hnhds
  have hcrit : deriv g uStar = 0 := hlocal.deriv_eq_zero

  refine ⟨uStar, huStar_lt0, ?_, hcrit⟩
  intro u hu0
  by_cases hua : a ≤ u
  · have hu_mem : u ∈ Set.Icc a (0 : ℝ) := ⟨hua, hu0⟩
    exact huStar_max' u hu_mem
  · have hu_le : u ≤ a := le_of_not_ge hua
    have hnu : ‖g u‖ < g v / 2 := ha u hu_le
    have hgu : g u < g v / 2 := by
      have hle : g u ≤ ‖g u‖ := by
        simpa [Real.norm_eq_abs] using (le_abs_self (g u))
      exact lt_of_le_of_lt hle hnu
    have : g v / 2 < g uStar := by nlinarith [hvpos', hgv_le]
    exact le_of_lt (lt_trans hgu this)

lemma H_eq_zero_of_critical {u : ℝ} (hcrit : deriv g u = 0) : H u = 0 := by
  -- From `g_deriv_eq` and `E_pos`, `deriv g u = 2 (E u)^2 (H u)`.
  -- Since `2 (E u)^2 > 0`, we get `H u = 0`.
  have h : (2 * (E u) ^ 2) * H u = 0 := by
    have : deriv g u = (2 * (E u) ^ 2) * H u := by
      simpa [mul_assoc] using (g_deriv_eq (u := u))
    simpa [this] using hcrit
  have hfac : (2 * (E u) ^ 2) ≠ 0 := by
    have : 0 < (E u) ^ 2 := sq_pos_of_pos (E_pos u)
    nlinarith
  rcases mul_eq_zero.mp h with h0 | h0
  · exfalso
    exact hfac h0
  · exact h0

/-! ## Parameterization of critical points and value of g -/

lemma r_mem_Ioo_of_critical {uStar : ℝ} (huStar : uStar < 0) :
    let dStar := d uStar
    let rStar := -uStar / dStar
    (0 : ℝ) < rStar ∧ rStar < 1 := by
  /-
  Blueprint idea:
    - d⋆ = E(u⋆) - u⋆ > 0, so r⋆ > 0.
    - E(u⋆) = u⋆ + d⋆ = d⋆ (1 - r⋆) > 0, hence r⋆ < 1.
  -/
  dsimp
  have hdpos : 0 < d uStar := d_pos uStar
  have hrpos : 0 < -uStar / d uStar := by
    have hnum : 0 < -uStar := by nlinarith
    exact div_pos hnum hdpos
  refine ⟨hrpos, ?_⟩
  -- `-uStar / d uStar < 1` follows from `-uStar < d uStar` and `d uStar > 0`.
  have hlt : -uStar < d uStar := by
    -- `d uStar - (-uStar) = E uStar > 0`.
    have hE : 0 < E uStar := E_pos uStar
    -- `d uStar = E uStar - uStar`.
    have : d uStar = E uStar - uStar := by simp [d, DecreasingG.d]
    nlinarith [hE, this]
  have : (-uStar) / d uStar < (d uStar) / d uStar := div_lt_div_of_pos_right hlt hdpos
  simpa [hdpos.ne'] using this

lemma d_sq_eq_of_H_eq_zero {uStar : ℝ} (huStar : uStar < 0) (hH : H uStar = 0) :
    let dStar := d uStar
    let rStar := -uStar / dStar
    dStar ^ 2 = (4 - rStar) / (rStar ^ 2 - 6 * rStar + 6) := by
  /-
  Blueprint algebra:
    Substitute u⋆ = -r⋆ d⋆ into H(u⋆)=0 to get
      (r⋆^2 - 6r⋆ + 6) d⋆^2 + (r⋆ - 4) = 0.
  -/
  classical
  dsimp
  set dStar : ℝ := d uStar with hdStar
  set rStar : ℝ := -uStar / dStar with hrStar
  have hdpos : 0 < dStar := by simpa [hdStar] using d_pos uStar
  have hdne : dStar ≠ 0 := hdpos.ne'

  have hu : uStar = -rStar * dStar := by
    have : rStar * dStar = -uStar := by simp [hrStar, hdne]
    have : uStar = -(rStar * dStar) := by
      simpa using (congrArg Neg.neg this).symm
    simpa [neg_mul] using this

  -- Rewrite `H uStar = 0` in terms of `dStar` and `rStar`.
  have hH1 :
      uStar ^ 2 * dStar + 6 * uStar * dStar ^ 2 + 6 * dStar ^ 3 - uStar - 4 * dStar = 0 := by
    have : uStar ^ 2 * d uStar + 6 * uStar * (d uStar) ^ 2 + 6 * (d uStar) ^ 3 - uStar - 4 * d uStar = 0 := by
      simpa [H, DecreasingG.H] using hH
    simpa [hdStar.symm] using this

  have hsub :
      (rStar ^ 2 - 6 * rStar + 6) * dStar ^ 3 + (rStar - 4) * dStar = 0 := by
    have htmp :
        (rStar * dStar) ^ 2 * dStar + -(6 * (rStar * dStar) * dStar ^ 2) + 6 * dStar ^ 3 +
            rStar * dStar - 4 * dStar = 0 := by
      simpa [hu] using hH1
    have hident :
        (rStar * dStar) ^ 2 * dStar + -(6 * (rStar * dStar) * dStar ^ 2) + 6 * dStar ^ 3 +
            rStar * dStar - 4 * dStar =
          (rStar ^ 2 - 6 * rStar + 6) * dStar ^ 3 + (rStar - 4) * dStar := by
      ring
    simpa [hident] using htmp

  have hfactor : dStar * ((rStar ^ 2 - 6 * rStar + 6) * dStar ^ 2 + (rStar - 4)) = 0 := by
    calc
      dStar * ((rStar ^ 2 - 6 * rStar + 6) * dStar ^ 2 + (rStar - 4)) =
          (rStar ^ 2 - 6 * rStar + 6) * dStar ^ 3 + (rStar - 4) * dStar := by
            ring
      _ = 0 := hsub

  have hbr : (rStar ^ 2 - 6 * rStar + 6) * dStar ^ 2 + (rStar - 4) = 0 := by
    rcases mul_eq_zero.mp hfactor with h0 | h0
    · exfalso
      exact hdne h0
    · exact h0

  have hq_pos : 0 < rStar ^ 2 - 6 * rStar + 6 := by
    have hr : 0 < rStar ∧ rStar < 1 := by
      -- this uses only `uStar < 0`.
      simpa [hdStar, hrStar] using (r_mem_Ioo_of_critical (uStar := uStar) huStar)
    have hlin : 0 < 6 * (1 - rStar) := by nlinarith [hr.2]
    have hsq : 0 ≤ rStar ^ 2 := sq_nonneg rStar
    have : rStar ^ 2 - 6 * rStar + 6 = rStar ^ 2 + 6 * (1 - rStar) := by ring
    simpa [this] using (add_pos_of_nonneg_of_pos hsq hlin)
  have hq_ne : (rStar ^ 2 - 6 * rStar + 6) ≠ 0 := ne_of_gt hq_pos

  have hmul' : dStar ^ 2 * (rStar ^ 2 - 6 * rStar + 6) = (4 - rStar) := by
    -- Rearrange `hbr`.
    have : (rStar ^ 2 - 6 * rStar + 6) * dStar ^ 2 = 4 - rStar := by nlinarith [hbr]
    simpa [mul_comm] using this

  -- Divide by the positive denominator.
  exact (eq_div_iff hq_ne).2 (by simpa [mul_comm] using hmul')

lemma g_eq_ratio_of_H_eq_zero {uStar : ℝ} (huStar : uStar < 0) (hH : H uStar = 0) :
    let dStar := d uStar
    let rStar := -uStar / dStar
    g uStar = rStar * (4 - rStar) * (1 - rStar) ^ 2 / (rStar ^ 2 - 6 * rStar + 6) ^ 2 := by
  /-
  Blueprint algebra:
    - Use the quartic form `g_eq_quartic`.
    - Write `E(u⋆)=d⋆(1-r⋆)` and `u⋆=-r⋆d⋆`.
    - Use `d_sq_eq_of_H_eq_zero` and simplify; a cancellation yields the ratio.
  -/
  classical
  dsimp
  set dStar : ℝ := d uStar with hdStar
  set rStar : ℝ := -uStar / dStar with hrStar
  have hdpos : 0 < dStar := by simpa [hdStar] using d_pos uStar
  have hdne : dStar ≠ 0 := hdpos.ne'

  have hu : uStar = -rStar * dStar := by
    have : rStar * dStar = -uStar := by simp [hrStar, hdne]
    have : uStar = -(rStar * dStar) := by
      simpa using (congrArg Neg.neg this).symm
    simpa [neg_mul] using this

  have hEexpr : E uStar = dStar * (1 - rStar) := by
    have hddef : dStar = E uStar - uStar := by
      simpa [hdStar, d, DecreasingG.d] using rfl
    have hE : E uStar = uStar + dStar := by nlinarith [hddef]
    calc
      E uStar = uStar + dStar := hE
      _ = (-rStar * dStar) + dStar := by simp [hu]
      _ = dStar * (1 - rStar) := by ring

  have hg_form :
      g uStar = dStar ^ 2 * (1 - rStar) ^ 2 * ((3 - 2 * rStar) * dStar ^ 2 - 2) := by
    -- Expand `g` and substitute `E uStar = dStar (1 - rStar)` and `uStar = -rStar dStar`.
    have hEexpr' : DecreasingG.E uStar = dStar * (1 - rStar) := by
      simpa [E] using hEexpr
    unfold g DecreasingG.g
    rw [hEexpr', hu]
    ring_nf

  -- Substitute the expression for `dStar^2` coming from `H uStar = 0`.
  have hd2_expanded :
      (d uStar) ^ 2 =
        (4 - (-uStar / d uStar)) /
          ((-uStar / d uStar) ^ 2 - 6 * (-uStar / d uStar) + 6) := by
    simpa using (d_sq_eq_of_H_eq_zero (uStar := uStar) huStar hH)
  have hr_eq : -uStar / d uStar = rStar := by
    have : rStar = -uStar / d uStar := by
      -- rewrite the denominator using `dStar = d uStar`.
      simpa [hrStar, hdStar] using (rfl : rStar = -uStar / dStar)
    exact this.symm
  have hd_eq : d uStar = dStar := hdStar.symm
  have hd2 : dStar ^ 2 = (4 - rStar) / (rStar ^ 2 - 6 * rStar + 6) := by
    simpa [hd_eq, hr_eq] using hd2_expanded

  have hq_pos : 0 < rStar ^ 2 - 6 * rStar + 6 := by
    have hr : 0 < rStar ∧ rStar < 1 := by
      simpa [hdStar, hrStar] using (r_mem_Ioo_of_critical (uStar := uStar) huStar)
    have hlin : 0 < 6 * (1 - rStar) := by nlinarith [hr.2]
    have hsq : 0 ≤ rStar ^ 2 := sq_nonneg rStar
    have : rStar ^ 2 - 6 * rStar + 6 = rStar ^ 2 + 6 * (1 - rStar) := by ring
    simpa [this] using (add_pos_of_nonneg_of_pos hsq hlin)
  have hq_ne : (rStar ^ 2 - 6 * rStar + 6) ≠ 0 := ne_of_gt hq_pos

  -- Finish by substitution and a rational simplification.
  have hnum :
      (3 - 2 * rStar) * (4 - rStar) - 2 * (rStar ^ 2 - 6 * rStar + 6) = rStar := by
    ring

  -- Use the simplified form for `g` and rewrite with `dStar^2`.
  calc
    g uStar = dStar ^ 2 * (1 - rStar) ^ 2 * ((3 - 2 * rStar) * dStar ^ 2 - 2) := hg_form
    _ = ((4 - rStar) / (rStar ^ 2 - 6 * rStar + 6)) * (1 - rStar) ^ 2 *
          ((3 - 2 * rStar) * ((4 - rStar) / (rStar ^ 2 - 6 * rStar + 6)) - 2) := by
          simp [hd2]
    _ =
        rStar * (4 - rStar) * (1 - rStar) ^ 2 / (rStar ^ 2 - 6 * rStar + 6) ^ 2 := by
          have hq2_ne : (rStar ^ 2 - 6 * rStar + 6) ^ 2 ≠ 0 := pow_ne_zero 2 hq_ne
          -- Clear the final denominator `(... )^2`.
          apply (eq_div_iff hq2_ne).2
          have hpoly :
              ((4 - rStar) / (rStar ^ 2 - 6 * rStar + 6)) * (1 - rStar) ^ 2 *
                    ((3 - 2 * rStar) * ((4 - rStar) / (rStar ^ 2 - 6 * rStar + 6)) - 2) *
                  (rStar ^ 2 - 6 * rStar + 6) ^ 2 =
                (4 - rStar) * (1 - rStar) ^ 2 *
                    ((3 - 2 * rStar) * (4 - rStar) - 2 * (rStar ^ 2 - 6 * rStar + 6)) := by
              -- Introduce `q` so that `field_simp` can see the cancellations in `q^2`.
              set q : ℝ := rStar ^ 2 - 6 * rStar + 6 with hq
              have hq_ne' : q ≠ 0 := by simpa [hq] using hq_ne
              have hq2_ne' : q ^ 2 ≠ 0 := pow_ne_zero 2 hq_ne'
              -- Rewrite the goal in terms of `q` (the `set` already did this).
              field_simp [hq_ne', hq2_ne']
          rw [hpoly]
          simp [hnum]
          ring

/-! ## Rational function bound (imported from the appendix in `main.tex`) -/

lemma ratio_bound {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    r * (4 - r) * (1 - r) ^ 2 / (r ^ 2 - 6 * r + 6) ^ 2 ≤ (1 : ℝ) / 18 := by
  -- See `rational_function_bound/RatioBound.lean`.
  simpa using Numcheck2.ratio_bound (r := r) hr0 hr1

lemma g_critical_le_one_div_18 {uStar : ℝ} (huStar : uStar < 0) (hH : H uStar = 0) :
    g uStar ≤ (1 : ℝ) / 18 := by
  /-
  Blueprint steps:
    - Define r⋆ := -u⋆ / d(u⋆) and show r⋆ ∈ (0,1).
    - Use `g_eq_ratio_of_H_eq_zero` to rewrite `g(u⋆)` as the rational function
      in r⋆.
    - Apply `ratio_bound`.
  -/
  have hr : (0 : ℝ) < (-uStar / d uStar) ∧ (-uStar / d uStar) < 1 := by
    simpa using (r_mem_Ioo_of_critical (uStar := uStar) huStar)
  have hg :
      g uStar =
        (-uStar / d uStar) * (4 - (-uStar / d uStar)) * (1 - (-uStar / d uStar)) ^ 2 /
          ((-uStar / d uStar) ^ 2 - 6 * (-uStar / d uStar) + 6) ^ 2 := by
    simpa using (g_eq_ratio_of_H_eq_zero (uStar := uStar) huStar hH)
  -- Apply the rational bound.
  simpa [hg] using
    (ratio_bound (r := (-uStar / d uStar)) hr.1 hr.2)

/-! ## Main result -/

theorem g_le_one_div_18_of_nonpos {u : ℝ} (hu : u ≤ 0) : g u ≤ (1 : ℝ) / 18 := by
  classical
  by_cases hnonpos : ∀ v, v ≤ (0 : ℝ) → g v ≤ 0
  · have : g u ≤ 0 := hnonpos u hu
    nlinarith
  · have hpos : ∃ v, v ≤ (0 : ℝ) ∧ 0 < g v := by
      -- Extract a witness from the negation of `∀ v≤0, g v ≤ 0`.
      by_contra hpos
      have hnonpos' : ∀ v, v ≤ (0 : ℝ) → g v ≤ 0 := by
        intro v hv
        by_contra hvpos
        have : 0 < g v := lt_of_not_ge hvpos
        exact hpos ⟨v, hv, this⟩
      exact hnonpos hnonpos'
    obtain ⟨uStar, huStarneg, hmax, hcrit⟩ := exists_interior_maximizer_of_exists_pos hpos
    have hH : H uStar = 0 := H_eq_zero_of_critical (u := uStar) hcrit
    have hgstar : g uStar ≤ (1 : ℝ) / 18 := g_critical_le_one_div_18 (uStar := uStar) huStarneg hH
    have hle : g u ≤ g uStar := hmax u hu
    exact le_trans hle hgstar

-- Main.tex naming: “for all u ≤ 0, g(u) ≤ 1/18”.
theorem g_le_one_div_18 {u : ℝ} (hu : u ≤ 0) : g u ≤ (1 : ℝ) / 18 :=
  g_le_one_div_18_of_nonpos hu

end
end UniformBoundOfG
