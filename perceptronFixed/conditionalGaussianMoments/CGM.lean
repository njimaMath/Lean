/-
The following was proved by Aristotle:

- lemma deriv_φ (x : ℝ) : deriv φ x = -x * φ x

- lemma tail_pos (u : ℝ) : 0 < tail u

- lemma integrable_pow_sub_mul_φ (k : ℕ) (u : ℝ) :
    IntegrableOn (fun x : ℝ => (x - u)^k * φ x) (Set.Ici u)

- lemma J_rec (k : ℕ) (u : ℝ) (hk : 1 ≤ k) :
    J (k + 1) u = (k : ℝ) * J (k - 1) u - u * J k u

- lemma μ_rec (k : ℕ) (u : ℝ) (hk : 1 ≤ k) :
    μ (k + 1) u = (k : ℝ) * μ (k - 1) u - u * μ k u
-/

import Mathlib


open scoped BigOperators Topology

open MeasureTheory

namespace TruncatedNormalMoments

noncomputable section

/-! ### Basic definitions: standard normal density, tail, truncated moments -/

/-- Standard normal density φ(x) = exp(-x^2/2) / sqrt(2π). -/
def φ (x : ℝ) : ℝ :=
  Real.exp (-(x^2) / 2) / Real.sqrt (2 * Real.pi)

/-- Tail probability (as an integral under Lebesgue measure): ∫_{x≥u} φ(x) dx. -/
def tail (u : ℝ) : ℝ :=
  ∫ x in Set.Ici u, φ x

/-- Numerator for the kth shifted moment on the tail: J_k(u) = ∫_{x≥u} (x-u)^k φ(x) dx. -/
def J (k : ℕ) (u : ℝ) : ℝ :=
  ∫ x in Set.Ici u, (x - u)^k * φ x

/-- Conditional moments μ_k(u) = E[(X-u)^k | X≥u] in ratio form. -/
def μ (k : ℕ) (u : ℝ) : ℝ :=
  J k u / tail u

/-- Mean excess d(u) = μ_1(u). -/
def d (u : ℝ) : ℝ :=
  μ 1 u

/-! ### Analytic lemmas needed for the integration-by-parts recursion

  The next block is where the real analysis lives.
  You can keep them as `sorry` while building the algebraic part, then fill them in one by one.

  What you will need (conceptually):
    • derivative identity: (deriv φ) x = -x * φ x
    • boundary vanishing: (x-u)^k * φ x → 0 as x → ∞
    • an integration-by-parts lemma for improper integrals on [u,∞)

  In Mathlib, the cleanest approach is usually:
    • prove the identity on [u, b] via `intervalIntegral.integration_by_parts`-style lemmas
    • pass to the limit b → ∞ using dominated convergence / integrability
    • rewrite `∫ x in Ici u` as an improper interval integral
-/

/-- Derivative identity for the standard normal density: φ' = -x φ. -/
lemma deriv_φ (x : ℝ) : deriv φ x = -x * φ x := by
  -- Fill in with calculus:
  --   φ(x) = c * exp (-(x^2)/2), c = 1/sqrt(2π).
  -- Use:
  --   `by simp [φ]` will not finish by itself; you will likely need `simp` + `ring`
  --   and lemmas about `deriv` of `Real.exp` and polynomials.
  unfold TruncatedNormalMoments.φ;
  norm_num ; ring

/-- Positivity of the tail integral, hence `tail u ≠ 0`. -/
lemma tail_pos (u : ℝ) : 0 < tail u := by
  -- Standard fact: φ(x) > 0 for all x, and Ici u has positive “mass” under φ.
  -- One route:
  --   show `0 ≤ φ` and `∃ x ∈ Ici u, 0 < φ x`, then use `integral_pos_of_continuous`.
  -- Another route:
  --   compare tail(u) with ∫_{u}^{u+1} φ(x) dx > 0.
  refine' lt_of_le_of_ne _ ( Ne.symm _ );
  · exact MeasureTheory.integral_nonneg fun x => by exact div_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ );
  · refine' ne_of_gt _;
    refine' ( lt_of_lt_of_le _ ( MeasureTheory.setIntegral_mono_set _ _ _ ) );
    rotate_left;
    exact Set.Icc u ( u + 1 );
    · -- The Gaussian function is integrable over the entire real line.
      have h_gauss_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x^2 / 2)) Set.univ := by
        simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num ) );
      exact MeasureTheory.IntegrableOn.mono_set ( by exact MeasureTheory.Integrable.div_const ( h_gauss_integrable.mono_set <| Set.subset_univ _ ) _ ) <| Set.subset_univ _;
    · exact Filter.Eventually.of_forall fun x => div_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ );
    · exact MeasureTheory.ae_of_all _ fun x hx => hx.1;
    · rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
      · exact lt_of_lt_of_le ( by norm_num ) ( MeasureTheory.measure_mono ( show Function.support TruncatedNormalMoments.φ ⊇ Set.Icc u ( u + 1 ) from fun x hx => ne_of_gt <| div_pos ( Real.exp_pos _ ) <| Real.sqrt_pos.mpr <| by positivity ) );
      · exact Filter.Eventually.of_forall fun x => div_nonneg ( Real.exp_nonneg _ ) ( Real.sqrt_nonneg _ );
      · exact Continuous.integrableOn_Icc ( by exact Continuous.div_const ( Real.continuous_exp.comp <| by continuity ) _ )

lemma tail_ne_zero (u : ℝ) : tail u ≠ 0 := by
  exact (ne_of_gt (tail_pos u))

/-- Boundary term: (x-u)^k * φ(x) → 0 as x → ∞. -/
lemma tendsto_pow_sub_mul_φ_atTop (k : ℕ) (u : ℝ) :
    Filter.Tendsto (fun x : ℝ => (x - u)^k * φ x) Filter.atTop (𝓝 0) := by
  -- We'll use the fact that φ(x) = exp(-x^2/2) / sqrt(2π) to simplify the expression.
  suffices h_suff_top : Filter.Tendsto (fun x => (x - u)^k * Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) Filter.atTop (nhds 0) by
    convert h_suff_top using 2
    unfold φ
    ring
  -- We'll use the fact that exp(-x^2/2) decays faster than any polynomial grows.
  have h_exp_decay : Filter.Tendsto (fun x : ℝ => x^k * Real.exp (-x^2 / 2)) Filter.atTop (nhds 0) := by
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
    refine' squeeze_zero_norm' _ this
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx using by
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      nlinarith
  -- We can factor out (x - u)^k from the limit expression.
  have h_factor : Filter.Tendsto (fun x : ℝ => ((x - u) / x)^k * x^k * Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) Filter.atTop (nhds 0) := by
    -- We'll use the fact that (x - u) / x → 1 as x → ∞.
    have h_frac : Filter.Tendsto (fun x : ℝ => (x - u) / x) Filter.atTop (nhds 1) := by
      norm_num [sub_div]
      exact le_trans (Filter.Tendsto.sub (tendsto_const_nhds.congr' (by filter_upwards [Filter.eventually_ne_atTop 0] with x hx; aesop)) (tendsto_const_nhds.div_atTop Filter.tendsto_id)) (by norm_num)
    simpa [mul_assoc] using Filter.Tendsto.div_const (Filter.Tendsto.mul (h_frac.pow k) h_exp_decay) _
  refine h_factor.congr' (by filter_upwards [Filter.eventually_gt_atTop 0] with x hx using by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hx.ne')])

/-- Integrability of the relevant integrands on Ici u. -/
lemma integrable_pow_sub_mul_φ (k : ℕ) (u : ℝ) :
    IntegrableOn (fun x : ℝ => (x - u)^k * φ x) (Set.Ici u) := by
  -- Again, polynomial times Gaussian is integrable.
  -- You can use domination by x^k * exp(-x^2/2) and known integrability lemmas.
  -- The integral of $(x-u)^k \phi(x)$ over $[u, \infty)$ is finite because $\phi(x)$ decays exponentially.
  have h_integrable : MeasureTheory.IntegrableOn (fun x => (x - u)^k * Real.exp (-x^2 / 2)) (Set.Ici u) := by
    -- We'll use the fact that $(x - u)^k e^{-x^2 / 2}$ is integrable because it's the product of a polynomial and a Gaussian function.
    have h_integrable : MeasureTheory.IntegrableOn (fun x => (x - u)^k * Real.exp (-x^2 / 2)) (Set.univ : Set ℝ) := by
      have h_gauss_integrable : ∀ p : Polynomial ℝ, MeasureTheory.IntegrableOn (fun x => p.eval x * Real.exp (-x^2 / 2)) (Set.univ : Set ℝ) := by
        intro p;
        have := @integrable_rpow_mul_exp_neg_mul_sq;
        simp_all +decide [ Polynomial.eval_eq_sum_range ];
        simp_all +decide [ div_eq_inv_mul, Finset.sum_mul _ _ _ ];
        exact MeasureTheory.integrable_finset_sum _ fun i hi => by simpa [ mul_assoc ] using MeasureTheory.Integrable.const_mul ( this ( show 0 < ( 2⁻¹ : ℝ ) by norm_num ) ( show -1 < ( i : ℝ ) by linarith ) ) ( p.coeff i ) ;
      convert h_gauss_integrable ( ( Polynomial.X - Polynomial.C u ) ^ k ) using 1 ; norm_num;
    exact h_integrable.mono_set <| Set.subset_univ _;
  simp_all +decide [ TruncatedNormalMoments.φ ];
  simpa only [ mul_div ] using h_integrable.div_const _

/-! ### Core recursion for J and μ -/

/- The integration-by-parts recursion for J:
    for k ≥ 1, J_{k+1}(u) = k * J_{k-1}(u) - u * J_k(u). -/
noncomputable section AristotleLemmas

/-
The function (x-u)^k * φ(x) tends to 0 as x goes to infinity.
-/
lemma TruncatedNormalMoments.tendsto_pow_sub_mul_phi_atTop (k : ℕ) (u : ℝ) :
    Filter.Tendsto (fun x => (x - u) ^ k * TruncatedNormalMoments.φ x) Filter.atTop (nhds 0) := by
      -- We'll use the fact that $\phi(x) = \frac{e^{-x^2/2}}{\sqrt{2\pi}}$ to simplify the expression.
      suffices h_suff_top : Filter.Tendsto (fun x => (x - u)^k * Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) Filter.atTop (nhds 0) by
        convert h_suff_top using 2 ; unfold TruncatedNormalMoments.φ ; ring;
      -- We'll use the fact that $e^{-x^2 / 2}$ decays faster than any polynomial grows. Specifically, we have $\lim_{x \to \infty} x^k e^{-x^2 / 2} = 0$ for any $k$.
      have h_exp_decay : Filter.Tendsto (fun x : ℝ => x^k * Real.exp (-x^2 / 2)) Filter.atTop (nhds 0) := by
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
        refine' squeeze_zero_norm' _ this;
        filter_upwards [ Filter.eventually_ge_atTop 2 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; nlinarith;
      -- We can factor out $(x - u)^k$ from the limit expression.
      have h_factor : Filter.Tendsto (fun x : ℝ => ((x - u) / x)^k * x^k * Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $(x - u) / x \to 1$ as $x \to \infty$.
        have h_frac : Filter.Tendsto (fun x : ℝ => (x - u) / x) Filter.atTop (nhds 1) := by
          norm_num [ sub_div ];
          exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with x hx; aesop ) ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( by norm_num );
        simpa [ mul_assoc ] using Filter.Tendsto.div_const ( Filter.Tendsto.mul ( h_frac.pow k ) h_exp_decay ) _;
      refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ div_pow, div_mul_cancel₀ _ ( pow_ne_zero _ hx.ne' ) ] )

/-
Compute the derivative of (x-u)^k * φ(x).
-/
lemma TruncatedNormalMoments.deriv_pow_sub_mul_phi (k : ℕ) (u x : ℝ) (hk : 1 ≤ k) :
    deriv (fun x => (x - u) ^ k * TruncatedNormalMoments.φ x) x =
    k * (x - u) ^ (k - 1) * TruncatedNormalMoments.φ x - x * (x - u) ^ k * TruncatedNormalMoments.φ x := by
      unfold TruncatedNormalMoments.φ;
      norm_num ; ring

/-
The integral of the derivative of (x-u)^k φ(x) over [u, ∞) is 0.
-/
lemma TruncatedNormalMoments.integral_deriv_pow_sub_mul_phi_eq_zero (k : ℕ) (u : ℝ) (hk : 1 ≤ k) :
    ∫ x in Set.Ici u, deriv (fun x => (x - u) ^ k * TruncatedNormalMoments.φ x) x = 0 := by
      -- By the Fundamental Theorem of Calculus, the integral of the derivative of a function over an interval is the function evaluated at the upper limit minus the function evaluated at the lower limit.
      have h_ftc : Filter.Tendsto (fun b => ∫ x in u..b, deriv (fun x => (x - u) ^ k * (TruncatedNormalMoments.φ x)) x) Filter.atTop (nhds (∫ x in Set.Ioi u, deriv (fun x => (x - u) ^ k * (TruncatedNormalMoments.φ x)) x)) := by
        apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
        · -- Since the derivative is a linear combination of integrable terms, it is integrable on Ici u.
          have h_deriv_integrable : MeasureTheory.IntegrableOn (fun x => k * (x - u) ^ (k - 1) * TruncatedNormalMoments.φ x - x * (x - u) ^ k * TruncatedNormalMoments.φ x) (Set.Ici u) := by
            refine' MeasureTheory.Integrable.sub _ _;
            · have := TruncatedNormalMoments.integrable_pow_sub_mul_φ ( k - 1 ) u;
              simpa only [ mul_assoc ] using this.const_mul _;
            · have h_integrable : ∀ p : ℕ, MeasureTheory.IntegrableOn (fun x => x ^ p * TruncatedNormalMoments.φ x) (Set.Ici u) := by
                -- The integral of $x^p \exp(-x^2/2)$ over the entire real line is finite, which implies that $x^p \exp(-x^2/2)$ is integrable on $[u, \infty)$.
                have h_integrable : ∀ p : ℕ, MeasureTheory.IntegrableOn (fun x => x ^ p * Real.exp (-x ^ 2 / 2)) Set.univ := by
                  intro p;
                  have := @integrable_rpow_mul_exp_neg_mul_sq;
                  simpa [ div_eq_inv_mul ] using this one_half_pos ( show -1 < ( p : ℝ ) by linarith );
                intro p; specialize h_integrable p; simp_all +decide [ TruncatedNormalMoments.φ ];
                simpa only [ mul_div ] using MeasureTheory.Integrable.integrableOn ( h_integrable.div_const _ );
              -- We can expand $(x - u)^k$ using the binomial theorem.
              have h_expand : ∀ x : ℝ, x * (x - u) ^ k * TruncatedNormalMoments.φ x = ∑ j ∈ Finset.range (k + 1), Nat.choose k j * (-u) ^ (k - j) * x ^ (j + 1) * TruncatedNormalMoments.φ x := by
                intro x; rw [ sub_eq_add_neg, add_pow ] ; ring;
                simp +decide only [mul_assoc, Finset.mul_sum _ _ _, mul_comm, mul_left_comm];
              simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
              exact MeasureTheory.integrable_finset_sum _ fun i hi => MeasureTheory.Integrable.const_mul ( MeasureTheory.Integrable.const_mul ( h_integrable _ ) _ ) _;
          refine' h_deriv_integrable.mono_set ( Set.Ioi_subset_Ici_self ) |> fun h => h.congr_fun _ measurableSet_Ioi;
          intro x hx; simp +decide [ TruncatedNormalMoments.deriv_pow_sub_mul_phi _ _ _ hk ] ;
        · exact Filter.tendsto_id;
      -- By the Fundamental Theorem of Calculus, we know that the integral of the derivative of a function over an interval is the function evaluated at the upper limit minus the function evaluated at the lower limit.
      have h_ftc_eval : ∀ b > u, ∫ x in u..b, deriv (fun x => (x - u) ^ k * (TruncatedNormalMoments.φ x)) x = (b - u) ^ k * (TruncatedNormalMoments.φ b) - (u - u) ^ k * (TruncatedNormalMoments.φ u) := by
        intros b hb;
        rw [ intervalIntegral.integral_deriv_eq_sub ];
        · exact fun x hx => DifferentiableAt.mul ( DifferentiableAt.pow ( differentiableAt_id.sub_const _ ) _ ) ( by exact DifferentiableAt.div ( DifferentiableAt.exp ( by norm_num ) ) ( differentiableAt_const _ ) ( by positivity ) );
        · apply_rules [ Continuous.intervalIntegrable ];
          unfold TruncatedNormalMoments.φ;
          fun_prop;
      rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ];
      exact tendsto_nhds_unique h_ftc ( Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop u ] with b hb; rw [ h_ftc_eval b hb ] ) ( by simpa [ show k ≠ 0 by linarith ] using TruncatedNormalMoments.tendsto_pow_sub_mul_phi_atTop k u ) )

end AristotleLemmas

lemma J_rec (k : ℕ) (u : ℝ) (hk : 1 ≤ k) :
    J (k + 1) u = (k : ℝ) * J (k - 1) u - u * J k u := by
  /-
    Proof sketch to formalize:

    Start from:
      J_{k+1}(u) = ∫_{x≥u} (x-u)^(k+1) φ(x) dx
                = ∫_{x≥u} (x-u)^k * ((x-u) φ(x)) dx.

    Use φ' = -x φ, so x φ = -φ'. Hence:
      (x-u) φ = x φ - u φ = -φ' - u φ.

    Therefore:
      integrand = (x-u)^k * (-(φ') - u φ)
                = -(x-u)^k * (φ') - u * (x-u)^k * φ.

    So:
      J_{k+1} = - ∫ (x-u)^k * (φ')  - u * J_k.

    For the first integral, integrate by parts on [u,∞):
      -∫ h * φ' = -[h φ]_{u}^{∞} + ∫ h' φ.

    Here h(x) = (x-u)^k, so h(u) = 0 when k ≥ 1.
    The boundary at ∞ vanishes by `tendsto_pow_sub_mul_φ_atTop`.
    Also h'(x) = k * (x-u)^(k-1).
    This gives:
      -∫ h φ' = k * J_{k-1}.

    Combine:
      J_{k+1} = k * J_{k-1} - u * J_k.
  -/
  have := TruncatedNormalMoments.integral_deriv_pow_sub_mul_phi_eq_zero k u hk;
  -- Apply the linearity of the integral to split the integral into two parts.
  have h_split : ∫ x in Set.Ici u, deriv (fun x => (x - u)^k * TruncatedNormalMoments.φ x) x = ∫ x in Set.Ici u, (k * (x - u)^(k - 1) * TruncatedNormalMoments.φ x) - (x * (x - u)^k * TruncatedNormalMoments.φ x) := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun x hx => by rw [ TruncatedNormalMoments.deriv_pow_sub_mul_phi k u x hk ] ;
  rw [ MeasureTheory.integral_sub ] at h_split;
  · -- Apply the linearity of the integral to split the integral into two parts and simplify.
    have h_split : ∫ x in Set.Ici u, x * (x - u)^k * TruncatedNormalMoments.φ x = ∫ x in Set.Ici u, (x - u)^(k + 1) * TruncatedNormalMoments.φ x + u * (x - u)^k * TruncatedNormalMoments.φ x := by
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun x hx => by ring;
    rw [ MeasureTheory.integral_add ] at h_split;
    · norm_num [ mul_assoc, MeasureTheory.integral_const_mul ] at * ; linarith!;
    · exact TruncatedNormalMoments.integrable_pow_sub_mul_φ _ _;
    · have := TruncatedNormalMoments.integrable_pow_sub_mul_φ k u;
      simpa only [ mul_assoc ] using this.const_mul u;
  · have := TruncatedNormalMoments.integrable_pow_sub_mul_φ ( k - 1 ) u;
    simpa only [ mul_assoc ] using this.const_mul _;
  · have h_integrable : MeasureTheory.IntegrableOn (fun x => (x - u) ^ (k + 1) * TruncatedNormalMoments.φ x) (Set.Ici u) ∧ MeasureTheory.IntegrableOn (fun x => (x - u) ^ k * TruncatedNormalMoments.φ x) (Set.Ici u) := by
      exact ⟨ TruncatedNormalMoments.integrable_pow_sub_mul_φ _ _, TruncatedNormalMoments.integrable_pow_sub_mul_φ _ _ ⟩;
    convert h_integrable.1.add ( h_integrable.2.const_mul u ) using 2 ; ring;
    norm_num ; ring;
    norm_num

/-- Convert the J recursion into the μ recursion by dividing by tail(u). -/
lemma μ_rec (k : ℕ) (u : ℝ) (hk : 1 ≤ k) :
    μ (k + 1) u = (k : ℝ) * μ (k - 1) u - u * μ k u := by
  have ht : tail u ≠ 0 := tail_ne_zero u
  -- expand μ, use J_rec, and simplify divisions
  -- `field_simp [μ, ht]` is usually the right tool here.
  simp [μ, J_rec k u hk, ht, div_eq_mul_inv, mul_add, add_mul, sub_eq_add_neg]  -- likely not enough
  -- finish with `ring` after `field_simp` in the actual proof
  ring

/-! ### Base moments μ₀, μ₁ and the explicit formulas for μ₂, μ₃, μ₄ -/

/-- J₀(u) = tail(u). -/
lemma J_zero (u : ℝ) : J 0 u = tail u := by
  simp [J, tail, φ]

/-- μ₀(u) = 1. -/
lemma μ_zero (u : ℝ) : μ 0 u = 1 := by
  have ht : tail u ≠ 0 := tail_ne_zero u
  -- μ 0 u = J 0 u / tail u = tail u / tail u
  simp [μ, J_zero, ht]

/-- μ₁(u) = d(u) by definition. -/
lemma μ_one (u : ℝ) : μ 1 u = d u := by
  rfl

/-- μ₂(u) = 1 - u * d(u). -/
lemma μ_two (u : ℝ) : μ 2 u = 1 - u * d u := by
  -- use μ_rec with k = 1:
  -- μ_2 = 1 * μ_0 - u * μ_1
  have hrec : μ (1 + 1) u = (1 : ℝ) * μ (1 - 1) u - u * μ 1 u := by
    simpa using μ_rec 1 u (by decide : (1 : ℕ) ≤ 1)
  -- simplify
  -- note: (1 - 1 : ℕ) = 0
  simpa [d, μ_zero, Nat.sub_self, one_mul, sub_eq_add_neg] using hrec

/-- μ₃(u) = (u^2 + 2) * d(u) - u. -/
lemma μ_three (u : ℝ) : μ 3 u = (u^2 + 2) * d u - u := by
  -- μ_3 = 2 * μ_1 - u * μ_2
  have hrec : μ (2 + 1) u = (2 : ℝ) * μ (2 - 1) u - u * μ 2 u := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (μ_rec 2 u (by decide : (1 : ℕ) ≤ 2))
  -- Substitute μ_2 and simplify
  -- After rewriting, use `ring` or `nlinarith`.
  -- The target is:
  --   2*d - u*(1 - u*d) = (u^2+2)*d - u
  -- which is pure algebra.
  calc
    μ 3 u
        = (2 : ℝ) * μ 1 u - u * μ 2 u := by
            -- from hrec, and 2-1=1
            simpa using hrec
    _   = (2 : ℝ) * d u - u * (1 - u * d u) := by
            rw [μ_one, μ_two]
    _   = (u^2 + 2) * d u - u := by
            ring

/-- μ₄(u) = u^2 + 3 - u * (u^2 + 5) * d(u). -/
lemma μ_four (u : ℝ) : μ 4 u = u^2 + 3 - u * (u^2 + 5) * d u := by
  -- μ_4 = 3 * μ_2 - u * μ_3
  have hrec : μ (3 + 1) u = (3 : ℝ) * μ (3 - 1) u - u * μ 3 u := by
    simpa using (μ_rec 3 u (by decide : (1 : ℕ) ≤ 3))
  -- 3-1=2
  calc
    μ 4 u
        = (3 : ℝ) * μ 2 u - u * μ 3 u := by
            simpa using hrec
    _   = (3 : ℝ) * (1 - u * d u) - u * ((u^2 + 2) * d u - u) := by
            simp [μ_two, μ_three]
    _   = u^2 + 3 - u * (u^2 + 5) * d u := by
            ring

end

end TruncatedNormalMoments
