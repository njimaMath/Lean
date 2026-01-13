/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 174cceb8-ea14-4321-a084-73515e827d79

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
  unfold TruncatedNormalMoments.φ; norm_num [ Real.exp_ne_zero, mul_comm ] ;
  ring

/-- Positivity of the tail integral, hence `tail u ≠ 0`. -/
lemma tail_pos (u : ℝ) : 0 < tail u := by
  -- Standard fact: φ(x) > 0 for all x, and Ici u has positive “mass” under φ.
  -- One route:
  --   show `0 ≤ φ` and `∃ x ∈ Ici u, 0 < φ x`, then use `integral_pos_of_continuous`.
  -- Another route:
  --   compare tail(u) with ∫_{u}^{u+1} φ(x) dx > 0.
  -- The integral of a positive function over an interval is positive.
  have h_pos : 0 < ∫ x in Set.Ici u, Real.exp (-x^2 / 2) := by
    rw [ MeasureTheory.integral_pos_iff_support_of_nonneg ];
    · simp +decide [ Function.support, Real.exp_ne_zero ];
    · exact fun x => Real.exp_nonneg _;
    · exact MeasureTheory.Integrable.integrableOn ( by simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num ) ) );
  unfold TruncatedNormalMoments.tail;
  unfold TruncatedNormalMoments.φ; rw [ MeasureTheory.integral_div ] ; positivity;

lemma tail_ne_zero (u : ℝ) : tail u ≠ 0 := by
  exact (ne_of_gt (tail_pos u))

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Tendsto
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun x : ℝ => (x - u) ^ k * φ x)-/
/-- Boundary term: (x-u)^k * φ(x) → 0 as x → ∞. -/
lemma tendsto_pow_sub_mul_φ_atTop (k : ℕ) (u : ℝ) :
    Tendsto (fun x : ℝ => (x - u)^k * φ x) atTop (𝓝 0) := by
  -- Use that exp(-x^2/2) dominates any polynomial.
  -- There are existing lemmas in Mathlib about `tendsto_pow_mul_exp_neg_sq_atTop`.
  -- You may want to rewrite:
  --   (x-u)^k ≤ C * x^k for x large, and then use known Gaussian decay.
  sorry

/-- Integrability of the relevant integrands on Ici u. -/
lemma integrable_pow_sub_mul_φ (k : ℕ) (u : ℝ) :
    IntegrableOn (fun x : ℝ => (x - u)^k * φ x) (Set.Ici u) := by
  -- Again, polynomial times Gaussian is integrable.
  -- You can use domination by x^k * exp(-x^2/2) and known integrability lemmas.
  -- We'll use the fact that $(x - u)^k \phi(x)$ is integrable on $[u, \infty)$.
  have h_integrable : MeasureTheory.IntegrableOn (fun x => (x - u) ^ k * Real.exp (-x ^ 2 / 2)) (Set.Ici u) := by
    have h_integrable : MeasureTheory.IntegrableOn (fun x => (x - u) ^ k * Real.exp (-x ^ 2 / 2)) (Set.univ : Set ℝ) := by
      field_simp;
      have h_gauss_integrable : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun x => x ^ n * Real.exp (-x ^ 2 / 2)) Set.univ := by
        intro n;
        have := @integrable_rpow_mul_exp_neg_mul_sq;
        simpa [ div_eq_inv_mul ] using this one_half_pos ( show -1 < ( n : ℝ ) by linarith );
      simp_all +decide [ sub_eq_add_neg, add_pow ];
      simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
      exact MeasureTheory.integrable_finset_sum _ fun i hi => by simpa [ mul_assoc, mul_comm, mul_left_comm ] using h_gauss_integrable i |> fun h => h.mul_const ( ( k.choose i : ℝ ) * ( -u ) ^ ( k - i ) ) ;
    exact h_integrable.mono_set <| Set.subset_univ _;
  simp_all +decide [ TruncatedNormalMoments.φ ];
  simpa only [ mul_div ] using h_integrable.div_const _

/-! ### Core recursion for J and μ -/

/-- The integration-by-parts recursion for J:
    for k ≥ 1, J_{k+1}(u) = k * J_{k-1}(u) - u * J_k(u). -/
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
  have h_rec : ∀ a b : ℝ, ∫ x in a..b, (x - u) ^ (k + 1) * φ x = ((k:ℝ) * ∫ x in a..b, (x - u) ^ (k - 1) * φ x) - (u * ∫ x in a..b, (x - u) ^ k * φ x) - ((b - u) ^ k * φ b - (a - u) ^ k * φ a) := by
    intros a b
    have h_parts : ∀ x : ℝ, deriv (fun x => (x - u) ^ k * φ x) x = - (x - u) ^ (k + 1) * φ x + k * (x - u) ^ (k - 1) * φ x - u * (x - u) ^ k * φ x := by
      intro x; rw [ show TruncatedNormalMoments.φ = fun x => Real.exp ( -x ^ 2 / 2 ) / Real.sqrt ( 2 * Real.pi ) from funext fun x => rfl ] ; norm_num [ Real.differentiableAt_exp, Real.sqrt_ne_zero'.mpr Real.pi_pos ] ; ring;
    have h_int_parts : ∫ x in a..b, deriv (fun x => (x - u) ^ k * φ x) x = (b - u) ^ k * φ b - (a - u) ^ k * φ a := by
      rw [ intervalIntegral.integral_deriv_eq_sub ];
      · exact fun x hx => DifferentiableAt.mul ( DifferentiableAt.pow ( differentiableAt_id.sub_const u ) _ ) ( by exact DifferentiableAt.div ( DifferentiableAt.exp ( by norm_num ) ) ( differentiableAt_const _ ) ( by positivity ) );
      · rw [ show deriv _ = _ from funext h_parts ];
        apply_rules [ Continuous.intervalIntegrable ];
        apply_rules [ Continuous.sub, Continuous.add, Continuous.mul, continuous_id, continuous_const, Continuous.pow, continuous_const ];
        · continuity;
        · fun_prop;
        · fun_prop;
        · fun_prop;
    rw [ ← h_int_parts, intervalIntegral.integral_congr fun x _ => h_parts x ];
    rw [ intervalIntegral.integral_sub, intervalIntegral.integral_add ] <;> norm_num [ mul_assoc ];
    · exact Continuous.intervalIntegrable ( by exact Continuous.neg ( by exact Continuous.mul ( by continuity ) ( by exact Continuous.div_const ( Real.continuous_exp.comp <| by continuity ) _ ) ) ) _ _;
    · exact Continuous.intervalIntegrable ( by exact Continuous.mul continuous_const <| Continuous.mul ( by continuity ) <| by exact Continuous.div_const ( Real.continuous_exp.comp <| by continuity ) _ ) _ _;
    · apply_rules [ Continuous.intervalIntegrable ];
      exact Continuous.add ( Continuous.neg ( Continuous.mul ( Continuous.pow ( continuous_id.sub continuous_const ) _ ) ( by exact Continuous.div_const ( Real.continuous_exp.comp <| by continuity ) _ ) ) ) ( Continuous.mul continuous_const <| Continuous.mul ( Continuous.pow ( continuous_id.sub continuous_const ) _ ) ( by exact Continuous.div_const ( Real.continuous_exp.comp <| by continuity ) _ ) );
    · exact Continuous.intervalIntegrable ( by exact Continuous.mul continuous_const <| by exact Continuous.mul ( by continuity ) <| by exact Continuous.div_const ( Real.continuous_exp.comp <| by continuity ) _ ) _ _;
  -- Let's choose any two points $a$ and $b$ such that $a < b$.
  have h_lim : Filter.Tendsto (fun b => ∫ x in u..b, (x - u) ^ (k + 1) * φ x) Filter.atTop (nhds (∫ x in Set.Ici u, (x - u) ^ (k + 1) * φ x)) ∧ Filter.Tendsto (fun b => ∫ x in u..b, (x - u) ^ (k - 1) * φ x) Filter.atTop (nhds (∫ x in Set.Ici u, (x - u) ^ (k - 1) * φ x)) ∧ Filter.Tendsto (fun b => ∫ x in u..b, (x - u) ^ k * φ x) Filter.atTop (nhds (∫ x in Set.Ici u, (x - u) ^ k * φ x)) := by
    have h_lim : ∀ {f : ℝ → ℝ}, MeasureTheory.IntegrableOn f (Set.Ici u) → Filter.Tendsto (fun b => ∫ x in u..b, f x) Filter.atTop (nhds (∫ x in Set.Ici u, f x)) := by
      intro f hf; rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ] ; apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ] ;
      · exact hf.mono_set <| Set.Ioi_subset_Ici_self;
      · exact Filter.tendsto_id;
    exact ⟨ h_lim <| integrable_pow_sub_mul_φ _ _, h_lim <| integrable_pow_sub_mul_φ _ _, h_lim <| integrable_pow_sub_mul_φ _ _ ⟩;
  -- Let's choose any two points $a$ and $b$ such that $a < b$ and apply the integration by parts formula.
  have h_lim_parts : Filter.Tendsto (fun b => ((b - u) ^ k * φ b - (u - u) ^ k * φ u)) Filter.atTop (nhds 0) := by
    -- We'll use the fact that $(b - u)^k e^{-b^2/2}$ tends to $0$ as $b$ tends to infinity.
    have h_exp : Filter.Tendsto (fun b => (b - u) ^ k * Real.exp (-b ^ 2 / 2)) Filter.atTop (nhds 0) := by
      have h_lim_zero : Filter.Tendsto (fun b => b ^ k * Real.exp (-b ^ 2 / 2)) Filter.atTop (nhds 0) := by
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
        refine' squeeze_zero_norm' _ this;
        filter_upwards [ Filter.eventually_ge_atTop 2 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; nlinarith;
      have h_lim_zero : Filter.Tendsto (fun b => ((b - u) / b) ^ k * b ^ k * Real.exp (-b ^ 2 / 2)) Filter.atTop (nhds 0) := by
        have h_lim_zero : Filter.Tendsto (fun b => ((b - u) / b) ^ k) Filter.atTop (nhds 1) := by
          have h_lim_zero : Filter.Tendsto (fun b => (1 - u / b) ^ k) Filter.atTop (nhds 1) := by
            exact le_trans ( Filter.Tendsto.pow ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) _ ) ( by norm_num );
          refine h_lim_zero.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with b hb using by rw [ sub_div, div_self hb.ne' ] );
        simpa [ mul_assoc ] using h_lim_zero.mul ‹Filter.Tendsto ( fun b : ℝ => b ^ k * Real.exp ( -b ^ 2 / 2 ) ) Filter.atTop ( 𝓝 0 ) ›;
      refine h_lim_zero.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with b hb using by rw [ div_pow, div_mul_cancel₀ _ ( pow_ne_zero _ hb.ne' ) ] );
    convert h_exp.div_const ( Real.sqrt ( 2 * Real.pi ) ) using 2 <;> norm_num [ TruncatedNormalMoments.φ ] ; ring;
    rw [ zero_pow ( by linarith ), MulZeroClass.mul_zero, sub_zero ];
  exact tendsto_nhds_unique h_lim.1 ( by simpa [ h_rec ] using Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.mul h_lim.2.1 ) ( tendsto_const_nhds.mul h_lim.2.2 ) ) h_lim_parts )

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
  simpa [d, μ_zero, μ_one, Nat.sub_self, one_mul, sub_eq_add_neg] using hrec

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
            simp [μ_one, μ_two, d]
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
