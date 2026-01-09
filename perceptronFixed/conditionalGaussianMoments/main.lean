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
  sorry

/-- Positivity of the tail integral, hence `tail u ≠ 0`. -/
lemma tail_pos (u : ℝ) : 0 < tail u := by
  -- Standard fact: φ(x) > 0 for all x, and Ici u has positive “mass” under φ.
  -- One route:
  --   show `0 ≤ φ` and `∃ x ∈ Ici u, 0 < φ x`, then use `integral_pos_of_continuous`.
  -- Another route:
  --   compare tail(u) with ∫_{u}^{u+1} φ(x) dx > 0.
  sorry

lemma tail_ne_zero (u : ℝ) : tail u ≠ 0 := by
  exact (ne_of_gt (tail_pos u))

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
  sorry


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
  sorry

/-- Convert the J recursion into the μ recursion by dividing by tail(u). -/
lemma μ_rec (k : ℕ) (u : ℝ) (hk : 1 ≤ k) :
    μ (k + 1) u = (k : ℝ) * μ (k - 1) u - u * μ k u := by
  have ht : tail u ≠ 0 := tail_ne_zero u
  -- expand μ, use J_rec, and simplify divisions
  -- `field_simp [μ, ht]` is usually the right tool here.
  simp [μ, J_rec k u hk, ht, div_eq_mul_inv, mul_add, add_mul, sub_eq_add_neg]  -- likely not enough
  -- finish with `ring` after `field_simp` in the actual proof
  sorry


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
