import Mathlib

/-!
# LEAN4 FOR REAL ANALYSIS

This file is a single-file "book manuscript" that follows the integrated
blueprint in `real_analysis/blueprint.txt`.

House style used here:
- We keep the text mostly in Lean comments (`/-! ... -/`), so this file can be
  read top-to-bottom like a book.
- We interleave short, runnable Lean snippets as examples and templates.
- For early and mid-level material we provide concrete proofs.
- For advanced chapters we keep reliable scaffolds and proof-shape templates,
  so the file stays stable as a teaching artifact.

The goal is not to compress everything into shortest code; the goal is to make
the transition from textbook analysis to Mathlib idioms explicit.
-/

set_option autoImplicit false

open scoped BigOperators Topology
open Filter Set

namespace RealAnalysisBook

/-!
## 0. Book Goals, Audience, and House Style

Audience:
- Readers already know standard undergraduate real analysis.
- Readers want to formalize analysis in Lean4 + Mathlib.
- Lean background is not assumed.

Core goals:
1. Learn Mathlib idioms for real analysis statements.
2. Learn stable proof engineering habits.
3. Learn how to search for and reuse existing lemmas.

Two intentional proof modes:
1. API mode: short, robust proofs using existing lemmas.
2. Definition mode: unfold definitions and run epsilon-style arguments.

Learning loop repeated throughout:
1. One target theorem with one new pattern/API.
2. Informal mathematical proof idea.
3. Lean implementation (often API-first).
4. Tooling notes (`simp`, `rw`, `calc`, search habits, etc.).
5. Exercises using the same pattern.
-/

/-!
# PART I. GETTING READY TO DO ANALYSIS IN MATHLIB

## Chapter 1. Setup and Reading Mathlib
-/

section Chapter01

/-!
### 1.1 First file and first compilation

Target: tiny arithmetic goals in `Nat` and `Int`.
Tools: `by`, `simp`, `norm_num`.
-/

example : (2 : Nat) + 3 = 5 := by
  norm_num

example : (7 : Int) - 4 = 3 := by
  norm_num

example : (3 : Nat) + 0 = 3 := by
  simp

/-!
### 1.2 Reading types as documentation

Core commands:
- `#check`: inspect a declaration's type.
- `#print`: inspect definition/equation lemmas.

Habit: before proving, inspect candidate lemmas and namespaces.
-/

-- #check Nat.add_assoc
-- #check add_zero
-- #check zero_le

example (x : Real) : x + 0 = x := by
  simp

example (x : Real) : x * 1 = x := by
  simp

/-!
### 1.3 Structuring files with `section` and local variables

Target pattern: rewrite under hypotheses.
-/

example {a b c : Real} (h : a = b) : a + c = b + c := by
  rw [h]

example {f : Real -> Real} {a b : Real} (h : a = b) : f a = f b := by
  rw [h]

end Chapter01

/-!
## Chapter 2. Core Lean Mechanics Used Every Day
-/

section Chapter02

/-!
### 2.1 Definitional equality and `rfl`
-/

example (n : Nat) : Nat.succ n = n + 1 := by
  rfl

example (x : Real) : (fun t => t) x = x := by
  rfl

/-!
### 2.2 Simplification and induction

We demonstrate the proof pattern "induction + simp".
-/

example (n : Nat) : (∑ _i ∈ Finset.range n, (1 : Nat)) = n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp

/-!
### 2.3 Proofs as functions (`->`, `forall`)
-/

example (P Q : Prop) : P -> Q -> P := by
  intro hP _hQ
  exact hP

example (α : Type) (P : α -> Prop) (a : α) : (forall x, P x) -> P a := by
  intro hAll
  exact hAll a

/-!
### 2.4 Conjunction, disjunction, existence as data
-/

example (P Q : Prop) : P -> Q -> P ∧ Q := by
  intro hP hQ
  constructor
  · exact hP
  · exact hQ

example (P Q : Prop) : P ∧ Q -> Q ∧ P := by
  intro h
  rcases h with ⟨hP, hQ⟩
  exact ⟨hQ, hP⟩

example : Exists fun n : Nat => n + 1 = 4 := by
  exact ⟨3, by decide⟩

/-!
### 2.5 Equality reasoning with `rw` and `calc`
-/

example {a b c : Real} (h1 : a = b) (h2 : b = c) : a = c := by
  calc
    a = b := h1
    _ = c := h2

example {a b c : Real} (h : a <= b) : a + c <= b + c := by
  linarith

/-!
### 2.6 Case splits and negation hygiene
-/

example (x : Real) : x = 0 ∨ x ≠ 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr hx

example (P : Prop) (h : ¬¬P) : P := by
  by_contra hP
  exact h hP

example (x : Real) : ¬ (x < 0 ∨ x > 0) -> x = 0 := by
  intro h
  push_neg at h
  exact le_antisymm h.2 h.1

end Chapter02

/-!
# PART II. ALGEBRA, ORDER, AND THE REAL LINE

## Chapter 3. Automation for Algebra and Inequalities
-/

section Chapter03

/-! ### 3.1 Polynomial identities via normalization (`ring`) -/

example (x y : Real) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

/-! ### 3.2 Linear/nonlinear inequalities (`linarith`, `nlinarith`) -/

example {x y : Real} (hx : x <= y) : x + 3 <= y + 3 := by
  linarith

example {x : Real} : x ^ 2 >= 0 := by
  nlinarith

/-! ### 3.3 Clearing denominators safely (`field_simp`) -/

example (x y : Real) (hy : y ≠ 0) : x / y + 1 = (x + y) / y := by
  field_simp [hy]

/-! ### 3.4 Arithmetic computation tools (`norm_num`, `positivity`) -/

example : (17 : Real) < 100 := by
  norm_num

example (x : Real) : 0 <= x ^ 2 + 1 := by
  positivity

end Chapter03

/-!
## Chapter 4. Casts and Coercions
-/

section Chapter04

/-! ### 4.1 Casts as a proof-engineering task -/

example (m n : Nat) (h : m <= n) : (m : Int) <= n := by
  exact_mod_cast h

example (m n : Nat) : ((m + n : Nat) : Int) = m + n := by
  norm_cast

/-! ### 4.2 Archimedean moves -/

example (x : Real) : Exists fun n : Nat => x < n := by
  exact exists_nat_gt x

example {eps : Real} (heps : 0 < eps) : Exists fun n : Nat => (1 : Real) / (n + 1) < eps := by
  simpa using exists_nat_one_div_lt heps

end Chapter04

/-!
## Chapter 5. Absolute Value, Intervals, and Set Membership
-/

section Chapter05

/-! ### 5.1 Order lemmas and inequality chaining -/

example {a b c : Real} (h : a <= b) : a + c <= b + c := by
  linarith

example {a b c : Real} (h : a <= b) (hc : 0 <= c) : a * c <= b * c := by
  exact mul_le_mul_of_nonneg_right h hc

/-! ### 5.2 `abs` as bridge to interval inequalities -/

example {x a eps : Real} (h : |x - a| < eps) : a - eps < x ∧ x < a + eps := by
  rcases abs_lt.mp h with ⟨h1, h2⟩
  constructor <;> linarith

/-! ### 5.3 Intervals as sets, membership via `simp` -/

example {x a b : Real} (hx : x ∈ Set.Icc a b) : a <= x ∧ x <= b := by
  simpa [Set.mem_Icc] using hx

example (a b : Real) : Set.Icc a b = {x : Real | a <= x ∧ x <= b} := by
  ext x
  simp [Set.mem_Icc]

end Chapter05

/-!
# PART III. SETS AND FUNCTIONS AS LANGUAGE

## Chapter 6. Extensionality, Images, and Preimages
-/

section Chapter06

/-! ### 6.1 Set extensionality template: `ext x; simp` -/

example (s t : Set Real) : s ∪ t = t ∪ s := by
  ext x
  simp [or_comm]

example (s t u : Set Real) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x
  simp [and_or_left]

/-! ### 6.2 Function extensionality and pointwise reasoning -/

example {f g : Real -> Real} (h : forall x, f x = g x) : f = g := by
  funext x
  exact h x

example (f g h : Real -> Real) : (fun x => f (g (h x))) = (f ∘ g ∘ h) := by
  rfl

/-! ### 6.3 Preimages and images -/

example {α β : Type} (f : α -> β) (s t : Set β) :
    f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t := by
  ext x
  simp

example {α β : Type} (f : α -> β) (s t : Set α) (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

end Chapter06

/-!
# PART IV. TOPOLOGY OF `Real` AND FILTERS

## Chapter 7. Metric and Topological Basics
-/

section Chapter07

/-! ### 7.1 Open and closed intervals -/

example (a b : Real) : IsOpen (Set.Ioo a b) := by
  simpa using isOpen_Ioo

example (a b : Real) : IsClosed (Set.Icc a b) := by
  simpa using isClosed_Icc

/-! ### 7.2 `dist` and `abs` bridge on `Real` -/

example (x a eps : Real) : x ∈ Metric.ball a eps ↔ |x - a| < eps := by
  simp [Metric.ball, Real.dist_eq]

end Chapter07

/-!
## Chapter 8. Neighborhoods and Filters
-/

section Chapter08

/-! ### 8.1 Neighborhood basics -/

example (a eps : Real) (heps : 0 < eps) : Metric.ball a eps ∈ 𝓝 a := by
  exact Metric.ball_mem_nhds a heps

/-! ### 8.2 `atTop` and eventually -/

example (P : Nat -> Prop) (hP : forall n, P n) : ∀ᶠ n in atTop, P n := by
  exact Filter.Eventually.of_forall hP

example (P Q : Nat -> Prop)
    (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  filter_upwards [hP, hQ] with n hnP hnQ
  exact ⟨hnP, hnQ⟩

/-! ### 8.3 `Tendsto` to epsilon-neighborhood form (sequence version) -/

example (u : Nat -> Real) (a : Real) (hu : Tendsto u atTop (𝓝 a))
    {eps : Real} (heps : 0 < eps) :
    u ⁻¹' {x : Real | |x - a| < eps} ∈ atTop := by
  have hball : {x : Real | |x - a| < eps} ∈ 𝓝 a := by
    simpa [Metric.ball, Real.dist_eq] using (Metric.ball_mem_nhds a heps)
  exact hu hball

end Chapter08

/-!
# PART V. LIMITS AND CONTINUITY

## Chapter 9. Limits of Sequences
-/

section Chapter09

/-! ### 9.1 Basic limits and eventual equality -/

example (a : Real) : Tendsto (fun _ : Nat => a) atTop (𝓝 a) := by
  simp

example (u v : Nat -> Real) (a : Real) (h : u =ᶠ[atTop] v)
    (hu : Tendsto u atTop (𝓝 a)) : Tendsto v atTop (𝓝 a) := by
  exact (tendsto_congr' h).1 hu

/-! ### 9.2 Algebra of limits -/

example (u v : Nat -> Real) (a b : Real)
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n => u n + v n) atTop (𝓝 (a + b)) := by
  simpa using hu.add hv

example (u v : Nat -> Real) (a b : Real)
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n => u n * v n) atTop (𝓝 (a * b)) := by
  simpa using hu.mul hv

/-! ### 9.3 Squeeze/order consequences

Two canonical API patterns:
1. Squeeze theorem from eventual inequalities.
2. Passing eventual order relations to the limit.
-/

example (u v w : Nat -> Real) (a : Real)
    (hu : Tendsto u atTop (𝓝 a)) (hw : Tendsto w atTop (𝓝 a))
    (huv : ∀ᶠ n in atTop, u n <= v n) (hvw : ∀ᶠ n in atTop, v n <= w n) :
    Tendsto v atTop (𝓝 a) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hu hw huv hvw

example (u v : Nat -> Real) (a b : Real)
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (huv : ∀ᶠ n in atTop, u n <= v n) :
    a <= b := by
  exact le_of_tendsto_of_tendsto hu hv huv

end Chapter09

/-!
## Chapter 10. Cauchy Sequences and Completeness of `Real`
-/

section Chapter10

/-! ### 10.1 Tendsto implies Cauchy -/

example (u : Nat -> Real) (a : Real) (hu : Tendsto u atTop (𝓝 a)) :
    Cauchy (Filter.map u atTop) := by
  exact hu.cauchy_map

/-! ### 10.2 Cauchy implies convergent in `Real` -/

example (u : Nat -> Real) (hu : Cauchy (Filter.map u atTop)) :
    Exists fun a : Real => Tendsto u atTop (𝓝 a) := by
  exact cauchy_map_iff_exists_tendsto.mp hu

end Chapter10

/-!
## Chapter 11. Limits of Functions and Continuity
-/

section Chapter11

/-! ### 11.1 Tendsto at a point and composition -/

example (a : Real) : Tendsto (fun x : Real => x) (𝓝 a) (𝓝 a) := by
  simpa using (tendsto_id : Tendsto (id : Real -> Real) (𝓝 a) (𝓝 a))

example {f g : Real -> Real} {a b c : Real}
    (hf : Tendsto f (𝓝 a) (𝓝 b)) (hg : Tendsto g (𝓝 b) (𝓝 c)) :
    Tendsto (fun x => g (f x)) (𝓝 a) (𝓝 c) := by
  exact hg.comp hf

/-! ### 11.2 `Continuous`, `ContinuousAt`, `ContinuousOn` -/

example : Continuous (fun x : Real => x) := by
  simpa using continuous_id

example : Continuous (fun _x : Real => (3 : Real)) := by
  simpa using continuous_const

example : Continuous (fun x : Real => x ^ 2) := by
  simpa using (continuous_id.pow 2)

example (f g : Real -> Real) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) := by
  exact hf.add hg

/-! ### 11.3 Extracting epsilon-delta from `ContinuousAt`

Definition-mode extraction from the metric characterization.
-/

example {f : Real -> Real} {a : Real} (hf : ContinuousAt f a) :
    ∀ eps > 0, ∃ δ > 0, ∀ x : Real, |x - a| < δ -> |f x - f a| < eps := by
  intro eps heps
  rcases Metric.continuousAt_iff.mp hf eps heps with ⟨δ, hδ, hδ_spec⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  simpa [Real.dist_eq] using (hδ_spec hx)

/-! ### 11.4 Intermediate Value Theorem

Use packaged IVT and unpack the witness.
-/

example {f : Real -> Real} {a b : Real} (hab : a <= b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : f a <= 0) (hb : 0 <= f b) :
    ∃ c ∈ Set.Icc a b, f c = 0 := by
  have hzero : (0 : Real) ∈ Set.Icc (f a) (f b) := ⟨ha, hb⟩
  rcases intermediate_value_Icc hab hf hzero with ⟨c, hc, hfc⟩
  exact ⟨c, hc, hfc⟩

/-! ### 11.5 Compactness + extreme value theorem on `[a,b]`

On compact intervals, continuous functions attain extrema.
-/

example {f : Real -> Real} {a b : Real} (hab : a <= b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ xMax ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x <= f xMax := by
  have hne : (Set.Icc a b).Nonempty := nonempty_Icc.2 hab
  exact isCompact_Icc.exists_isMaxOn hne hf

example {f : Real -> Real} {a b : Real} (hab : a <= b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ xMin ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f xMin <= f x := by
  have hne : (Set.Icc a b).Nonempty := nonempty_Icc.2 hab
  exact isCompact_Icc.exists_isMinOn hne hf

end Chapter11

/-!
# PART VI. SERIES AND INFINITE SUMS

## Chapter 12. Finite Sums as Practice
-/

section Chapter12

/-! ### 12.1 BigOperators basics -/

example (n : Nat) (c : Real) : (∑ _i ∈ Finset.range n, c) = n • c := by
  simp

example (n : Nat) : (∑ _i ∈ Finset.range n, (0 : Real)) = 0 := by
  simp

end Chapter12

/-!
## Chapter 13. Infinite Series: `Summable` and `tsum`
-/

section Chapter13

/-! ### 13.1 Geometric series -/

example {r : Real} (hr : |r| < 1) : Summable (fun n : Nat => r ^ n) := by
  exact summable_geometric_of_abs_lt_one hr

example {r : Real} (hr : |r| < 1) : (∑' n : Nat, r ^ n) = (1 - r)⁻¹ := by
  simpa using tsum_geometric_of_abs_lt_one hr

/-! ### 13.2 Comparison and absolute convergence

Absolute convergence implies convergence, and comparison gives summability.
-/

example (f : Nat -> Real) (habs : Summable (fun n => |f n|)) : Summable f := by
  exact Summable.of_abs habs

example (f g : Nat -> Real) (hg_nonneg : ∀ n, 0 <= g n)
    (hgf : ∀ n, g n <= f n) (hf : Summable f) :
    Summable g := by
  exact Summable.of_nonneg_of_le hg_nonneg hgf hf

/-! ### 13.3 Uniform convergence via series (M-test)

Use the M-test interface directly.
-/

example {f : Nat -> Real -> Real} {u : Nat -> Real} {s : Set Real}
    (hu : Summable u) (hbound : ∀ n x, x ∈ s -> ‖f n x‖ <= u n) :
    TendstoUniformlyOn (fun N x => Finset.sum (Finset.range N) (fun n => f n x))
      (fun x => ∑' n : Nat, f n x) atTop s := by
  simpa using tendstoUniformlyOn_tsum_nat hu hbound

end Chapter13

/-!
# PART VII. DIFFERENTIATION

## Chapter 14. Derivatives API
-/

section Chapter14

/-! ### 14.1 First derivatives -/

example (x : Real) : HasDerivAt (fun y : Real => y) 1 x := by
  simpa using (hasDerivAt_id (x := x))

example (c x : Real) : HasDerivAt (fun _ : Real => c) 0 x := by
  simpa using (hasDerivAt_const (x := x) (c := c))

/-! ### 14.2 Sum/product/chain rules -/

example (x : Real) : HasDerivAt (fun y : Real => y ^ 2) (2 * x) x := by
  simpa using (hasDerivAt_pow 2 x)

/-! ### 14.3 Differentiability implies continuity -/

example {f : Real -> Real} {a : Real} (h : DifferentiableAt Real f a) :
    ContinuousAt f a := by
  exact h.continuousAt

/-! ### 14.4 Mean value theorem and monotonicity

Apply MVT and derivative-sign monotonicity APIs.
-/

example {f : Real -> Real} {a b : Real} (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  exact exists_deriv_eq_slope f hab hcont hdiff

example {f : Real -> Real} (hf : Differentiable ℝ f)
    (hderiv_nonneg : ∀ x, 0 <= deriv f x) :
    Monotone f := by
  exact monotone_of_deriv_nonneg hf hderiv_nonneg

end Chapter14

/-!
# PART VIII. INTEGRATION

## Chapter 15. Minimal Measurability Toolkit
-/

section Chapter15

/-! ### 15.1 Measurability closure lemmas -/

example : Measurable (fun x : Real => x) := by
  simpa using measurable_id

example (f g : Real -> Real) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x + g x) := by
  exact hf.add hg

example (f : Real -> Real) (hf : Measurable f) : Measurable (fun x => |f x|) := by
  exact hf.abs

end Chapter15

/-!
## Chapter 16. Interval Integrals
-/

section Chapter16

/-! ### 16.1 IntervalIntegral notation and linearity basics -/

example (a b c : Real) : (∫ _x in a..b, c) = (b - a) • c := by
  simp

example (a b : Real) : (∫ _x in a..b, (0 : Real)) = 0 := by
  simp

/-! ### 16.2 FTC interface

Two standard FTC interfaces: derivative of an interval integral and
integral of a derivative.
-/

example (f : Real -> Real) (hf : Continuous f) (a b : Real) :
    deriv (fun u => ∫ x in a..u, f x) b = f b := by
  simpa using (Continuous.deriv_integral (f := f) hf a b)

example (f : Real -> Real) (a b : Real)
    (hderiv : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) MeasureTheory.volume a b) :
    (∫ y in a..b, deriv f y) = f b - f a := by
  simpa using (intervalIntegral.integral_deriv_eq_sub (a := a) (b := b) (f := f) hderiv hint)

/-! ### 16.3 Convergence under the integral sign

Dominated convergence is the standard API entry point.
-/

example {α ι : Type} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F : ι -> α -> Real} {f : α -> Real} {l : Filter ι}
    [l.IsCountablyGenerated] (bound : α -> Real)
    (hF_meas : ∀ᶠ n in l, MeasureTheory.AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ x ∂μ, ‖F n x‖ <= bound x)
    (hbound_int : MeasureTheory.Integrable bound μ)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) l (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ) bound hF_meas h_bound hbound_int h_lim

end Chapter16

/-!
# PART IX. SYNTHESIS AND MINI-PROJECTS

## Chapter 17. Case Studies on `[a,b]`
-/

section Chapter17

/-! ### 17.1 Heine-Borel style consequences -/

example (a b : Real) : IsCompact (Set.Icc a b) := by
  simpa using (isCompact_Icc : IsCompact (Set.Icc a b))

example {f : Real -> Real} (hf : Continuous f) (a b : Real) :
    ContinuousOn f (Set.Icc a b) := by
  exact hf.continuousOn

/-! ### 17.2 One explicit epsilon proof (definition mode showcase)

Explicit eventual epsilon/2 proof with the triangle inequality.
-/

example (u v : Nat -> Real) (a b eps : Real)
    (hue : ∀ᶠ n in atTop, |u n - a| < eps / 2)
    (hve : ∀ᶠ n in atTop, |v n - b| < eps / 2) :
    ∀ᶠ n in atTop, |(u n + v n) - (a + b)| < eps := by
  filter_upwards [hue, hve] with n hun hvn
  have htri : |(u n + v n) - (a + b)| <= |u n - a| + |v n - b| := by
    have htri_norm : ‖(u n - a) + (v n - b)‖ <= ‖u n - a‖ + ‖v n - b‖ := norm_add_le _ _
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      htri_norm
  have hsum : |u n - a| + |v n - b| < eps / 2 + eps / 2 := add_lt_add hun hvn
  have hlt : |(u n + v n) - (a + b)| < eps / 2 + eps / 2 := lt_of_le_of_lt htri hsum
  simpa [add_halves] using hlt

end Chapter17

/-!
## Chapter 18. Writing Your Reusable Lemma Library
-/

section Chapter18

/-!
We define sample reusable lemmas in stable shapes.
These are small, but they show the style needed for later large projects.
-/

lemma tendsto_add_const {u : Nat -> Real} {a : Real}
    (hu : Tendsto u atTop (𝓝 a)) (c : Real) :
    Tendsto (fun n => u n + c) atTop (𝓝 (a + c)) := by
  simpa using hu.add tendsto_const_nhds

lemma tendsto_shift_one {u : Nat -> Real} {a : Real}
    (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => u (n + 1)) atTop (𝓝 a) := by
  simpa [Function.comp, Nat.add_comm] using hu.comp (tendsto_add_atTop_nat 1)

end Chapter18

/-!
# PART X. PROBABILITY

## Chapter 19. Probability Spaces and Random Variables
## Chapter 20. Expectation, Independence, and Convergence in Probability

This integrated file keeps probability chapters as a roadmap in comments, with
the expectation that concrete statements are added from the exact APIs chosen
in your local Mathlib version.

Recommended implementation order:
1. Start with `[MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]`.
2. Formalize event identities (`P(univ)=1`, complement formula).
3. Add measurability closure for random variables.
4. Add expectation linearity + variance lemmas.
5. Add one LLN-style theorem application.
-/

section Chapter19And20

variable {Ω : Type} [MeasurableSpace Ω]

example (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] : μ Set.univ = 1 := by
  simp [MeasureTheory.measure_univ]

example (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) :
    μ sᶜ = 1 - μ s := by
  have hs_ne_top : μ s ≠ ⊤ := MeasureTheory.measure_ne_top μ s
  simpa [MeasureTheory.measure_univ] using (MeasureTheory.measure_compl hs hs_ne_top)

example (μ : MeasureTheory.Measure Ω) (X Y : Ω -> Real)
    (hX : MeasureTheory.Integrable X μ) (hY : MeasureTheory.Integrable Y μ) :
    (∫ ω, (X ω + Y ω) ∂μ) = (∫ ω, X ω ∂μ) + (∫ ω, Y ω ∂μ) := by
  simpa using MeasureTheory.integral_add hX hY

end Chapter19And20

/-!
## Chapter 21. Probability Toolkit (Chapter 3 in Part X)

This chapter adds a compact, concrete toolbox that compiles on current
Mathlib versions. We focus on measurability closure and basic expectation
identities that are used repeatedly in probability proofs.
-/

section Chapter21

variable {Ω : Type} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]

/-! ### 21.1 Random variables: measurability closure -/

example {X Y : Ω -> Real} (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => X ω + Y ω) := by
  exact hX.add hY

example {X : Ω -> Real} (hX : Measurable X) :
    Measurable (fun ω => |X ω|) := by
  exact hX.abs

example {X : Ω -> Real} (hX : Measurable X) :
    Measurable (fun ω => X ω ^ 2) := by
  simpa using (hX.pow_const 2)

/-! ### 21.2 Expectation of constants and linearity -/

example (c : Real) : (∫ _ : Ω, c ∂μ) = c := by
  simp

example {X Y : Ω -> Real} (hX : MeasureTheory.Integrable X μ)
    (hY : MeasureTheory.Integrable Y μ) :
    (∫ ω, X ω + Y ω ∂μ) = (∫ ω, X ω ∂μ) + (∫ ω, Y ω ∂μ) := by
  simpa using MeasureTheory.integral_add hX hY

example {X : Ω -> Real} (c : Real) :
    (∫ ω, c * X ω ∂μ) = c * (∫ ω, X ω ∂μ) := by
  simpa using (MeasureTheory.integral_const_mul c X)

/-! ### 21.3 Convergence in probability: first-form API shape

We record the standard "definition mode" predicate without proving a theorem,
so later chapters can add results specialized to your local Mathlib API.
-/

def ConvergesInProbability (u : Nat -> Ω -> Real) (f : Ω -> Real) : Prop :=
  ∀ eps > 0, Tendsto (fun n => μ {ω | |u n ω - f ω| > eps}) atTop (𝓝 0)

end Chapter21

/-!
## Appendices (Reference + Workflow)

Appendix A: tactic index by first appearance
- Core: `rfl`, `intro`, `exact`, `apply`, `refine`, `have`, `constructor`, `cases`, `rcases`, `use`
- Rewriting: `rw`, `simp`, `simpa`, `calc`, `funext`, `ext`
- Automation: `norm_num`, `ring`, `linarith`, `nlinarith`, `field_simp`, `positivity`
- Filters: `filter_upwards`, eventual patterns, `Tendsto`
- Logic hygiene: `by_cases`, `by_contra`, `push_neg`
- Inspection: `#check`, `#print`

Appendix B: lemma-finding routine
1. Normalize goal shape (`simp`, cast cleanup).
2. Identify namespace family (`abs`, `interval`, `Tendsto`, `Continuous`, `integral`, `deriv`).
3. Search by type shape, then apply with `simpa`.

Appendix C: common pitfalls
1. Cast issues: solve casts before arithmetic automation.
2. `simp` surprises: prefer local simp lists over global attributes.
3. Typeclass ambiguity: annotate `(0 : Real)`, `(1 : Real)` when needed.
4. Automation failures: preprocess goal, then call automation.

Appendix D: suggested mini-project milestones
1. After Part IV: short limit-laws collection for sequences.
2. After Part V: IVT-based root existence for a concrete function.
3. After Part VIII: interval integral computations + FTC report.
4. After Part X: small probability toolkit (indicator, variance, one concentration corollary).

End matter concept map:
- textbook limits -> `Filter.Tendsto`
- sequence convergence -> `Tendsto u atTop (𝓝 a)`
- continuity -> `Continuous`/`ContinuousAt`/`ContinuousOn`
- derivatives -> `HasDerivAt`, `deriv`
- integrals -> interval integral API + integral API
- series -> `Summable`, `tsum`
- probability -> probability-measure and expectation APIs
-/

end RealAnalysisBook
