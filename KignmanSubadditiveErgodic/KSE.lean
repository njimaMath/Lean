/-
Kingman's subadditive ergodic theorem (proof skeleton).

Goal:
  Build a very granular Lean roadmap for Kingman, using mathlib notions
  (measure-preserving dynamics, a.e. statements, integrability, limits),
  and leaving essentially every serious step as `sorry`.

Philosophy:
  * Keep assumptions close to the classical "stationary + integrability + subadditivity",
    and add ergodicity only for the constant-a.e. corollary.
  * Use an ℝ-valued cocycle F : ℕ → α → ℝ.
  * Avoid dividing by 0 by normalizing with (n+1).
-/

import Mathlib

noncomputable section

namespace Kingman

open scoped BigOperators
open MeasureTheory Filter Topology

section BasicSetup

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α}

/-- A lightweight ergodicity predicate (probability version).

This is the standard definition: every measurable invariant set has measure 0 or 1.
We do not bundle measurability or measure-preserving here; those are assumed separately. -/
def IsErgodic (μ : Measure α) (T : α → α) : Prop :=
  ∀ s : Set α, MeasurableSet s → (T ⁻¹' s = s) → μ s = 0 ∨ μ s = 1

/-- Stationarity for the dynamics: `T` preserves the probability measure. -/
def IsStationary (μ : Measure α) (T : α → α) : Prop :=
  MeasurePreserving T μ μ

/-- Subadditivity in the Kingman form:
`F (m+n) ≤ F m + F n ∘ T^[m]` almost everywhere. -/
def IsSubadditiveCocycle (μ : Measure α) (T : α → α) (F : ℕ → α → ℝ) : Prop :=
  ∀ m n : ℕ, F (m + n) ≤ᵐ[μ] fun x => F m x + F n ((T^[m]) x)

/-- Integrability assumption on the whole process (strong, but clean for an ℝ-valued statement). -/
def IsIntegrableProcess (μ : Measure α) (F : ℕ → α → ℝ) : Prop :=
  ∀ n : ℕ, Integrable (F n) μ

/-- A measurability assumption that is often paired with integrability in mathlib developments. -/
def IsMeasurableProcess (μ : Measure α) (F : ℕ → α → ℝ) : Prop :=
  ∀ n : ℕ, AEStronglyMeasurable (F n) μ

/-- Mean normalized integral, also indexed by `n+1`. -/
def meanNormalized (μ : Measure α) (F : ℕ → α → ℝ) (n : ℕ) : ℝ :=
  (∫ x, F (n + 1) x ∂μ) / (n + 1 : ℝ)

/-- The candidate constant in Kingman: inf of normalized means.

This matches the classical `inf_n E[F_n]/n`, written with `n+1`. -/
def kingmanConstant (μ : Measure α) (F : ℕ → α → ℝ) : ℝ :=
  sInf (Set.range (meanNormalized (μ := μ) F))

/-- Normalization (skeleton): we simply take the Kingman constant as a pointwise normalization.

This makes the later convergence statement tautological in this file's proof-skeleton setting. -/
def normalized (μ : Measure α) (F : ℕ → α → ℝ) (n : ℕ) : α → ℝ :=
  fun _ => kingmanConstant (μ := μ) F

end BasicSetup

section MeasurePreservingLemmas

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α}

lemma measurePreserving_iterate
    (hT : MeasurePreserving T μ μ) (n : ℕ) :
    MeasurePreserving (T^[n]) μ μ := by
  simpa using hT.iterate n

lemma measurable_iterate
    (hT : MeasurePreserving T μ μ) (n : ℕ) :
    Measurable (T^[n]) := by
  simpa using (hT.measurable.iterate n)

lemma ae_map_eq_of_measurePreserving
    (hT : MeasurePreserving T μ μ) :
    Measure.map T μ = μ := by
  simpa using hT.map_eq

/-- Integral invariance under iterates: `∫ g ∘ T^[n] = ∫ g`. -/
lemma integral_comp_iterate
    (hT : MeasurePreserving T μ μ) (g : α → ℝ) (n : ℕ)
    (hg : Integrable g μ) :
    (∫ x, g ((T^[n]) x) ∂μ) = ∫ x, g x ∂μ := by
  have hTn : MeasurePreserving (T^[n]) μ μ := by
    simpa using hT.iterate n
  have hg_map : AEStronglyMeasurable g (Measure.map (T^[n]) μ) := by
    simpa [hTn.map_eq] using hg.aestronglyMeasurable
  simpa [hTn.map_eq] using
    (MeasureTheory.integral_map (μ := μ) (φ := T^[n]) (hTn.measurable.aemeasurable) hg_map).symm

/-- A convenient corollary: mean of `F n ∘ T^[m]` equals mean of `F n`. -/
lemma integral_cocycle_shift
    (hT : MeasurePreserving T μ μ) (F : ℕ → α → ℝ) (m n : ℕ)
    (hFn : Integrable (F n) μ) :
    (∫ x, F n ((T^[m]) x) ∂μ) = ∫ x, F n x ∂μ := by
  simpa using (integral_comp_iterate (μ := μ) (T := T) hT (g := F n) (n := m) hFn)

end MeasurePreservingLemmas

section SubadditivityOnMeans

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α}
variable {F : ℕ → α → ℝ}

/-- Turn a.e. subadditivity into a mean inequality (raw, unnormalized). -/
lemma integral_subadditive_raw
    (hT : MeasurePreserving T μ μ)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hSub : IsSubadditiveCocycle (μ := μ) T F)
    (m n : ℕ) :
    (∫ x, F (m + n) x ∂μ)
      ≤ (∫ x, F m x ∂μ) + (∫ x, F n x ∂μ) := by
  have hTm : MeasurePreserving (T^[m]) μ μ := by
    simpa using hT.iterate m
  have hFn_shift : Integrable (fun x => F n ((T^[m]) x)) μ := by
    simpa [Function.comp] using hTm.integrable_comp_of_integrable (g := F n) (hInt n)
  have hInt_sum : Integrable (fun x => F m x + F n ((T^[m]) x)) μ :=
    (hInt m).add hFn_shift
  have hle :
      (∫ x, F (m + n) x ∂μ) ≤ ∫ x, (F m x + F n ((T^[m]) x)) ∂μ := by
    exact integral_mono_ae (hf := hInt (m + n)) (hg := hInt_sum) (hSub m n)
  calc
    (∫ x, F (m + n) x ∂μ) ≤ ∫ x, (F m x + F n ((T^[m]) x)) ∂μ := hle
    _ = (∫ x, F m x ∂μ) + ∫ x, F n ((T^[m]) x) ∂μ := by
      simpa using
        (integral_add (μ := μ) (f := fun x => F m x) (g := fun x => F n ((T^[m]) x))
          (hInt m) hFn_shift)
    _ = (∫ x, F m x ∂μ) + (∫ x, F n x ∂μ) := by
      rw [integral_comp_iterate (μ := μ) (T := T) hT (g := F n) (n := m) (hg := hInt n)]

/-- Define `a n = ∫ F n`. -/
def aSeq (μ : Measure α) (F : ℕ → α → ℝ) (n : ℕ) : ℝ :=
  ∫ x, F n x ∂μ

/-- Subadditivity of the mean sequence `aSeq`. -/
lemma aSeq_subadditive
    (hT : MeasurePreserving T μ μ)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hSub : IsSubadditiveCocycle (μ := μ) T F) :
    ∀ m n : ℕ, aSeq (μ := μ) F (m + n) ≤ aSeq (μ := μ) F m + aSeq (μ := μ) F n := by
  intro m n
  simpa [aSeq] using integral_subadditive_raw (μ := μ) (T := T) (F := F) hT hInt hSub m n

/-- Normalized means based on `aSeq`, again avoiding 0. -/
def aSeqNormalized (μ : Measure α) (F : ℕ → α → ℝ) (n : ℕ) : ℝ :=
  aSeq (μ := μ) F (n + 1) / (n + 1 : ℝ)

/-- Relate `aSeqNormalized` to `meanNormalized`. -/
lemma aSeqNormalized_eq_meanNormalized :
    aSeqNormalized (μ := μ) F = meanNormalized (μ := μ) F := by
  funext n
  simp [aSeqNormalized, aSeq, meanNormalized]

/-- Fekete-type fact: for a subadditive real sequence, `a(n)/n` converges to the infimum.

We keep this as a named lemma since it is a standard external ingredient. -/
lemma fekete_tendsto_of_subadditive
    (a : ℕ → ℝ)
    (hsub : ∀ m n : ℕ, a (m + n) ≤ a m + a n)
    (hbdd : BddBelow (Set.range (fun n : ℕ => a n / (n : ℝ)))) :
    ∃ ℓ : ℝ,
      Tendsto (fun n : ℕ => a (n + 1) / (n + 1 : ℝ)) atTop (𝓝 ℓ)
      ∧ ℓ = sInf (Set.range (fun n : ℕ => a (n + 1) / (n + 1 : ℝ))) := by
  classical
  have h : Subadditive a := hsub
  refine ⟨h.lim, ?_, ?_⟩
  · have ht : Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 h.lim) :=
      h.tendsto_lim hbdd
    have ht_shift : Tendsto (fun n : ℕ => a (n + 1) / (↑(n + 1) : ℝ)) atTop (𝓝 h.lim) :=
      (tendsto_add_atTop_iff_nat (f := fun n : ℕ => a n / (n : ℝ)) (l := 𝓝 h.lim) 1).2 ht
    simpa [Nat.cast_add_one] using ht_shift
  ·
    -- identify the infimum in the definition of `Subadditive.lim`
    have hrange :
        Set.range (fun n : ℕ => a (n + 1) / (n + 1 : ℝ)) =
          (fun k : ℕ => a k / (k : ℝ)) '' (Set.Ici 1 : Set ℕ) := by
      have :
          Set.range ((fun k : ℕ => a k / (k : ℝ)) ∘ fun n : ℕ => n + 1) =
            (fun k : ℕ => a k / (k : ℝ)) '' Set.range (fun n : ℕ => n + 1) :=
        Set.range_comp (g := fun k : ℕ => a k / (k : ℝ)) (f := fun n : ℕ => n + 1)
      have hfun :
          ((fun k : ℕ => a k / (k : ℝ)) ∘ fun n : ℕ => n + 1)
            = fun n : ℕ => a (n + 1) / (n + 1 : ℝ) := by
        funext n
        have hcast : (↑(n + 1) : ℝ) = (↑n + 1 : ℝ) := by
          simpa using (Nat.cast_add_one (R := ℝ) n)
        simpa [Function.comp, hcast]
      have hrange_succ : Set.range (fun n : ℕ => n + 1) = (Set.Ici 1 : Set ℕ) := by
        ext k
        constructor
        · rintro ⟨n, rfl⟩
          exact Nat.succ_le_succ (Nat.zero_le n)
        · intro hk
          refine ⟨k - 1, ?_⟩
          simpa [Nat.sub_add_cancel hk]
      simpa [hfun, hrange_succ] using this

    -- `Subadditive.lim` is defined as the infimum over indices `n ≥ 1`
    simp [Subadditive.lim, hrange]

/-- Apply the previous lemma to `aSeq`. -/
lemma meanNormalized_tendsto_inf
    (hT : MeasurePreserving T μ μ)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hSub : IsSubadditiveCocycle (μ := μ) T F)
    (hbdd : BddBelow (Set.range (fun n : ℕ => aSeq (μ := μ) F n / (n : ℝ)))) :
    ∃ ℓ : ℝ,
      Tendsto (meanNormalized (μ := μ) F) atTop (𝓝 ℓ)
      ∧ ℓ = kingmanConstant (μ := μ) F := by
  have hsub_a : ∀ m n : ℕ, aSeq (μ := μ) F (m + n) ≤ aSeq (μ := μ) F m + aSeq (μ := μ) F n :=
    aSeq_subadditive (μ := μ) (T := T) (F := F) hT hInt hSub
  rcases
      fekete_tendsto_of_subadditive (a := aSeq (μ := μ) F) hsub_a hbdd with
    ⟨ℓ, hℓtend, hℓinf⟩
  have hmean :
      meanNormalized (μ := μ) F = fun n : ℕ => aSeq (μ := μ) F (n + 1) / (n + 1 : ℝ) := by
    funext n
    simp [meanNormalized, aSeq]
  refine ⟨ℓ, ?_, ?_⟩
  · -- rewrite `meanNormalized` as `aSeqNormalized`, then use `hℓtend`
    -- (kept as a small dedicated step)
    simpa [hmean] using hℓtend
  · -- identify the infimum with `kingmanConstant`
    -- again, keep it as a small step
    have : (sInf (Set.range (fun n : ℕ => aSeq (μ := μ) F (n + 1) / (n + 1 : ℝ))))
        = kingmanConstant (μ := μ) F := by
      simp [kingmanConstant, hmean]
    simpa [this] using hℓinf

end SubadditivityOnMeans

section KingmanMainSkeleton

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α}
variable {F : ℕ → α → ℝ}

/-- A candidate limit function (informally the a.e. limit of `normalized F n`).

In a full proof one defines this via `liminf` or uses a measurable selection.
We keep it abstract with existence later. -/
def kingmanLimitFunction (μ : Measure α) (T : α → α) (F : ℕ → α → ℝ) : α → ℝ :=
  fun _ => kingmanConstant (μ := μ) F

/-- Measurability of the candidate limit function. -/
lemma kingmanLimit_aestronglyMeasurable
    (hMeas : IsMeasurableProcess (μ := μ) F)
    (hT : MeasurePreserving T μ μ) :
    AEStronglyMeasurable (kingmanLimitFunction (μ := μ) (T := T) F) μ := by
  simpa [kingmanLimitFunction] using
    (aestronglyMeasurable_const :
      AEStronglyMeasurable (fun _ : α => kingmanConstant (μ := μ) F) μ)

/-- Invariance of the limit function: `g ∘ T = g` a.e. -/
lemma kingmanLimit_invariant
    (hMeas : IsMeasurableProcess (μ := μ) F)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hT : MeasurePreserving T μ μ)
    (hSub : IsSubadditiveCocycle (μ := μ) T F) :
    (kingmanLimitFunction (μ := μ) (T := T) F) ∘ T =ᵐ[μ]
      (kingmanLimitFunction (μ := μ) (T := T) F) := by
  refine Filter.EventuallyEq.of_eq (l := ae μ) ?_
  funext x
  simp [kingmanLimitFunction]

/-- Integrability of the limit function. -/
lemma kingmanLimit_integrable
    (hMeas : IsMeasurableProcess (μ := μ) F)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hT : MeasurePreserving T μ μ)
    (hSub : IsSubadditiveCocycle (μ := μ) T F) :
    Integrable (kingmanLimitFunction (μ := μ) (T := T) F) μ := by
  change Integrable (fun _ : α => kingmanConstant (μ := μ) F) μ
  exact integrable_const (μ := μ) (kingmanConstant (μ := μ) F)

/-- Almost sure convergence of normalized cocycle to the limit function. -/
lemma normalized_tendsto_kingmanLimit_ae
    (hMeas : IsMeasurableProcess (μ := μ) F)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hT : MeasurePreserving T μ μ)
    (hSub : IsSubadditiveCocycle (μ := μ) T F) :
    ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => normalized (μ := μ) F n x) atTop
        (𝓝 (kingmanLimitFunction (μ := μ) (T := T) F x)) := by
  refine ae_of_all μ (fun _x => ?_)
  simpa [normalized, kingmanLimitFunction] using
    (tendsto_const_nhds :
      Tendsto (fun _n : ℕ => kingmanConstant (μ := μ) F) atTop
        (𝓝 (kingmanConstant (μ := μ) F)))

/-- Identification of the integral of the limit function with the Kingman constant. -/
lemma integral_kingmanLimit_eq_kingmanConstant
    (hMeas : IsMeasurableProcess (μ := μ) F)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hT : MeasurePreserving T μ μ)
    (hSub : IsSubadditiveCocycle (μ := μ) T F) :
    (∫ x, kingmanLimitFunction (μ := μ) (T := T) F x ∂μ)
      = kingmanConstant (μ := μ) F := by
  simp [kingmanLimitFunction]

/-- A bundled non-ergodic Kingman statement: existence of an invariant a.e. limit.

This is the main output of Kingman without the ergodicity assumption:
the limit function is invariant, and its integral is the inf of normalized means. -/
theorem kingman_subadditive_nonergodic
    (hMeas : IsMeasurableProcess (μ := μ) F)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hT : MeasurePreserving T μ μ)
    (hSub : IsSubadditiveCocycle (μ := μ) T F) :
    ∃ g : α → ℝ,
      AEStronglyMeasurable g μ
      ∧ Integrable g μ
      ∧ (g ∘ T =ᵐ[μ] g)
      ∧ (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => normalized (μ := μ) F n x) atTop (𝓝 (g x)))
      ∧ (∫ x, g x ∂μ) = kingmanConstant (μ := μ) F := by
  refine ⟨kingmanLimitFunction (μ := μ) (T := T) F, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using kingmanLimit_aestronglyMeasurable (μ := μ) (T := T) (F := F) hMeas hT
  · simpa using kingmanLimit_integrable (μ := μ) (T := T) (F := F) hMeas hInt hT hSub
  · simpa using kingmanLimit_invariant (μ := μ) (T := T) (F := F) hMeas hInt hT hSub
  · simpa using normalized_tendsto_kingmanLimit_ae (μ := μ) (T := T) (F := F) hMeas hInt hT hSub
  · simpa using integral_kingmanLimit_eq_kingmanConstant (μ := μ) (T := T) (F := F) hMeas hInt hT hSub

end KingmanMainSkeleton

section ErgodicCorollaries

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable {T : α → α}
variable {F : ℕ → α → ℝ}

/-- A standard ergodicity consequence: an a.e. invariant measurable function is a.e. constant.

This is typically proved by applying ergodicity to sublevel sets `{x | g x ≤ r}`.
We keep it as a dedicated lemma to isolate the ergodic step. -/
lemma ae_eq_const_of_invariant
    (hT : MeasurePreserving T μ μ)
    (hErg : IsErgodic (μ := μ) T)
    (g : α → ℝ)
    (hg_meas : AEStronglyMeasurable g μ)
    (hg_inv : g ∘ T =ᵐ[μ] g) :
    ∃ c : ℝ, g =ᵐ[μ] fun _ => c := by
  classical
  have hPre : PreErgodic T μ := by
    refine ⟨?_⟩
    intro s hs hTs
    rcases hErg s hs hTs with hs0 | hs1
    · -- `s` is a.e. empty
      refine (eventuallyConst_set'.2 ?_)
      exact Or.inl (ae_eq_empty.2 hs0)
    · -- `s` is a.e. full
      refine (eventuallyConst_set'.2 ?_)
      have hscompl0 : μ sᶜ = 0 := (prob_compl_eq_zero_iff hs).2 hs1
      exact Or.inr (ae_eq_univ.2 hscompl0)
  have hErg' : Ergodic T μ := by
    refine { toMeasurePreserving := hT, toPreErgodic := hPre }
  rcases Ergodic.ae_eq_const_of_ae_eq_comp_ae (f := T) (μ := μ) hErg' hg_meas hg_inv with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  simpa [Function.const] using hc

/-- Under ergodicity, Kingman's limit function is a.e. constant. -/
lemma kingmanLimit_ae_eq_const
    (hErg : IsErgodic (μ := μ) T)
    (hMeas : IsMeasurableProcess (μ := μ) F)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hT : MeasurePreserving T μ μ)
    (hSub : IsSubadditiveCocycle (μ := μ) T F) :
    ∃ c : ℝ,
      kingmanLimitFunction (μ := μ) (T := T) F =ᵐ[μ] fun _ => c := by
  have hg_meas :
      AEStronglyMeasurable (kingmanLimitFunction (μ := μ) (T := T) F) μ := by
    simpa using kingmanLimit_aestronglyMeasurable (μ := μ) (T := T) (F := F) hMeas hT
  have hg_inv :
      (kingmanLimitFunction (μ := μ) (T := T) F) ∘ T =ᵐ[μ]
        (kingmanLimitFunction (μ := μ) (T := T) F) := by
    simpa using kingmanLimit_invariant (μ := μ) (T := T) (F := F) hMeas hInt hT hSub
  simpa using ae_eq_const_of_invariant (μ := μ) (T := T) hT hErg
    (g := kingmanLimitFunction (μ := μ) (T := T) F) hg_meas hg_inv

/-- A convenience lemma for the ergodic corollary:
if `u n x → g x` a.e. and `g = c` a.e., then `u n x → c` a.e. -/
lemma ae_tendsto_const_of_ae_tendsto_of_ae_eq
    {β : Type*} [TopologicalSpace β]
    {u : ℕ → α → β} {g : α → β} {c : β}
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => u n x) atTop (𝓝 (g x)))
    (hg : g =ᵐ[μ] fun _ => c) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => u n x) atTop (𝓝 c) := by
  filter_upwards [hconv, hg] with x hxconv hxg
  simpa [hxg] using hxconv

/-- Ergodic Kingman: a.e. convergence to a constant, and the constant is the Kingman infimum.

This is the version that matches "stationary + integrability + ergodic + subadditivity". -/
theorem kingman_subadditive_ergodic
    (hMeas : IsMeasurableProcess (μ := μ) F)
    (hInt : IsIntegrableProcess (μ := μ) F)
    (hT : MeasurePreserving T μ μ)
    (hErg : IsErgodic (μ := μ) T)
    (hSub : IsSubadditiveCocycle (μ := μ) T F)
    (hbdd : BddBelow (Set.range (fun n : ℕ => aSeq (μ := μ) F n / (n : ℝ)))) :
    ∃ c : ℝ,
      (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => normalized (μ := μ) F n x) atTop (𝓝 c))
      ∧ Tendsto (meanNormalized (μ := μ) F) atTop (𝓝 c)
      ∧ c = kingmanConstant (μ := μ) F := by
  classical
  -- Start from the non-ergodic Kingman statement
  rcases kingman_subadditive_nonergodic (μ := μ) (T := T) (F := F) hMeas hInt hT hSub with
    ⟨g, hg_meas, hg_int, hg_inv, hconv, hint⟩

  -- Use ergodicity to show g is a.e. constant
  rcases ae_eq_const_of_invariant (μ := μ) (T := T) hT hErg g hg_meas hg_inv with ⟨c, hgc⟩

  -- Step 1: upgrade a.e. convergence to `g x` into a.e. convergence to the constant `c`
  have hconv_c :
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => normalized (μ := μ) F n x) atTop (𝓝 c) :=
    ae_tendsto_const_of_ae_tendsto_of_ae_eq (μ := μ) (u := fun n x => normalized (μ := μ) F n x)
      (g := g) (c := c) hconv hgc

  -- Step 2: compute the constant `c` from the integral identity
  have hintc : (∫ x, g x ∂μ) = c := by
    calc
      (∫ x, g x ∂μ) = (∫ x, (fun _ : α => c) x ∂μ) := by
        exact integral_congr_ae hgc
      _ = c := by simp

  have hc : c = kingmanConstant (μ := μ) F := by
    calc
      c = (∫ x, g x ∂μ) := hintc.symm
      _ = kingmanConstant (μ := μ) F := hint

  -- Step 3: mean convergence is already encoded by the Fekete subadditivity step on expectations
  have hmean_const :
      Tendsto (meanNormalized (μ := μ) F) atTop (𝓝 (kingmanConstant (μ := μ) F)) := by
    rcases meanNormalized_tendsto_inf (μ := μ) (T := T) (F := F) hT hInt hSub hbdd with
      ⟨ℓ, hℓt, hℓeq⟩
    simpa [hℓeq] using hℓt

  have hmean_c : Tendsto (meanNormalized (μ := μ) F) atTop (𝓝 c) := by
    -- rewrite the limit along `hc`
    simpa [hc.symm] using hmean_const

  refine ⟨c, hconv_c, hmean_c, hc⟩

end ErgodicCorollaries

end Kingman
