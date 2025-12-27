import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.OrderClosed

open scoped BigOperators ENNReal Topology

namespace Percolation

/-- The integer lattice `ℤ^d` as functions `Fin d → ℤ`. -/
abbrev Zd (d : ℕ) : Type := Fin d → ℤ

/-- Directions in `ℤ^d`: a coordinate `i : Fin d` and a sign (`true` = `+eᵢ`, `false` = `-eᵢ`). -/
abbrev Dir (d : ℕ) : Type := Fin d × Bool

instance (d : ℕ) : Fintype (Dir d) := inferInstance
instance (d : ℕ) : DecidableEq (Dir d) := inferInstance

lemma card_dir (d : ℕ) : Fintype.card (Dir d) = 2 * d := by
  simp [Dir, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- A length-`n` nearest-neighbor path from `0` in `ℤ^d`, encoded by its sequence of directions. -/
abbrev Path (d n : ℕ) : Type := List.Vector (Dir d) n

instance (d n : ℕ) : Fintype (Path d n) := inferInstance
instance (d n : ℕ) : DecidableEq (Path d n) := inferInstance

lemma card_path (d n : ℕ) : Fintype.card (Path d n) = (2 * d) ^ n := by
  classical
  simpa [Path, card_dir d] using (card_vector (α := Dir d) n)

section Probability

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)
variable {d : ℕ} {p : ℝ≥0∞}

/-- Event: there exists an open path of length `n` from the origin. -/
def ExistsOpenPath (Open : ∀ {n : ℕ}, Path d n → Set Ω) (n : ℕ) : Set Ω :=
  ⋃ γ : Path d n, Open γ

/-- Event: for every length `n`, there exists an open path of length `n` from the origin.

This is the "arbitrarily long open paths from `0`" event; it contains the event
"there exists an infinite open path starting at `0`". -/
def ArbLongOpenPaths (Open : ∀ {n : ℕ}, Path d n → Set Ω) : Set Ω :=
  ⋂ n : ℕ, ExistsOpenPath (d := d) Open n

theorem prob_existsOpenPath_le
    (Open : ∀ {n : ℕ}, Path d n → Set Ω)
    (hprob : ∀ {n : ℕ} (γ : Path d n), μ (Open γ) ≤ p ^ n) (n : ℕ) :
    μ (ExistsOpenPath (d := d) Open n) ≤ ((2 * d : ℝ≥0∞) * p) ^ n := by
  classical
  have h_union :
      μ (⋃ γ : Path d n, Open γ) ≤ ∑ γ : Path d n, μ (Open γ) := by
    simpa [ExistsOpenPath] using
      (measure_iUnion_fintype_le (μ := μ) (s := fun γ : Path d n => Open γ))
  have h_sum :
      (∑ γ : Path d n, μ (Open γ)) ≤ ∑ γ : Path d n, p ^ n := by
    -- Rewrite as a `Finset` sum to use `Finset.sum_le_sum`.
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Path d n))) fun γ _ => hprob γ)
  have h_const :
      (∑ γ : Path d n, p ^ n) = (Fintype.card (Path d n) : ℝ≥0∞) * (p ^ n) := by
    simp
  have h_card :
      (Fintype.card (Path d n) : ℝ≥0∞) = ((2 * d : ℝ≥0∞) ^ n) := by
    -- `card_path` is a statement in `ℕ`; cast it to `ℝ≥0∞`.
    simpa using (show (Fintype.card (Path d n) : ℝ≥0∞) = ((2 * d) ^ n : ℝ≥0∞) from by
      exact_mod_cast (card_path d n))
  calc
    μ (ExistsOpenPath (d := d) Open n)
        = μ (⋃ γ : Path d n, Open γ) := by simp [ExistsOpenPath]
    _ ≤ ∑ γ : Path d n, μ (Open γ) := h_union
    _ ≤ ∑ γ : Path d n, p ^ n := h_sum
    _ = (Fintype.card (Path d n) : ℝ≥0∞) * (p ^ n) := h_const
    _ = ((2 * d : ℝ≥0∞) ^ n) * (p ^ n) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using congrArg (fun t => t * (p ^ n)) h_card
    _ = ((2 * d : ℝ≥0∞) * p) ^ n := by
      -- Combine the powers.
      simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_pow (2 * d : ℝ≥0∞) p n).symm

theorem prob_arbLongOpenPaths_eq_zero
    (Open : ∀ {n : ℕ}, Path d n → Set Ω)
    (hprob : ∀ {n : ℕ} (γ : Path d n), μ (Open γ) ≤ p ^ n)
    (hp : ((2 * d : ℝ≥0∞) * p) < 1) :
    μ (ArbLongOpenPaths (d := d) Open) = 0 := by
  classical
  let r : ℝ≥0∞ := (2 * d : ℝ≥0∞) * p
  have hle : ∀ n : ℕ, μ (ArbLongOpenPaths (d := d) Open) ≤ r ^ n := by
    intro n
    have hsub :
        ArbLongOpenPaths (d := d) Open ⊆ ExistsOpenPath (d := d) Open n := by
      intro ω hω
      exact (Set.mem_iInter.mp hω) n
    refine (measure_mono hsub).trans ?_
    simpa [r] using prob_existsOpenPath_le (μ := μ) (d := d) (p := p) Open hprob n
  -- Since `r < 1`, we have `r^n → 0`; combine this with `μ(A) ≤ r^n` to get `μ(A) = 0`.
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add (a := μ (ArbLongOpenPaths (d := d) Open)) (b := 0) ?_
    intro ε εpos _h0
    have htend :
        Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simpa [r] using hp)
    have hIio :
        Set.Iio (ε : ℝ≥0∞) ∈ 𝓝 (0 : ℝ≥0∞) := by
      refine Iio_mem_nhds ?_
      exact_mod_cast εpos
    have h_eventually :
        ∀ᶠ n : ℕ in Filter.atTop, r ^ n < (ε : ℝ≥0∞) :=
      htend.eventually_mem hIio
    rcases (Filter.eventually_atTop.1 h_eventually) with ⟨N, hN⟩
    have hNlt : r ^ N < (ε : ℝ≥0∞) := hN N le_rfl
    have : μ (ArbLongOpenPaths (d := d) Open) ≤ (ε : ℝ≥0∞) :=
      (hle N).trans (le_of_lt hNlt)
    simpa [zero_add] using this
  · exact zero_le _

end Probability

section CriticalProbability

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {d : ℕ}

/-- Percolation probability at parameter `p`: the probability of arbitrarily long open paths. -/
def percolationProb (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, Path d n → Set Ω) (p : ℝ≥0∞) : ℝ≥0∞ :=
  μ p (ArbLongOpenPaths (d := d) (Open := Open p))

/-- Critical probability `p_c`: the infimum of parameters where percolation has positive
probability. -/
noncomputable def p_c (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, Path d n → Set Ω) : ℝ≥0∞ :=
  sInf {p : ℝ≥0∞ | 0 < percolationProb (d := d) μ Open p}

theorem percolationProb_eq_zero_of_lt_one_div_two_mul_d
    (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, Path d n → Set Ω)
    (hprob : ∀ p {n : ℕ} (γ : Path d n), μ p (Open p γ) ≤ p ^ n)
    {p : ℝ≥0∞} (hp : p < (1 / (2 * d : ℝ≥0∞))) :
    percolationProb (d := d) μ Open p = 0 := by
  have hp' : ((2 * d : ℝ≥0∞) * p) < 1 := by
    simpa using
      (ENNReal.mul_lt_of_lt_div' (a := p) (b := (1 : ℝ≥0∞)) (c := (2 * d : ℝ≥0∞)) hp)
  have h :=
    prob_arbLongOpenPaths_eq_zero (μ := μ p) (d := d) (p := p) (Open := Open p)
      (hprob := by
        intro n γ
        simpa using hprob p γ)
      hp'
  simpa [percolationProb] using h

theorem one_div_two_mul_d_le_p_c
    (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, Path d n → Set Ω)
    (hprob : ∀ p {n : ℕ} (γ : Path d n), μ p (Open p γ) ≤ p ^ n) :
    (1 / (2 * d : ℝ≥0∞)) ≤ p_c (d := d) μ Open := by
  refine le_sInf ?_
  intro p hpPos
  have : ¬p < (1 / (2 * d : ℝ≥0∞)) := by
    intro hpLt
    have hz :
        percolationProb (d := d) μ Open p = 0 :=
      percolationProb_eq_zero_of_lt_one_div_two_mul_d (d := d) (μ := μ) (Open := Open) hprob hpLt
    simpa [hz] using hpPos
  exact not_lt.mp this

theorem p_c_pos
    (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, Path d n → Set Ω)
    (hprob : ∀ p {n : ℕ} (γ : Path d n), μ p (Open p γ) ≤ p ^ n) :
    0 < p_c (d := d) μ Open := by
  have hle : (1 / (2 * d : ℝ≥0∞)) ≤ p_c (d := d) μ Open :=
    one_div_two_mul_d_le_p_c (d := d) (μ := μ) (Open := Open) hprob
  have hpos : 0 < (1 / (2 * d : ℝ≥0∞)) := by
    refine ENNReal.div_pos (by simp) ?_
    -- The denominator is finite.
    simpa [Nat.cast_mul] using
      (ENNReal.mul_ne_top (a := (2 : ℝ≥0∞)) (b := (d : ℝ≥0∞)) (by simp) (by simp))
  exact hpos.trans_le hle

end CriticalProbability

end Percolation
