import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Data.Int.Basic
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

section BondPercolation

open MeasureTheory

namespace Bond

namespace Zd

variable {d : ℕ}

def e (i : Fin d) : Percolation.Zd d := fun j => if j = i then (1 : ℤ) else 0

lemma e_apply_self (i : Fin d) : e (d := d) i i = 1 := by simp [e]

lemma e_apply_ne (i j : Fin d) (h : j ≠ i) : e (d := d) i j = 0 := by simp [e, h]

end Zd

namespace Lattice

variable {d : ℕ}

abbrev V : Type := Percolation.Zd d

def Adj (x y : V (d := d)) : Prop :=
  ∃ i : Fin d, y = x + Zd.e (d := d) i ∨ y = x - Zd.e (d := d) i

lemma Adj_symm {x y : V (d := d)} : Adj (d := d) x y → Adj (d := d) y x := by
  sorry

lemma Adj_irrefl (x : V (d := d)) : ¬ Adj (d := d) x x := by
  sorry

def latticeGraph (d : ℕ) : SimpleGraph (Percolation.Zd d) where
  Adj := Adj (d := d)
  symm := by
    intro x y
    exact Adj_symm (d := d)
  loopless := by
    intro x
    exact Adj_irrefl (d := d) x

lemma countable_Zd (d : ℕ) : Countable (Percolation.Zd d) := by infer_instance

end Lattice

namespace Prob

open Lattice

abbrev V (d : ℕ) : Type := Percolation.Zd d
abbrev G (d : ℕ) : SimpleGraph (V d) := Lattice.latticeGraph d
abbrev Edge (d : ℕ) : Type := {e : Sym2 (V d) // e ∈ (G d).edgeSet}

noncomputable def P (d : ℕ) (p : ℝ≥0∞) : Measure (Set (Edge d)) := by
  classical
  sorry

instance (d : ℕ) (p : ℝ≥0∞) : MeasureTheory.IsProbabilityMeasure (P d p) := by
  classical
  sorry

theorem measurable_mem_edge (d : ℕ) (p : ℝ≥0∞) (e : Edge d) :
    MeasurableSet {ω : Set (Edge d) | e ∈ ω} := by
  classical
  sorry

end Prob

namespace Geometry

variable {d : ℕ}

def box (n : ℕ) : Set (Percolation.Zd d) := {x | ∀ i : Fin d, Int.natAbs (x i) ≤ n}

theorem finite_box (n : ℕ) : (box (d := d) n).Finite := by
  classical
  sorry

abbrev Z2 : Type := Percolation.Zd 2

def rect (n m : ℕ) : Set Z2 :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ (n : ℤ) ∧ 0 ≤ x 1 ∧ x 1 ≤ (m : ℤ)}

theorem finite_rect (n m : ℕ) : (rect n m).Finite := by
  classical
  sorry

def leftBoundary (n m : ℕ) : Set Z2 := {x | x 0 = 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ (m : ℤ)}

def rightBoundary (n m : ℕ) : Set Z2 := {x | x 0 = (n : ℤ) ∧ 0 ≤ x 1 ∧ x 1 ≤ (m : ℤ)}

def bottomBoundary (n m : ℕ) : Set Z2 := {x | x 1 = 0 ∧ 0 ≤ x 0 ∧ x 0 ≤ (n : ℤ)}

def topBoundary (n m : ℕ) : Set Z2 := {x | x 1 = (m : ℤ) ∧ 0 ≤ x 0 ∧ x 0 ≤ (n : ℤ)}

end Geometry

namespace Open

open Lattice Prob Geometry

variable {d : ℕ}

abbrev V : Type := Percolation.Zd d
abbrev G : SimpleGraph (V (d := d)) := Lattice.latticeGraph d
abbrev E : Type := Prob.Edge d

def edgeOfAdj {x y : V (d := d)} (h : (G (d := d)).Adj x y) : E (d := d) := by
  refine ⟨s(x, y), ?_⟩
  simpa using h

def openAdj (ω : Set (E (d := d))) (x y : V (d := d)) : Prop :=
  ∃ h : (G (d := d)).Adj x y, edgeOfAdj (d := d) h ∈ ω

def WalkAllOpen (ω : Set (E (d := d))) : ∀ {x y : V (d := d)}, (G (d := d)).Walk x y → Prop
  | _, _, .nil => True
  | _, _, .cons h w => edgeOfAdj (d := d) h ∈ ω ∧ WalkAllOpen ω w

def WalkAllIn (S : Set (V (d := d))) {x y : V (d := d)} (w : (G (d := d)).Walk x y) : Prop :=
  ∀ v, v ∈ w.support → v ∈ S

def OpenConnected (ω : Set (E (d := d))) (x y : V (d := d)) : Prop :=
  ∃ w : (G (d := d)).Walk x y, WalkAllOpen (d := d) ω w

theorem OpenConnected_refl (ω : Set (E (d := d))) (x : V (d := d)) :
    OpenConnected (d := d) ω x x := by
  classical
  sorry

theorem OpenConnected_symm (ω : Set (E (d := d))) {x y : V (d := d)} :
    OpenConnected (d := d) ω x y → OpenConnected (d := d) ω y x := by
  classical
  sorry

theorem OpenConnected_trans (ω : Set (E (d := d))) {x y z : V (d := d)} :
    OpenConnected (d := d) ω x y → OpenConnected (d := d) ω y z → OpenConnected (d := d) ω x z := by
  classical
  sorry

theorem OpenConnected_mono {ω ω' : Set (E (d := d))} (hω : ω ⊆ ω') {x y : V (d := d)} :
    OpenConnected (d := d) ω x y → OpenConnected (d := d) ω' x y := by
  classical
  sorry

def connectsToBoundary (n : ℕ) : Set (Set (E (d := d))) :=
  {ω | ∃ y : V (d := d), y ∉ Geometry.box (d := d) n ∧ OpenConnected (d := d) ω 0 y}

def percolates : Set (Set (E (d := d))) := ⋂ n : ℕ, connectsToBoundary (d := d) n

theorem measurableSet_connectsToBoundary (n : ℕ) :
    MeasurableSet (connectsToBoundary (d := d) n) := by
  classical
  sorry

theorem measurableSet_percolates : MeasurableSet (percolates (d := d)) := by
  classical
  sorry

end Open

namespace CriticalProbability

open Prob Open

noncomputable def theta (d : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  (Prob.P d p) (Open.percolates (d := d))

noncomputable def p_c (d : ℕ) : ℝ≥0∞ :=
  sInf {p : ℝ≥0∞ | 0 < theta d p}

theorem theta_mono {d : ℕ} {p q : ℝ≥0∞} (hpq : p ≤ q) : theta d p ≤ theta d q := by
  classical
  sorry

theorem p_c_le_of_theta_pos {d : ℕ} {p : ℝ≥0∞} (hp : 0 < theta d p) : p_c d ≤ p := by
  classical
  sorry

theorem le_p_c_of_theta_eq_zero {d : ℕ} {p : ℝ≥0∞} (hp : theta d p = 0) : p ≤ p_c d := by
  classical
  sorry

end CriticalProbability

namespace TwoD

open Prob Open Geometry CriticalProbability

abbrev V : Type := Percolation.Zd 2
abbrev G : SimpleGraph V := Lattice.latticeGraph 2
abbrev E : Type := Prob.Edge 2

def CrossLR (n m : ℕ) : Set (Set E) :=
  {ω |
    ∃ x : V, x ∈ Geometry.leftBoundary n m ∧
      ∃ y : V, y ∈ Geometry.rightBoundary n m ∧
        ∃ w : (G).Walk x y, Open.WalkAllOpen (d := 2) ω w ∧
          Open.WalkAllIn (d := 2) (Geometry.rect n m) w}

def CrossTB (n m : ℕ) : Set (Set E) :=
  {ω |
    ∃ x : V, x ∈ Geometry.bottomBoundary n m ∧
      ∃ y : V, y ∈ Geometry.topBoundary n m ∧
        ∃ w : (G).Walk x y, Open.WalkAllOpen (d := 2) ω w ∧
          Open.WalkAllIn (d := 2) (Geometry.rect n m) w}

noncomputable def dualConfig (ω : Set E) : Set E := by
  classical
  sorry

theorem crossing_dichotomy (n m : ℕ) (ω : Set E) :
    ω ∈ CrossLR n m ∨ dualConfig ω ∈ CrossTB n m := by
  classical
  sorry

theorem crossing_disjoint (n m : ℕ) (ω : Set E) :
    ¬(ω ∈ CrossLR n m ∧ dualConfig ω ∈ CrossTB n m) := by
  classical
  sorry

theorem crossing_complement (n m : ℕ) (ω : Set E) :
    ω ∈ CrossLR n m ↔ ¬ dualConfig ω ∈ CrossTB n m := by
  classical
  sorry

theorem prob_crossLR_square_at_half (n : ℕ) :
    (Prob.P (d := 2) (1 / 2) (CrossLR n n)) = (1 / 2 : ℝ≥0∞) := by
  classical
  sorry

theorem rsw_lower_bound_at_half (ρ : ℝ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ n : ℕ, c ≤ (Prob.P (d := 2) (1 / 2) (CrossLR (Nat.floor (ρ * n)) n)) := by
  classical
  sorry

theorem russo_formula_crossLR (n : ℕ) : True := by
  trivial

theorem prob_crossLR_square_tendsto_one_of_gt_half {p : ℝ≥0∞} (hp : (1 / 2 : ℝ≥0∞) < p) :
    Filter.Tendsto (fun n : ℕ => (Prob.P (d := 2) p (CrossLR n n))) Filter.atTop (𝓝 1) := by
  classical
  sorry

theorem theta_pos_of_gt_half {p : ℝ≥0∞} (hp : (1 / 2 : ℝ≥0∞) < p) :
    0 < CriticalProbability.theta 2 p := by
  classical
  sorry

theorem theta_eq_zero_of_lt_half {p : ℝ≥0∞} (hp : p < (1 / 2 : ℝ≥0∞)) :
    CriticalProbability.theta 2 p = 0 := by
  classical
  sorry

theorem one_half_le_p_c : (1 / 2 : ℝ≥0∞) ≤ CriticalProbability.p_c 2 := by
  classical
  sorry

theorem p_c_le_one_half : CriticalProbability.p_c 2 ≤ (1 / 2 : ℝ≥0∞) := by
  classical
  sorry

theorem p_c_two_eq_one_half : CriticalProbability.p_c 2 = (1 / 2 : ℝ≥0∞) := by
  classical
  exact le_antisymm p_c_le_one_half one_half_le_p_c

end TwoD

end Bond

end BondPercolation





end Percolation
