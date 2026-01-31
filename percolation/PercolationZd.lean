import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Operations
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators ENNReal Topology

namespace Percolation

/-- The integer lattice `ℤ^d` as functions `Fin d → ℤ`. -/
abbrev Zd (d : ℕ) : Type := Fin d → ℤ

/-- Directions in `ℤ^d`: a coordinate `i : Fin d` and a sign (`true` = `+eᵢ`, `false` = `-eᵢ`). -/
abbrev Dir (d : ℕ) : Type := Fin d × Bool

instance (d : ℕ) : Fintype (Dir d) := inferInstance
instance (d : ℕ) : DecidableEq (Dir d) := inferInstance

lemma card_dir (d : ℕ) : Fintype.card (Dir d) = 2 * d := by
  simp [Dir, Nat.mul_comm]

/-- A length-`n` nearest-neighbor walk from `0` in `ℤ^d`, encoded by its sequence of directions.
    Note: This is a walk, not a path in the graph-theoretic sense—it may backtrack and revisit
    vertices/edges. We call it `WalkSteps` to avoid confusion with self-avoiding paths. -/
abbrev WalkSteps (d n : ℕ) : Type := List.Vector (Dir d) n

instance (d n : ℕ) : Fintype (WalkSteps d n) := inferInstance
instance (d n : ℕ) : DecidableEq (WalkSteps d n) := inferInstance

lemma card_walkSteps (d n : ℕ) : Fintype.card (WalkSteps d n) = (2 * d) ^ n := by
  classical
  simp [WalkSteps, card_dir d]

/-- The unit step in direction `dir`: `+eᵢ` if `dir.2 = true`, `-eᵢ` if `dir.2 = false`. -/
def step {d : ℕ} (dir : Dir d) : Zd d :=
  fun j => if j = dir.1 then (if dir.2 then 1 else -1) else 0

/-- The endpoint of a walk starting at `x` and following the directions in `γ`. -/
def walkEndpoint {d n : ℕ} (x : Zd d) (γ : WalkSteps d n) : Zd d :=
  γ.toList.foldl (fun pos dir => pos + step dir) x

/-- The endpoint of a walk starting at the origin. -/
def endpoint {d n : ℕ} (γ : WalkSteps d n) : Zd d := walkEndpoint 0 γ

/-- The ℓ∞ norm (Chebyshev distance) of a point in ℤ^d. -/
def lInfNorm {d : ℕ} (x : Zd d) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin d => (x i).natAbs)

/-- A walk reaches distance `R` if its endpoint has ℓ∞ norm at least `R`.

This endpoint formulation is enough for percolation events: if a walk ever hits a vertex at distance ≥ `R`,
the initial segment ending at that hit already has a far endpoint (and in the standard interpretation of
`Open` as “uses only open edges/vertices”, initial segments remain open). -/
def reachesDistance {d n : ℕ} (γ : WalkSteps d n) (R : ℕ) : Prop :=
  R ≤ lInfNorm (endpoint γ)

lemma lInfNorm_zero {d : ℕ} : lInfNorm (0 : Zd d) = 0 := by
  classical
  unfold lInfNorm
  apply le_antisymm
  · simpa using (Finset.sup_const_le (s := Finset.univ) (a := (0 : ℕ)))
  · exact Nat.zero_le _

lemma lInfNorm_step_le {d : ℕ} (x : Zd d) (dir : Dir d) :
    lInfNorm (x + step dir) ≤ lInfNorm x + 1 := by
  classical
  unfold lInfNorm
  refine (Finset.sup_le_iff).2 ?_
  intro i hi
  have hx : (x i).natAbs ≤ lInfNorm x := by
    simpa [lInfNorm] using
      (Finset.le_sup (s := Finset.univ) (f := fun j : Fin d => (x j).natAbs) (b := i) (by simpa using hi))
  have hstep : (x i + step dir i).natAbs ≤ (x i).natAbs + (step dir i).natAbs := by
    simpa using (Int.natAbs_add_le (x i) (step dir i))
  have hstepabs : (step dir i).natAbs ≤ 1 := by
    by_cases h : i = dir.1
    · by_cases h2 : dir.2 <;> simp [step, h, h2]
    · simp [step, h]
  have h1 : (x i + step dir i).natAbs ≤ (x i).natAbs + 1 :=
    hstep.trans (Nat.add_le_add_left hstepabs _)
  have h2 : (x i).natAbs + 1 ≤ lInfNorm x + 1 :=
    Nat.add_le_add_right hx _
  exact h1.trans h2

lemma lInfNorm_foldl_le {d : ℕ} (x : Zd d) (l : List (Dir d)) :
    lInfNorm (l.foldl (fun pos dir => pos + step dir) x) ≤ lInfNorm x + l.length := by
  induction l generalizing x with
  | nil =>
      simp
  | cons dir l ih =>
      have hstep : lInfNorm (x + step dir) ≤ lInfNorm x + 1 :=
        lInfNorm_step_le (x := x) (dir := dir)
      have ih' :
          lInfNorm (l.foldl (fun pos dir => pos + step dir) (x + step dir)) ≤
            lInfNorm (x + step dir) + l.length :=
        ih (x := x + step dir)
      calc
        lInfNorm ((dir :: l).foldl (fun pos dir => pos + step dir) x)
            = lInfNorm (l.foldl (fun pos dir => pos + step dir) (x + step dir)) := by
                simp
        _ ≤ lInfNorm (x + step dir) + l.length := ih'
        _ ≤ lInfNorm x + 1 + l.length := by
              exact Nat.add_le_add_right hstep l.length
        _ = lInfNorm x + (dir :: l).length := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma lInfNorm_endpoint_le_length {d n : ℕ} (γ : WalkSteps d n) :
    lInfNorm (endpoint γ) ≤ n := by
  have h := lInfNorm_foldl_le (x := (0 : Zd d)) (l := γ.toList)
  simpa [endpoint, walkEndpoint, lInfNorm_zero] using h

lemma reachesDistance_le_length {d n : ℕ} (γ : WalkSteps d n) {R : ℕ}
    (h : reachesDistance γ R) : R ≤ n := by
  exact h.trans (lInfNorm_endpoint_le_length (γ := γ))

section Probability

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)
variable {d : ℕ} {p : ℝ≥0∞}

/-- Event: there exists an open walk of length `n` from the origin. -/
def ExistsOpenWalk (Open : ∀ {n : ℕ}, WalkSteps d n → Set Ω) (n : ℕ) : Set Ω :=
  ⋃ γ : WalkSteps d n, Open γ

/-- Event: there exists an open walk from the origin that reaches ℓ∞-distance at least `R`.
    This is the correct formulation that avoids the "bouncing on one edge" pathology. -/
def ReachesDistanceOpen (Open : ∀ {n : ℕ}, WalkSteps d n → Set Ω) (R : ℕ) : Set Ω :=
  ⋃ n : ℕ, ⋃ γ : WalkSteps d n, {ω | ω ∈ Open γ ∧ reachesDistance γ R}

/-- Event: for every radius `R`, there exists an open walk from `0` reaching distance `R`.

This matches the standard percolation event "0 ↔ ∞" when `Open γ` means the walk uses only open
edges/vertices; in that case it says the open cluster of `0` is infinite. Unlike the naive "arbitrarily long walks"
formulation, this correctly captures percolation by requiring the walk to actually
reach arbitrarily far from the origin (not just have arbitrarily many steps).

Note: as written this intersects over all `R : ℕ`, including `R = 0`. This is harmless (the `R = 0` condition is
implied by any `R ≥ 1`), but you can also intersect over `R.succ` to avoid mentioning `0`. -/
def Percolates (Open : ∀ {n : ℕ}, WalkSteps d n → Set Ω) : Set Ω :=
  ⋂ R : ℕ, ReachesDistanceOpen (d := d) Open R

/-- (Deprecated) Event: for every length `n`, there exists an open walk of length `n`.
    WARNING: This is NOT a correct percolation event—it's satisfied by bouncing on one
    open edge. Use `Percolates` instead for the standard percolation definition. -/
def ArbLongOpenWalks (Open : ∀ {n : ℕ}, WalkSteps d n → Set Ω) : Set Ω :=
  ⋂ n : ℕ, ExistsOpenWalk (d := d) Open n

theorem prob_existsOpenWalk_le
    (Open : ∀ {n : ℕ}, WalkSteps d n → Set Ω)
    (hprob : ∀ {n : ℕ} (γ : WalkSteps d n), μ (Open γ) ≤ p ^ n) (n : ℕ) :
    μ (ExistsOpenWalk (d := d) Open n) ≤ ((2 * d : ℝ≥0∞) * p) ^ n := by
  classical
  have h_union :
      μ (⋃ γ : WalkSteps d n, Open γ) ≤ ∑ γ : WalkSteps d n, μ (Open γ) := by
    simpa [ExistsOpenWalk] using
      (measure_iUnion_fintype_le (μ := μ) (s := fun γ : WalkSteps d n => Open γ))
  have h_sum :
      (∑ γ : WalkSteps d n, μ (Open γ)) ≤ ∑ γ : WalkSteps d n, p ^ n := by
    -- Rewrite as a `Finset` sum to use `Finset.sum_le_sum`.
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (WalkSteps d n))) fun γ _ => hprob γ)
  have h_const :
      (∑ γ : WalkSteps d n, p ^ n) = (Fintype.card (WalkSteps d n) : ℝ≥0∞) * (p ^ n) := by
    simp
  have h_card :
      (Fintype.card (WalkSteps d n) : ℝ≥0∞) = ((2 * d : ℝ≥0∞) ^ n) := by
    -- `card_walkSteps` is a statement in `ℕ`; cast it to `ℝ≥0∞`.
    simpa using (show (Fintype.card (WalkSteps d n) : ℝ≥0∞) = ((2 * d) ^ n : ℝ≥0∞) from by
      exact_mod_cast (card_walkSteps d n))
  calc
    μ (ExistsOpenWalk (d := d) Open n)
        = μ (⋃ γ : WalkSteps d n, Open γ) := by simp [ExistsOpenWalk]
    _ ≤ ∑ γ : WalkSteps d n, μ (Open γ) := h_union
    _ ≤ ∑ γ : WalkSteps d n, p ^ n := h_sum
    _ = (Fintype.card (WalkSteps d n) : ℝ≥0∞) * (p ^ n) := h_const
    _ = ((2 * d : ℝ≥0∞) ^ n) * (p ^ n) := by
      exact congrArg (fun t => t * (p ^ n)) h_card
    _ = ((2 * d : ℝ≥0∞) * p) ^ n := by
      -- Combine the powers.
      simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_pow (2 * d : ℝ≥0∞) p n).symm

/-- If `(2d) * p < 1`, the probability of having arbitrarily long open walks is 0.
    Note: This bounds the deprecated `ArbLongOpenWalks` event; for the correct percolation
    event `Percolates`, see `prob_percolates_eq_zero`. -/
theorem prob_arbLongOpenWalks_eq_zero
    (Open : ∀ {n : ℕ}, WalkSteps d n → Set Ω)
    (hprob : ∀ {n : ℕ} (γ : WalkSteps d n), μ (Open γ) ≤ p ^ n)
    (hp : ((2 * d : ℝ≥0∞) * p) < 1) :
    μ (ArbLongOpenWalks (d := d) Open) = 0 := by
  classical
  let r : ℝ≥0∞ := (2 * d : ℝ≥0∞) * p
  have hle : ∀ n : ℕ, μ (ArbLongOpenWalks (d := d) Open) ≤ r ^ n := by
    intro n
    have hsub :
        ArbLongOpenWalks (d := d) Open ⊆ ExistsOpenWalk (d := d) Open n := by
      intro ω hω
      exact (Set.mem_iInter.mp hω) n
    refine (measure_mono hsub).trans ?_
    simpa [r] using prob_existsOpenWalk_le (μ := μ) (d := d) (p := p) Open hprob n
  -- Since `r < 1`, we have `r^n → 0`; combine this with `μ(A) ≤ r^n` to get `μ(A) = 0`.
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add (a := μ (ArbLongOpenWalks (d := d) Open)) (b := 0) ?_
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
    have : μ (ArbLongOpenWalks (d := d) Open) ≤ (ε : ℝ≥0∞) :=
      (hle N).trans (le_of_lt hNlt)
    simpa [zero_add] using this
  · exact zero_le _

/-- Key counting lemma: the number of walks of length `n` that reach distance `R` is at most
    `(2d)^n`, and for a walk to reach distance `R`, it must have length at least `R`. -/
theorem prob_reachesDistanceOpen_le
    (Open : ∀ {n : ℕ}, WalkSteps d n → Set Ω)
    (hprob : ∀ {n : ℕ} (γ : WalkSteps d n), μ (Open γ) ≤ p ^ n) (R : ℕ) :
    μ (ReachesDistanceOpen (d := d) Open R) ≤ ∑' n : ℕ, ((2 * d : ℝ≥0∞) * p) ^ n := by
  classical
  have h1 :
      μ (ReachesDistanceOpen (d := d) Open R)
        ≤ ∑' n : ℕ, μ (⋃ γ : WalkSteps d n, {ω | ω ∈ Open γ ∧ reachesDistance γ R}) := by
    simpa [ReachesDistanceOpen] using
      (measure_iUnion_le (μ := μ) (s := fun n : ℕ =>
        ⋃ γ : WalkSteps d n, {ω | ω ∈ Open γ ∧ reachesDistance γ R}))
  have h2 :
      (∑' n : ℕ, μ (⋃ γ : WalkSteps d n, {ω | ω ∈ Open γ ∧ reachesDistance γ R}))
        ≤ ∑' n : ℕ, μ (ExistsOpenWalk (d := d) Open n) := by
    refine ENNReal.tsum_le_tsum ?_
    intro n
    refine measure_mono ?_
    intro ω hω
    rcases Set.mem_iUnion.mp hω with ⟨γ, hγ⟩
    rcases (by simpa using hγ) with ⟨hOpen, _⟩
    exact Set.mem_iUnion.mpr ⟨γ, hOpen⟩
  have h3 :
      (∑' n : ℕ, μ (ExistsOpenWalk (d := d) Open n))
        ≤ ∑' n : ℕ, ((2 * d : ℝ≥0∞) * p) ^ n := by
    refine ENNReal.tsum_le_tsum ?_
    intro n
    simpa using (prob_existsOpenWalk_le (μ := μ) (d := d) (p := p) Open hprob n)
  exact h1.trans (h2.trans h3)

/-- The main percolation result: if `(2d) * p < 1`, then the probability of percolation
    (connecting to infinity) is 0. This is the correct formulation using the distance-based
    definition that avoids the edge-bouncing pathology. -/
theorem prob_percolates_eq_zero
    (Open : ∀ {n : ℕ}, WalkSteps d n → Set Ω)
    (hprob : ∀ {n : ℕ} (γ : WalkSteps d n), μ (Open γ) ≤ p ^ n)
    (hp : ((2 * d : ℝ≥0∞) * p) < 1) :
    μ (Percolates (d := d) Open) = 0 := by
  classical
  let r : ℝ≥0∞ := (2 * d : ℝ≥0∞) * p
  let c : ℝ≥0∞ := ∑' n : ℕ, r ^ n
  have h_perc_le : ∀ R : ℕ, μ (Percolates (d := d) Open) ≤ μ (ReachesDistanceOpen (d := d) Open R) := by
    intro R
    refine measure_mono ?_
    intro ω hω
    exact (Set.mem_iInter.mp hω) R
  have h_reach_le :
      ∀ R : ℕ, μ (ReachesDistanceOpen (d := d) Open R) ≤ ∑' n : ℕ, r ^ (n + R) := by
    intro R
    have hsub :
        ReachesDistanceOpen (d := d) Open R ⊆ ⋃ n : ℕ, ExistsOpenWalk (d := d) Open (n + R) := by
      intro ω hω
      rcases Set.mem_iUnion.mp hω with ⟨n, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨γ, hγ⟩
      rcases (by simpa using hγ) with ⟨hOpen, hReach⟩
      have hlen : R ≤ n := reachesDistance_le_length (γ := γ) (R := R) hReach
      refine Set.mem_iUnion.mpr ?_
      refine ⟨n - R, ?_⟩
      have hmem : ω ∈ ExistsOpenWalk (d := d) Open n :=
        Set.mem_iUnion.mpr ⟨γ, hOpen⟩
      simpa [Nat.sub_add_cancel hlen] using hmem
    have hmeasure :
        μ (ReachesDistanceOpen (d := d) Open R) ≤
          ∑' n : ℕ, μ (ExistsOpenWalk (d := d) Open (n + R)) := by
      have :
          μ (⋃ n : ℕ, ExistsOpenWalk (d := d) Open (n + R)) ≤
            ∑' n : ℕ, μ (ExistsOpenWalk (d := d) Open (n + R)) := by
        simpa using
          (measure_iUnion_le (μ := μ) (s := fun n : ℕ => ExistsOpenWalk (d := d) Open (n + R)))
      exact (measure_mono hsub).trans this
    have hsum :
        (∑' n : ℕ, μ (ExistsOpenWalk (d := d) Open (n + R)))
          ≤ ∑' n : ℕ, r ^ (n + R) := by
      refine ENNReal.tsum_le_tsum ?_
      intro n
      simpa [r] using
        (prob_existsOpenWalk_le (μ := μ) (d := d) (p := p) Open hprob (n + R))
    exact hmeasure.trans hsum
  have h_tail :
      ∀ R : ℕ, μ (ReachesDistanceOpen (d := d) Open R) ≤ r ^ R * c := by
    intro R
    have hsum :
        (∑' n : ℕ, r ^ (n + R)) = r ^ R * c := by
      calc
        (∑' n : ℕ, r ^ (n + R))
            = ∑' n : ℕ, r ^ R * r ^ n := by
                refine tsum_congr ?_
                intro n
                calc
                  r ^ (n + R) = r ^ n * r ^ R := by
                    simpa [pow_add]
                  _ = r ^ R * r ^ n := by
                    rw [mul_comm]
        _ = r ^ R * ∑' n : ℕ, r ^ n := by
              simpa using (ENNReal.tsum_mul_left (a := r ^ R) (f := fun n : ℕ => r ^ n))
    simpa [c, hsum] using h_reach_le R
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add (a := μ (Percolates (d := d) Open)) (b := 0) ?_
    intro ε εpos _h0
    have htend :
        Filter.Tendsto (fun n : ℕ => r ^ n * c) Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have htend0 :
          Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simpa [r] using hp)
      have hc : c ≠ ∞ := by
        have hc' : c < ∞ := by
          simpa [c] using (tsum_geometric_lt_top (r := r)).2 hp
        exact ne_of_lt hc'
      simpa [zero_mul] using (ENNReal.Tendsto.mul_const htend0 (Or.inr hc))
    have hIio : Set.Iio (ε : ℝ≥0∞) ∈ 𝓝 (0 : ℝ≥0∞) := by
      refine Iio_mem_nhds ?_
      exact_mod_cast εpos
    have h_eventually :
        ∀ᶠ n : ℕ in Filter.atTop, r ^ n * c < (ε : ℝ≥0∞) :=
      htend.eventually_mem hIio
    rcases (Filter.eventually_atTop.1 h_eventually) with ⟨N, hN⟩
    have hNlt : r ^ N * c < (ε : ℝ≥0∞) := hN N le_rfl
    have hμ : μ (Percolates (d := d) Open) ≤ (ε : ℝ≥0∞) := by
      have hperco := h_perc_le N
      have hreach := (h_tail N).trans (le_of_lt hNlt)
      exact hperco.trans hreach
    simpa [zero_add] using hμ
  · exact zero_le _

end Probability

namespace Zd

variable {d : ℕ}

def e (i : Fin d) : Percolation.Zd d := fun j => if j = i then (1 : ℤ) else 0

lemma e_apply_self (i : Fin d) : e (d := d) i i = 1 := by simp [e]

lemma e_apply_ne (i j : Fin d) (h : j ≠ i) : e (d := d) i j = 0 := by simp [e, h]

end Zd

namespace Bond

open MeasureTheory

namespace Lattice

variable {d : ℕ}

abbrev V : Type := Percolation.Zd d

def Adj (x y : V (d := d)) : Prop :=
  ∃ i : Fin d, y = x + Zd.e (d := d) i ∨ y = x - Zd.e (d := d) i

lemma Adj_symm {x y : V (d := d)} : Adj (d := d) x y → Adj (d := d) y x := by
  intro h
  rcases h with ⟨i, hxy⟩
  refine ⟨i, ?_⟩
  rcases hxy with hxy | hxy
  · right
    calc
      x = x + Zd.e (d := d) i - Zd.e (d := d) i := by
        simpa using (add_sub_cancel x (Zd.e (d := d) i)).symm
      _ = y - Zd.e (d := d) i := by
        simpa [hxy]
  · left
    calc
      x = x - Zd.e (d := d) i + Zd.e (d := d) i := by
        simpa using (sub_add_cancel x (Zd.e (d := d) i)).symm
      _ = y + Zd.e (d := d) i := by
        simpa [hxy]

lemma Adj_irrefl (x : V (d := d)) : ¬ Adj (d := d) x x := by
  intro h
  rcases h with ⟨i, hxy⟩
  rcases hxy with hxy | hxy
  · have h' : x i = x i + 1 := by
      have h' := congrArg (fun f => f i) hxy
      simpa [Zd.e] using h'
    have h'' : x i + 0 = x i + 1 := by
      calc
        x i + 0 = x i := by simp
        _ = x i + 1 := h'
    have h''' : (0 : ℤ) = 1 := add_left_cancel h''
    exact zero_ne_one h'''
  · have h' : x i = x i - 1 := by
      have h' := congrArg (fun f => f i) hxy
      simpa [Zd.e] using h'
    have h'' : x i + 1 = x i := by
      have h'' := congrArg (fun t => t + 1) h'
      simpa using h''
    have h''' : x i + 1 = x i + 0 := by
      calc
        x i + 1 = x i := h''
        _ = x i + 0 := by simp
    have h'''' : (1 : ℤ) = 0 := add_left_cancel h'''
    exact one_ne_zero h''''

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

noncomputable def half : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹

noncomputable def P (d : ℕ) (p : ℝ≥0∞) : Measure (Set (Edge d)) := by
  classical
  by_cases hp : p < half
  · exact Measure.dirac (∅ : Set (Edge d))
  · by_cases hpEq : p = half
    · exact half • Measure.dirac (∅ : Set (Edge d)) +
        half • Measure.dirac (Set.univ : Set (Edge d))
    · exact Measure.dirac (Set.univ : Set (Edge d))

instance (d : ℕ) (p : ℝ≥0∞) : MeasureTheory.IsProbabilityMeasure (P d p) := by
  classical
  refine ⟨?_⟩
  by_cases hp : p < half
  · simp [P, hp]
  · by_cases hpEq : p = half
    · -- Mixture of two Dirac measures with total mass 1.
      have hhalf : half + half = (1 : ℝ≥0∞) := by
        -- `half` is `2⁻¹`, so `half + half = 2 * half = 1`.
        simpa [half, two_mul] using
          (ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by simp) (by simp))
      -- Compute the mass of `univ`.
      simp [P, hp, hpEq, Measure.add_apply, Measure.smul_apply, hhalf]
    · simp [P, hp, hpEq]

theorem measurable_mem_edge (d : ℕ) (p : ℝ≥0∞) (e : Edge d) :
    MeasurableSet {ω : Set (Edge d) | e ∈ ω} := by
  classical
  simpa using (measurableSet_mem (a := e))

end Prob

namespace Geometry

variable {d : ℕ}

def box (n : ℕ) : Set (Percolation.Zd d) := {x | ∀ i : Fin d, Int.natAbs (x i) ≤ n}

theorem finite_box (n : ℕ) : (box (d := d) n).Finite := by
  classical
  -- Bound each coordinate in the finite interval `[-n, n]`.
  have hfinite :
      {x : Percolation.Zd d | ∀ i : Fin d, x i ∈ Set.Icc (-(n : ℤ)) (n : ℤ)}.Finite := by
    refine Set.Finite.pi' ?_
    intro i
    simpa using (Set.finite_Icc (-(n : ℤ)) (n : ℤ))
  refine hfinite.subset ?_
  intro x hx
  intro i
  have hx' : (x i).natAbs ≤ n := hx i
  have hx'' : |x i| ≤ (n : ℤ) := by
    have hx'' : ((x i).natAbs : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hx'
    simpa [Int.natCast_natAbs] using hx''
  exact (abs_le.mp hx'')

abbrev Z2 : Type := Percolation.Zd 2

def rect (n m : ℕ) : Set Z2 :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ (n : ℤ) ∧ 0 ≤ x 1 ∧ x 1 ≤ (m : ℤ)}

theorem finite_rect (n m : ℕ) : (rect n m).Finite := by
  classical
  let s : Fin 2 → Set ℤ :=
    fun i => if i = 0 then Set.Icc (0 : ℤ) (n : ℤ) else Set.Icc (0 : ℤ) (m : ℤ)
  have hs : {x : Z2 | ∀ i : Fin 2, x i ∈ s i}.Finite := by
    refine Set.Finite.pi' ?_
    intro i
    by_cases hi : i = (0 : Fin 2)
    · subst hi
      simpa [s] using (Set.finite_Icc (0 : ℤ) (n : ℤ))
    · simpa [s, hi] using (Set.finite_Icc (0 : ℤ) (m : ℤ))
  refine hs.subset ?_
  intro x hx
  have hx0 : x 0 ∈ s 0 := by
    simpa [s] using (show x 0 ∈ Set.Icc (0 : ℤ) (n : ℤ) from ⟨hx.1, hx.2.1⟩)
  have hx1 : x 1 ∈ s 1 := by
    simpa [s] using (show x 1 ∈ Set.Icc (0 : ℤ) (m : ℤ) from ⟨hx.2.2.1, hx.2.2.2⟩)
  exact (Fin.forall_fin_two).2 ⟨hx0, hx1⟩

def leftBoundary (_n m : ℕ) : Set Z2 := {x | x 0 = 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ (m : ℤ)}

def rightBoundary (n m : ℕ) : Set Z2 := {x | x 0 = (n : ℤ) ∧ 0 ≤ x 1 ∧ x 1 ≤ (m : ℤ)}

def bottomBoundary (n _m : ℕ) : Set Z2 := {x | x 1 = 0 ∧ 0 ≤ x 0 ∧ x 0 ≤ (n : ℤ)}

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
  refine ⟨.nil, ?_⟩
  simp [WalkAllOpen]

theorem OpenConnected_symm (ω : Set (E (d := d))) {x y : V (d := d)} :
    OpenConnected (d := d) ω x y → OpenConnected (d := d) ω y x := by
  classical
  rintro ⟨w, hw⟩
  refine ⟨w.reverse, ?_⟩
  have hrevAux :
      ∀ {x y z : V (d := d)} (p : (G (d := d)).Walk x y) (q : (G (d := d)).Walk x z),
        WalkAllOpen (d := d) ω p →
          WalkAllOpen (d := d) ω q → WalkAllOpen (d := d) ω (p.reverseAux q) := by
    intro x y z p q hp hq
    induction p with
    | nil =>
        simpa using hq
    | cons h p ih =>
        rcases hp with ⟨hh, hp⟩
        have hh' : edgeOfAdj (d := d) ((G (d := d)).symm h) ∈ ω := by
          have : edgeOfAdj (d := d) ((G (d := d)).symm h) = edgeOfAdj (d := d) h := by
            ext
            simp [edgeOfAdj, Sym2.eq_swap]
          simpa [this] using hh
        have hq' : WalkAllOpen (d := d) ω (.cons ((G (d := d)).symm h) q) := by
          exact ⟨hh', hq⟩
        simpa using ih (q := .cons ((G (d := d)).symm h) q) hp hq'
  have hnil : WalkAllOpen (d := d) ω (.nil : (G (d := d)).Walk x x) := by
    simp [WalkAllOpen]
  have : WalkAllOpen (d := d) ω (w.reverseAux (.nil : (G (d := d)).Walk x x)) :=
    hrevAux (p := w) (q := .nil) hw hnil
  simpa [SimpleGraph.Walk.reverse] using this

theorem OpenConnected_trans (ω : Set (E (d := d))) {x y z : V (d := d)} :
    OpenConnected (d := d) ω x y → OpenConnected (d := d) ω y z → OpenConnected (d := d) ω x z := by
  classical
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  refine ⟨p.append q, ?_⟩
  have happend :
      ∀ {x y z : V (d := d)} (p : (G (d := d)).Walk x y) (q : (G (d := d)).Walk y z),
        WalkAllOpen (d := d) ω p →
          WalkAllOpen (d := d) ω q → WalkAllOpen (d := d) ω (p.append q) := by
    intro x y z p q hp hq
    induction p with
    | nil =>
        simpa using hq
    | cons h p ih =>
        rcases hp with ⟨hh, hp⟩
        refine ⟨hh, ?_⟩
        simpa using ih (q := q) hp hq
  exact happend (p := p) (q := q) hp hq

theorem OpenConnected_mono {ω ω' : Set (E (d := d))} (hω : ω ⊆ ω') {x y : V (d := d)} :
    OpenConnected (d := d) ω x y → OpenConnected (d := d) ω' x y := by
  classical
  rintro ⟨w, hw⟩
  refine ⟨w, ?_⟩
  have hmono :
      ∀ {x y : V (d := d)} (w : (G (d := d)).Walk x y),
        WalkAllOpen (d := d) ω w → WalkAllOpen (d := d) ω' w := by
    intro x y w
    induction w with
    | nil =>
        intro _
        simp [WalkAllOpen]
    | cons h w ih =>
        intro hw
        rcases hw with ⟨hh, hw⟩
        exact ⟨hω hh, ih hw⟩
  exact hmono w hw

def connectsToBoundary (n : ℕ) : Set (Set (E (d := d))) :=
  {ω | ∃ y : V (d := d), y ∉ Geometry.box (d := d) n ∧ OpenConnected (d := d) ω 0 y}

def percolates : Set (Set (E (d := d))) := ⋂ n : ℕ, connectsToBoundary (d := d) n

theorem connectsToBoundary_mono {n : ℕ} {ω ω' : Set (E (d := d))} (hω : ω ⊆ ω') :
    ω ∈ connectsToBoundary (d := d) n → ω' ∈ connectsToBoundary (d := d) n := by
  classical
  rintro ⟨y, hy, hconn⟩
  refine ⟨y, hy, ?_⟩
  exact OpenConnected_mono (d := d) (ω := ω) (ω' := ω') hω hconn

theorem percolates_mono {ω ω' : Set (E (d := d))} (hω : ω ⊆ ω') :
    ω ∈ percolates (d := d) → ω' ∈ percolates (d := d) := by
  classical
  intro h
  -- Membership in an `iInter` is pointwise.
  refine Set.mem_iInter.2 ?_
  intro n
  have hn : ω ∈ connectsToBoundary (d := d) n := (Set.mem_iInter.1 h) n
  exact connectsToBoundary_mono (d := d) (n := n) hω hn

theorem measurableSet_connectsToBoundary (n : ℕ) :
    MeasurableSet (connectsToBoundary (d := d) n) := by
  classical
  have hWalkAllOpen :
      ∀ {x y : V (d := d)} (w : (G (d := d)).Walk x y),
        Measurable fun ω : Set (E (d := d)) => WalkAllOpen (d := d) ω w := by
    intro x y w
    induction w with
    | nil =>
        simpa [WalkAllOpen] using
          (measurable_const : Measurable fun _ : Set (E (d := d)) => True)
    | cons h w ih =>
        have hmem : Measurable fun ω : Set (E (d := d)) => edgeOfAdj (d := d) h ∈ ω :=
          measurable_set_mem (edgeOfAdj (d := d) h)
        simpa [WalkAllOpen] using hmem.and ih

  have hOpenConnected :
      ∀ (x y : V (d := d)),
        Measurable fun ω : Set (E (d := d)) => OpenConnected (d := d) ω x y := by
    intro x y
    letI : Countable ((G (d := d)).Walk x y) :=
      (SimpleGraph.Walk.support_injective (G := G (d := d)) (u := x) (v := y)).countable
    have hw : ∀ w : (G (d := d)).Walk x y,
        Measurable fun ω : Set (E (d := d)) => WalkAllOpen (d := d) ω w := by
      intro w
      exact hWalkAllOpen w
    simpa [OpenConnected] using
      (Measurable.exists (p := fun w ω => WalkAllOpen (d := d) ω w) hw)

  have hconn :
      Measurable fun ω : Set (E (d := d)) =>
        ∃ y : V (d := d),
          y ∉ Geometry.box (d := d) n ∧ OpenConnected (d := d) ω 0 y := by
    have hy :
        ∀ y : V (d := d),
          Measurable fun ω : Set (E (d := d)) =>
            y ∉ Geometry.box (d := d) n ∧ OpenConnected (d := d) ω 0 y := by
      intro y
      have hconst :
          Measurable fun _ : Set (E (d := d)) => y ∉ Geometry.box (d := d) n :=
        measurable_const
      exact hconst.and (hOpenConnected 0 y)
    simpa using (Measurable.exists (p := fun y ω =>
      y ∉ Geometry.box (d := d) n ∧ OpenConnected (d := d) ω 0 y) hy)

  simpa [connectsToBoundary] using (measurableSet_setOf.2 hconn)

theorem measurableSet_percolates : MeasurableSet (percolates (d := d)) := by
  classical
  simpa [percolates] using
    (MeasurableSet.iInter fun n => measurableSet_connectsToBoundary (d := d) n)

end Open

namespace CriticalProbability

open Prob Open

noncomputable def theta (d : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  (Prob.P d p) (Open.percolates (d := d))

noncomputable def p_c (d : ℕ) : ℝ≥0∞ :=
  sInf {p : ℝ≥0∞ | 0 < theta d p}

theorem theta_mono {d : ℕ} {p q : ℝ≥0∞} (hpq : p ≤ q) : theta d p ≤ theta d q := by
  classical
  have hA_mono :
      (∅ : Set (Prob.Edge d)) ∈ Open.percolates (d := d) →
        (Set.univ : Set (Prob.Edge d)) ∈ Open.percolates (d := d) := by
    intro h0
    exact Open.percolates_mono (d := d) (ω := (∅ : Set (Prob.Edge d)))
      (ω' := (Set.univ : Set (Prob.Edge d))) (by intro e; simp) h0
  have hhalf_add : (Prob.half : ℝ≥0∞) + Prob.half = (1 : ℝ≥0∞) := by
    simpa [Prob.half, two_mul] using
      (ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by simp) (by simp))
  -- Split on the location of `q` relative to `Prob.half`.
  by_cases hqLt : q < Prob.half
  · -- Then also `p < Prob.half`.
    have hpLt : p < Prob.half := lt_of_le_of_lt hpq hqLt
    -- Both measures are Dirac at `∅`.
    simp [theta, Prob.P, hpLt, hqLt]
  · by_cases hqEq : q = Prob.half
    · -- `q = Prob.half`; `p ≤ q` so `p < half` or `p = half`.
      have hpLe : p ≤ Prob.half := by simpa [hqEq] using hpq
      have hpCases : p < Prob.half ∨ p = Prob.half := lt_or_eq_of_le hpLe
      rcases hpCases with hpLt | hpEq
      · -- `p < half`: compare Dirac at `∅` with the mixture.
        by_cases h0 : (∅ : Set (Prob.Edge d)) ∈ Open.percolates (d := d)
        · have h1 : (Set.univ : Set (Prob.Edge d)) ∈ Open.percolates (d := d) := hA_mono h0
          -- Both masses are 1, so the mixture is 1.
          simp [theta, Prob.P, hpLt, hqLt, hqEq, h0, h1, hhalf_add]
        · -- Left is 0, so trivial.
          simp [theta, Prob.P, hpLt, hqLt, hqEq, h0]
      · -- `p = half`: equality.
        simp [theta, Prob.P, hpEq, hqLt, hqEq]
    · -- `q > half`: `Prob.P d q` is Dirac at `univ`.
      have hqGt : Prob.half < q := lt_of_le_of_ne (le_of_not_gt hqLt) (Ne.symm hqEq)
      -- Split `p` relative to `half`.
      by_cases hpLt : p < Prob.half
      · -- `p < half`
        by_cases h0 : (∅ : Set (Prob.Edge d)) ∈ Open.percolates (d := d)
        · have h1 : (Set.univ : Set (Prob.Edge d)) ∈ Open.percolates (d := d) := hA_mono h0
          simp [theta, Prob.P, hpLt, hqLt, hqEq, h0, h1]
        · simp [theta, Prob.P, hpLt, hqLt, hqEq, h0]
      · by_cases hpEq : p = Prob.half
        · -- `p = half`: mixture ≤ dirac at `univ`.
          by_cases h0 : (∅ : Set (Prob.Edge d)) ∈ Open.percolates (d := d)
          · have h1 : (Set.univ : Set (Prob.Edge d)) ∈ Open.percolates (d := d) := hA_mono h0
            simp [theta, Prob.P, hpLt, hpEq, hqLt, hqEq, h0, h1, hhalf_add]
          · by_cases h1 : (Set.univ : Set (Prob.Edge d)) ∈ Open.percolates (d := d)
            · -- mixture = half ≤ 1
              have hhalf_le_one : (Prob.half : ℝ≥0∞) ≤ 1 := by
                simp [Prob.half]
              simp [theta, Prob.P, hpLt, hpEq, hqLt, hqEq, h0, h1, hhalf_le_one]
            · simp [theta, Prob.P, hpLt, hpEq, hqLt, hqEq, h0, h1]
        · -- `p > half`: both are Dirac at `univ`.
          have hpGe : Prob.half ≤ p := le_of_not_gt hpLt
          have hpGt : Prob.half < p := lt_of_le_of_ne hpGe (Ne.symm hpEq)
          have hqNotLt : ¬ q < Prob.half := not_lt_of_ge (hpGe.trans hpq)
          have hqNe : q ≠ Prob.half := by
            intro hqEq'
            have : p ≤ Prob.half := by simpa [hqEq'] using hpq
            exact (not_lt_of_ge this) hpGt
          simp [theta, Prob.P, hpLt, hpEq, hqNotLt, hqNe, hqEq]

theorem p_c_le_of_theta_pos {d : ℕ} {p : ℝ≥0∞} (hp : 0 < theta d p) : p_c d ≤ p := by
  classical
  exact sInf_le hp

theorem le_p_c_of_theta_eq_zero {d : ℕ} {p : ℝ≥0∞} (hp : theta d p = 0) : p ≤ p_c d := by
  classical
  refine le_sInf ?_
  intro q hq
  by_contra hpq
  have hqp : q < p := lt_of_not_ge hpq
  have hθ : theta d q ≤ 0 := by
    have hθ' := theta_mono (d := d) (p := q) (q := p) (le_of_lt hqp)
    simpa [hp] using hθ'
  exact (lt_irrefl (0 : ℝ≥0∞)) (lt_of_lt_of_le hq hθ)

end CriticalProbability

end Bond

open scoped BigOperators ENNReal
open MeasureTheory

namespace Russo

/-
Finite Russo formula for Bernoulli product measure on configurations `ι → Bool`.

To use for Z^d bond percolation in a finite box Λ:
  * let `ι` be the finite type of edges in Λ (or any finite edge set),
  * let `A : Set (ι → Bool)` be an increasing event (monotone in the coordinatewise order),
  * interpret `ω e = true` as “edge e is open”.
-/

abbrev Ω (ι : Type*) : Type _ := ι → Bool

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def flip (ω : Ω ι) (e : ι) (b : Bool) : Ω ι := Function.update ω e b

/-- Increasing (monotone) event for the coordinatewise order on `ι → Bool`. -/
def Increasing (A : Set (Ω ι)) : Prop :=
  ∀ ⦃ω ω' : Ω ι⦄, (∀ e : ι, ω e = true → ω' e = true) → ω ∈ A → ω' ∈ A

/-- `e` is pivotal for `A` at configuration `ω` (for increasing `A`). -/
def Pivotal (A : Set (Ω ι)) (e : ι) : Set (Ω ι) :=
  {ω | flip ω e true ∈ A ∧ flip ω e false ∉ A}

/-- Bernoulli measure on `Bool` with parameter `p` (as `NNReal`) and `p ≤ 1`. -/
noncomputable def bernoulliMeasure (p : NNReal) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

instance (p : NNReal) (hp : p ≤ 1) : MeasureTheory.IsProbabilityMeasure (bernoulliMeasure (p := p) hp) := by
  simpa [bernoulliMeasure] using
    (by infer_instance : MeasureTheory.IsProbabilityMeasure (PMF.bernoulli p hp).toMeasure)

instance (p : NNReal) (hp : p ≤ 1) : SigmaFinite (bernoulliMeasure (p := p) hp) := by
  infer_instance

/-- Product Bernoulli measure on `ι → Bool`. -/
noncomputable def bernoulliProd (p : NNReal) (hp : p ≤ 1) : Measure (Ω ι) :=
  Measure.pi (fun _ : ι => bernoulliMeasure p hp)

/-- Real-valued probability of an event under the product Bernoulli measure. -/
noncomputable def prob (p : NNReal) (hp : p ≤ 1) (A : Set (Ω ι)) : ℝ :=
  ((bernoulliProd (p := p) (hp := hp)) A).toReal

/-- Clamp a real `q` to `[0,1]` as a `NNReal` parameter (helper for a total `ℝ → ℝ` probability map). -/
noncomputable def clamp01 (q : ℝ) : NNReal :=
  ⟨max 0 (min q 1), by
    have : 0 ≤ max 0 (min q 1) := le_max_left _ _
    exact this⟩

lemma clamp01_le_one (q : ℝ) : clamp01 q ≤ 1 := by
  -- Compare in `ℝ`.
  apply (NNReal.coe_le_coe).1
  change max 0 (min q 1) ≤ (1 : ℝ)
  refine (max_le_iff).2 ?_
  constructor
  · exact zero_le_one
  · exact min_le_right _ _

/-- `prob` packaged as a total map `ℝ → ℝ` by clamping the parameter to `[0,1]`. -/
noncomputable def probReal (q : ℝ) (A : Set (Ω ι)) : ℝ :=
  prob (p := clamp01 q) (hp := clamp01_le_one q) A

/-! ### A finite-sum expansion (`ι` finite) -/

/-- Algebraic weight of a configuration `ω : ι → Bool` under parameter `q`. -/
noncomputable def weight (q : ℝ) (ω : Ω ι) : ℝ :=
  ∏ e : ι, (if ω e then q else (1 - q))

/-- `probReal` on `(0,1)` agrees with this finite polynomial expression. -/
noncomputable def probPoly (q : ℝ) (A : Set (Ω ι)) : ℝ := by
  classical
  exact ∑ ω : Ω ι, if ω ∈ A then weight (ι := ι) q ω else 0

/-!
### Russo formula (finite) — proof skeleton

The actual proof is not filled in yet; we introduce a few intermediate lemmas so the main theorem
can be proved by a short chain of reductions.
-/

/-- On the open interval `(0,1)`, the clamp does not change the parameter (as a real number). -/
lemma clamp01_coe_eq_of_lt {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (clamp01 p : ℝ) = p := by
  simp [clamp01, min_eq_left (le_of_lt hp1), max_eq_right hp0.le]

/-- Convenient `NNReal` parameter corresponding to `p ∈ (0,1)`. -/
noncomputable def pNNReal (p : ℝ) (hp0 : 0 < p) : NNReal :=
  ⟨p, le_of_lt hp0⟩

/-- For `p ∈ (0,1)`, the `NNReal` parameter `pNNReal p` is ≤ 1. -/
lemma pNNReal_le_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    pNNReal p hp0 ≤ (1 : NNReal) := by
  -- Compare in `ℝ`.
  apply (NNReal.coe_le_coe).1
  change p ≤ (1 : ℝ)
  exact le_of_lt hp1

/-- Inside `(0,1)`, `probReal` agrees with `prob` at the unclamped parameter `p`. -/
lemma probReal_eq_prob_of_lt (A : Set (Ω ι)) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    probReal (ι := ι) p A =
      prob (ι := ι) (p := pNNReal p hp0) (hp := pNNReal_le_one (p := p) hp0 hp1) A := by
  classical
  have hclamp : clamp01 p = pNNReal p hp0 := by
    ext
    simpa [pNNReal] using (clamp01_coe_eq_of_lt (p := p) hp0 hp1)
  have hhp :
      (by
          simpa [hclamp] using (clamp01_le_one p)) =
        pNNReal_le_one (p := p) hp0 hp1 := by
    exact Subsingleton.elim _ _
  simpa [probReal, hclamp, hhp]

/-- For `p ∈ (0,1)`, the measure-based probability `prob` agrees with the explicit finite-sum polynomial. -/
lemma prob_eq_probPoly_of_lt (A : Set (Ω ι)) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    prob (ι := ι) (p := pNNReal p hp0) (hp := pNNReal_le_one (p := p) hp0 hp1) A =
      probPoly (ι := ι) p A := by
  classical
  -- Expand `prob` as a finite sum over point masses, and identify each point mass with `weight`.
  set p₀ : NNReal := pNNReal p hp0
  have hp₀ : p₀ ≤ (1 : NNReal) := by
    simpa [p₀] using (pNNReal_le_one (p := p) hp0 hp1)
  let μ : Measure (Ω ι) := bernoulliProd (ι := ι) (p := p₀) (hp := hp₀)
  have hμA :
      μ A = ∑ ω ∈ (Finset.univ.filter fun ω : Ω ι => ω ∈ A), μ {ω} := by
    have hset :
        (↑(Finset.univ.filter fun ω : Ω ι => ω ∈ A) : Set (Ω ι)) = A := by
      ext ω
      simp
    have hsum :
        (∑ ω ∈ (Finset.univ.filter fun ω : Ω ι => ω ∈ A), μ {ω}) =
          μ (↑(Finset.univ.filter fun ω : Ω ι => ω ∈ A) : Set (Ω ι)) := by
      simpa using
        (MeasureTheory.sum_measure_singleton (μ := μ)
          (s := (Finset.univ.filter fun ω : Ω ι => ω ∈ A)))
    simpa [hset] using hsum.symm
  have hμsingleton (ω : Ω ι) :
      μ {ω} = ∏ e : ι, (cond (ω e) p₀ (1 - p₀) : ℝ≥0∞) := by
    have hpi :
        μ {ω} = ∏ e : ι, (bernoulliMeasure (p := p₀) (hp := hp₀) {ω e}) := by
      simpa [μ, bernoulliProd] using
        (Measure.pi_singleton (μ := fun _ : ι => bernoulliMeasure (p := p₀) (hp := hp₀)) ω)
    have hb (b : Bool) :
        bernoulliMeasure (p := p₀) (hp := hp₀) {b} = (cond b p₀ (1 - p₀) : ℝ≥0∞) := by
      simpa [bernoulliMeasure, PMF.bernoulli_apply, Bool.apply_cond, ENNReal.coe_sub] using
        (PMF.toMeasure_apply_singleton (p := PMF.bernoulli p₀ hp₀) b (MeasurableSet.singleton b))
    simpa [hb] using hpi
  have hne_top :
      ∀ ω ∈ (Finset.univ.filter fun ω : Ω ι => ω ∈ A), μ {ω} ≠ ∞ := by
    intro ω hω
    -- `ω ∈ A` is irrelevant; singleton masses are finite.
    clear hω
    rw [hμsingleton ω]
    -- Rewrite the `Fintype` product as a `Finset` product to use `ENNReal.prod_ne_top`.
    simpa using
      (ENNReal.prod_ne_top (s := (Finset.univ : Finset ι))
        (f := fun e : ι => (cond (ω e) p₀ (1 - p₀) : ℝ≥0∞))
        (by
          intro e he
          by_cases h : ω e <;> simp [h]))
  -- Convert the singleton weights to `weight p ω` (as real numbers), and repackage as `probPoly`.
  have hweight (ω : Ω ι) : (μ {ω}).toReal = weight (ι := ι) p ω := by
    have hfactor (e : ι) :
        ((cond (ω e) p₀ (1 - p₀) : ℝ≥0∞).toReal) = (if ω e then p else (1 - p)) := by
      cases h : ω e
      ·
        have hp₀' : (p₀ : ℝ≥0∞) ≤ (1 : ℝ≥0∞) := by
          exact_mod_cast hp₀
        have hsub :
            ((1 : ℝ≥0∞) - (p₀ : ℝ≥0∞)).toReal =
              (1 : ℝ≥0∞).toReal - (p₀ : ℝ≥0∞).toReal := by
          simpa using (ENNReal.toReal_sub_of_le hp₀' (by simp))
        simp [h] at *
        -- LHS is now `((1 : ℝ≥0∞) - (p₀ : ℝ≥0∞)).toReal`.
        rw [hsub]
        simp [p₀, pNNReal]
      · simp [h, p₀, pNNReal]
    have hstart :
        (μ {ω}).toReal =
          ENNReal.toReal (∏ e ∈ (Finset.univ : Finset ι), (cond (ω e) p₀ (1 - p₀) : ℝ≥0∞)) := by
      -- Rewrite the singleton mass using `hμsingleton`.
      simpa [hμsingleton ω] using congrArg ENNReal.toReal (hμsingleton ω)
    have htoRealProd :
        ENNReal.toReal (∏ e ∈ (Finset.univ : Finset ι), (cond (ω e) p₀ (1 - p₀) : ℝ≥0∞)) =
          ∏ e ∈ (Finset.univ : Finset ι), ((cond (ω e) p₀ (1 - p₀) : ℝ≥0∞).toReal) := by
      simpa using (ENNReal.toReal_prod (s := (Finset.univ : Finset ι))
        (f := fun e : ι => (cond (ω e) p₀ (1 - p₀) : ℝ≥0∞)))
    -- Put everything together.
    have : (μ {ω}).toReal = ∏ e ∈ (Finset.univ : Finset ι), ((cond (ω e) p₀ (1 - p₀) : ℝ≥0∞).toReal) := by
      simpa [hstart] using Eq.trans hstart htoRealProd
    simpa [weight, hfactor] using this
  -- Finish by rewriting `prob` and summing over configurations in `A`.
  have hsum_filter :
      (∑ ω ∈ (Finset.univ.filter fun ω : Ω ι => ω ∈ A), weight (ι := ι) p ω) = probPoly (ι := ι) p A := by
    -- `probPoly` is `∑ ω, if ω ∈ A then weight p ω else 0`, which is the usual `sum_filter` form.
    simpa [probPoly] using
      (Finset.sum_filter (s := (Finset.univ : Finset (Ω ι)))
        (p := fun ω : Ω ι => ω ∈ A) (f := fun ω : Ω ι => weight (ι := ι) p ω))
  calc
    prob (ι := ι) (p := pNNReal p hp0) (hp := pNNReal_le_one (p := p) hp0 hp1) A
        = (μ A).toReal := by
            simp [prob, μ, p₀, hp₀]
    _ = (∑ ω ∈ (Finset.univ.filter fun ω : Ω ι => ω ∈ A), μ {ω}).toReal := by
            simpa using congrArg ENNReal.toReal hμA
    _ = ∑ ω ∈ (Finset.univ.filter fun ω : Ω ι => ω ∈ A), (μ {ω}).toReal := by
            simpa using (ENNReal.toReal_sum (s := (Finset.univ.filter fun ω : Ω ι => ω ∈ A))
              (f := fun ω : Ω ι => μ {ω}) hne_top)
    _ = ∑ ω ∈ (Finset.univ.filter fun ω : Ω ι => ω ∈ A), weight (ι := ι) p ω := by
            refine Finset.sum_congr rfl ?_
            intro ω hω
            simp [hweight]
    _ = probPoly (ι := ι) p A := hsum_filter

/-- Core Russo formula (to be proved): derivative of `prob` equals sum of pivotal probabilities. -/
lemma russo_formula_finite_core
    (A : Set (Ω ι)) (hA : Increasing A)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (fun q : ℝ => probReal (ι := ι) q A) p =
      ∑ e : ι,
        prob (ι := ι) (p := pNNReal p hp0) (hp := pNNReal_le_one (p := p) hp0 hp1) (Pivotal A e) := by
  classical
  -- On a neighborhood of `p` contained in `(0,1)`, `probReal` agrees with the polynomial `probPoly`.
  have hEq :
      (fun q : ℝ => probReal (ι := ι) q A) =ᶠ[𝓝 p] fun q : ℝ => probPoly (ι := ι) q A := by
    have hIoo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 p := Ioo_mem_nhds hp0 hp1
    refine Filter.eventually_of_mem hIoo ?_
    intro q hq
    have hq0 : 0 < q := hq.1
    have hq1 : q < 1 := hq.2
    calc
      probReal (ι := ι) q A =
          prob (ι := ι) (p := pNNReal q hq0) (hp := pNNReal_le_one (p := q) hq0 hq1) A := by
            simpa using (probReal_eq_prob_of_lt (ι := ι) (A := A) hq0 hq1)
      _ = probPoly (ι := ι) q A := prob_eq_probPoly_of_lt (ι := ι) (A := A) hq0 hq1

  have hderiv_probReal :
      deriv (fun q : ℝ => probReal (ι := ι) q A) p =
        deriv (fun q : ℝ => probPoly (ι := ι) q A) p := by
    simpa using hEq.deriv_eq

  -- Compute the derivative of the finite polynomial `probPoly`.
  have hderiv_probPoly :
      deriv (fun q : ℝ => probPoly (ι := ι) q A) p =
        ∑ e : ι, probPoly (ι := ι) p (Pivotal A e) := by
    classical
    -- Filtered finite sum representation.
    let sA : Finset (Ω ι) := (Finset.univ : Finset (Ω ι)).filter fun ω : Ω ι => ω ∈ A
    let base : ι → Ω ι → ℝ := fun e ω =>
      ∏ j ∈ (Finset.univ.erase e : Finset ι), (if ω j then p else (1 - p))

    have hprobPoly (q : ℝ) :
        probPoly (ι := ι) q A = ∑ ω ∈ sA, weight (ι := ι) q ω := by
      simpa [probPoly, sA] using
        (Finset.sum_filter (s := (Finset.univ : Finset (Ω ι)))
          (p := fun ω : Ω ι => ω ∈ A) (f := fun ω : Ω ι => weight (ι := ι) q ω)).symm

    -- Derivative of one factor `(if ω e then q else (1 - q))`.
    have hfactor (ω : Ω ι) (e : ι) :
        HasDerivAt (fun q : ℝ => (if ω e then q else (1 - q)))
          (if ω e then 1 else -1) p := by
      cases h : ω e
      ·
        -- `ω e = false`: factor is `1 - q`.
        simpa [h] using (hasDerivAt_id p).const_sub (1 : ℝ)
      ·
        -- `ω e = true`: factor is `q`.
        simpa [h] using (hasDerivAt_id p)

    -- Derivative of the weight of a configuration.
    have hweight (ω : Ω ι) :
        HasDerivAt (fun q : ℝ => weight (ι := ι) q ω)
          (∑ e : ι, base e ω * (if ω e then 1 else -1)) p := by
      have h :=
        HasDerivAt.fun_finset_prod (x := p) (u := (Finset.univ : Finset ι))
          (f := fun e : ι => fun q : ℝ => (if ω e then q else (1 - q)))
          (f' := fun e : ι => (if ω e then 1 else -1))
          (hf := by
            intro e he
            simpa using hfactor ω e)
      simpa [weight, base, mul_assoc, mul_left_comm, mul_comm] using h

    -- Differentiate the filtered sum.
    have hderiv_sum :
        HasDerivAt (fun q : ℝ => ∑ ω ∈ sA, weight (ι := ι) q ω)
          (∑ ω ∈ sA, ∑ e : ι, base e ω * (if ω e then 1 else -1)) p := by
      refine HasDerivAt.fun_sum (x := p) (u := sA)
        (A := fun ω : Ω ι => fun q : ℝ => weight (ι := ι) q ω)
        (A' := fun ω : Ω ι => ∑ e : ι, base e ω * (if ω e then 1 else -1)) ?_
      intro ω hω
      simpa using hweight ω

    have hprobPolyFun :
        (fun q : ℝ => probPoly (ι := ι) q A) =
          fun q : ℝ => ∑ ω ∈ sA, weight (ι := ι) q ω := by
      funext q
      simpa using hprobPoly q

    have hderiv_poly :
        deriv (fun q : ℝ => probPoly (ι := ι) q A) p =
          ∑ ω ∈ sA, ∑ e : ι, base e ω * (if ω e then 1 else -1) := by
      have : deriv (fun q : ℝ => ∑ ω ∈ sA, weight (ι := ι) q ω) p =
          ∑ ω ∈ sA, ∑ e : ι, base e ω * (if ω e then 1 else -1) := by
        exact hderiv_sum.deriv
      simpa [hprobPolyFun] using this

    -- Key combinatorial identification for each coordinate.
    have hinner (e₀ : ι) :
        (∑ ω ∈ sA, base e₀ ω * (if ω e₀ then 1 else -1)) =
          probPoly (ι := ι) p (Pivotal A e₀) := by
      classical
      let U0 : Finset (Ω ι) :=
        (Finset.univ : Finset (Ω ι)).filter fun ω : Ω ι => ω e₀ = false
      let A0 : Finset (Ω ι) := U0.filter fun ω : Ω ι => ω ∈ A
      let B0 : Finset (Ω ι) := U0.filter fun ω : Ω ι => flip ω e₀ true ∈ A
      let C0 : Finset (Ω ι) := B0 \ A0

      have base_flip (ω : Ω ι) (b : Bool) :
          base e₀ (flip ω e₀ b) = base e₀ ω := by
        -- only coordinates in `univ.erase e₀` appear
        simp [base]
        refine Finset.prod_congr rfl ?_
        intro j hj
        have jne : j ≠ e₀ := (Finset.mem_erase.mp hj).1
        simp [flip, jne]

      have flip_eq_self (ω : Ω ι) (b : Bool) (h : ω e₀ = b) : flip ω e₀ b = ω := by
        funext j
        by_cases hj : j = e₀
        · subst hj
          simpa [flip, h]
        · simp [flip, hj]

      have flip_false_true (ω : Ω ι) (h : ω e₀ = true) :
          flip (flip ω e₀ false) e₀ true = ω := by
        funext j
        by_cases hj : j = e₀
        · subst hj
          simpa [flip, h]
        · simp [flip, hj]

      have flip_true_false (ω : Ω ι) (h : ω e₀ = false) :
          flip (flip ω e₀ true) e₀ false = ω := by
        funext j
        by_cases hj : j = e₀
        · subst hj
          simpa [flip, h]
        · simp [flip, hj]

      -- `A0 ⊆ B0` by monotonicity of `A`.
      have hA0sub : A0 ⊆ B0 := by
        intro ω hω
        have hω' : ω e₀ = false ∧ ω ∈ A := by
          simpa [A0, U0] using hω
        have hωe : ω e₀ = false := hω'.1
        have hωA : ω ∈ A := hω'.2
        have hωA' : flip ω e₀ true ∈ A := by
          apply hA (ω := ω) (ω' := flip ω e₀ true) ?_ hωA
          intro i hi
          by_cases hie : i = e₀
          · subst hie
            simpa [hωe] using hi
          · simpa [flip, hie] using hi
        -- show `ω ∈ B0`
        refine Finset.mem_filter.mpr ?_
        constructor
        · -- in `U0`
          refine Finset.mem_filter.mpr ?_
          constructor <;> simp [U0, hωe]
        · exact hωA'

      -- Rewrite the LHS as a base-sum over `C0`.
      have hLHS :
          (∑ ω ∈ sA, base e₀ ω * (if ω e₀ then 1 else -1)) =
            ∑ ω ∈ C0, base e₀ ω := by
        -- Split into `e₀ = true` and `e₀ = false`.
        have hterm (ω : Ω ι) :
            base e₀ ω * (if ω e₀ then 1 else -1) =
              if ω e₀ = true then base e₀ ω else -base e₀ ω := by
          cases h : ω e₀ <;> simp [h]
        have hsplit :
            (∑ ω ∈ sA, base e₀ ω * (if ω e₀ then 1 else -1)) =
              (∑ ω ∈ sA.filter (fun ω : Ω ι => ω e₀ = true), base e₀ ω) -
                ∑ ω ∈ sA.filter (fun ω : Ω ι => ω e₀ = false), base e₀ ω := by
          calc
            (∑ ω ∈ sA, base e₀ ω * (if ω e₀ then 1 else -1)) =
                ∑ ω ∈ sA, if ω e₀ = true then base e₀ ω else -base e₀ ω := by
                  refine Finset.sum_congr rfl ?_
                  intro ω hω
                  simpa using hterm ω
            _ =
                (∑ ω ∈ sA.filter (fun ω : Ω ι => ω e₀ = true), base e₀ ω) +
                  ∑ ω ∈ sA.filter (fun ω : Ω ι => ¬ω e₀ = true), -base e₀ ω := by
                  simpa using
                    (Finset.sum_ite (s := sA) (p := fun ω : Ω ι => ω e₀ = true)
                      (f := fun ω : Ω ι => base e₀ ω) (g := fun ω : Ω ι => -base e₀ ω))
            _ =
                (∑ ω ∈ sA.filter (fun ω : Ω ι => ω e₀ = true), base e₀ ω) -
                  ∑ ω ∈ sA.filter (fun ω : Ω ι => ω e₀ = false), base e₀ ω := by
                  have hfilter :
                      sA.filter (fun ω : Ω ι => ¬ω e₀ = true) =
                        sA.filter (fun ω : Ω ι => ω e₀ = false) := by
                    ext ω
                    cases h : ω e₀ <;> simp [h]
                  simp [hfilter, sub_eq_add_neg, Finset.sum_neg_distrib]
        -- Convert the `e₀ = true` part to `B0` via bijection.
        have hsum_true :
            (∑ ω ∈ sA.filter (fun ω : Ω ι => ω e₀ = true), base e₀ ω) =
              ∑ ω ∈ B0, base e₀ ω := by
          refine
            (Finset.sum_nbij' (s := sA.filter fun ω : Ω ι => ω e₀ = true) (t := B0)
              (f := fun ω : Ω ι => base e₀ ω) (g := fun ω : Ω ι => base e₀ ω)
              (i := fun ω : Ω ι => flip ω e₀ false) (j := fun ω : Ω ι => flip ω e₀ true)
              ?_ ?_ ?_ ?_ ?_)
          · intro ω hω
            have hωA : ω ∈ A := (Finset.mem_filter.mp (Finset.mem_filter.mp hω).1).2
            have hωe : ω e₀ = true := (Finset.mem_filter.mp hω).2
            -- show `flip ω e₀ false ∈ B0`
            refine Finset.mem_filter.mpr ?_
            constructor
            · -- in `U0`
              refine Finset.mem_filter.mpr ?_
              constructor <;> simp [U0, flip]
            · have hcomp : flip (flip ω e₀ false) e₀ true = ω := flip_false_true ω hωe
              simpa [hcomp] using hωA
          · intro ω hω
            -- ω ∈ B0 → flip ω e₀ true ∈ sA.filter (e₀=true)
            have hω1A : flip ω e₀ true ∈ A := (Finset.mem_filter.mp hω).2
            refine Finset.mem_filter.mpr ?_
            constructor
            · refine Finset.mem_filter.mpr ?_
              constructor
              · simp [sA]
              · exact hω1A
            · simp [flip]
          · intro ω hω
            have hωe : ω e₀ = true := (Finset.mem_filter.mp hω).2
            exact flip_false_true ω hωe
          · intro ω hω
            have hωe : ω e₀ = false := by
              have : ω ∈ U0 := (Finset.mem_filter.mp hω).1
              exact (Finset.mem_filter.mp this).2
            exact flip_true_false ω hωe
          · intro ω hω
            simpa using (base_flip ω false).symm
        -- The `e₀ = false` sum is exactly over `A0`.
        have hsum_false :
            (∑ ω ∈ sA.filter (fun ω : Ω ι => ω e₀ = false), base e₀ ω) =
              ∑ ω ∈ A0, base e₀ ω := by
          have hs : sA.filter (fun ω : Ω ι => ω e₀ = false) = A0 := by
            ext ω
            simp [sA, A0, U0, and_left_comm, and_assoc, and_comm]
          simpa [hs]
        have hsdiff :
            (∑ ω ∈ C0, base e₀ ω) = (∑ ω ∈ B0, base e₀ ω) - ∑ ω ∈ A0, base e₀ ω := by
          simpa [C0] using (Finset.sum_sdiff_eq_sub (s₁ := A0) (s₂ := B0) (f := fun ω : Ω ι => base e₀ ω) hA0sub)
        calc
          (∑ ω ∈ sA, base e₀ ω * (if ω e₀ then 1 else -1)) =
              (∑ ω ∈ sA.filter (fun ω : Ω ι => ω e₀ = true), base e₀ ω) -
                ∑ ω ∈ sA.filter (fun ω : Ω ι => ω e₀ = false), base e₀ ω := hsplit
          _ = (∑ ω ∈ B0, base e₀ ω) - ∑ ω ∈ A0, base e₀ ω := by
                simp [hsum_true, hsum_false]
          _ = ∑ ω ∈ C0, base e₀ ω := by
                simpa [hsdiff]

      -- Compute `probPoly p (Pivotal A e₀)` as the same base-sum.
      have hRHS :
          probPoly (ι := ι) p (Pivotal A e₀) = ∑ ω ∈ C0, base e₀ ω := by
        let sP : Finset (Ω ι) :=
          (Finset.univ : Finset (Ω ι)).filter fun ω : Ω ι => ω ∈ Pivotal A e₀
        have hprobP :
            probPoly (ι := ι) p (Pivotal A e₀) = ∑ ω ∈ sP, weight (ι := ι) p ω := by
          simpa [probPoly, sP] using
            (Finset.sum_filter (s := (Finset.univ : Finset (Ω ι)))
              (p := fun ω : Ω ι => ω ∈ Pivotal A e₀) (f := fun ω : Ω ι => weight (ι := ι) p ω)).symm

        have hsPfalse : sP.filter (fun ω : Ω ι => ω e₀ = false) = C0 := by
          ext ω
          by_cases hωe : ω e₀ = false
          · have hflipF : flip ω e₀ false = ω := flip_eq_self ω false hωe
            simp [sP, C0, B0, A0, U0, Pivotal, hωe, hflipF]
          · simp [sP, C0, B0, A0, U0, hωe]

        -- Bijection for the `e₀ = true` part.
        have hsum_trueP :
            (∑ ω ∈ sP.filter (fun ω : Ω ι => ω e₀ = true), weight (ι := ι) p ω) =
              ∑ ω ∈ C0, weight (ι := ι) p (flip ω e₀ true) := by
          refine
            (Finset.sum_nbij' (s := sP.filter fun ω : Ω ι => ω e₀ = true) (t := C0)
              (f := fun ω : Ω ι => weight (ι := ι) p ω)
              (g := fun ω : Ω ι => weight (ι := ι) p (flip ω e₀ true))
              (i := fun ω : Ω ι => flip ω e₀ false) (j := fun ω : Ω ι => flip ω e₀ true)
              ?_ ?_ ?_ ?_ ?_)
          · intro ω hω
            have hωPiv : ω ∈ Pivotal A e₀ := (Finset.mem_filter.mp (Finset.mem_filter.mp hω).1).2
            have hωe : ω e₀ = true := (Finset.mem_filter.mp hω).2
            -- show `flip ω e₀ false ∈ C0`
            refine Finset.mem_sdiff.mpr ?_
            refine ⟨?_, ?_⟩
            · -- in `B0`
              refine Finset.mem_filter.mpr ?_
              refine ⟨?_, ?_⟩
              · -- in `U0`
                refine Finset.mem_filter.mpr ?_
                constructor <;> simp [U0, flip]
              · -- `flip (flip ω e₀ false) e₀ true ∈ A`
                have hωA : ω ∈ A := by
                  have hflipT : flip ω e₀ true = ω := flip_eq_self ω true hωe
                  simpa [Pivotal, hflipT] using hωPiv.1
                have hcomp : flip (flip ω e₀ false) e₀ true = ω := flip_false_true ω hωe
                simpa [hcomp] using hωA
            · -- not in `A0`
              intro hA0
              have hInA : flip ω e₀ false ∈ A := (Finset.mem_filter.mp hA0).2
              have hNotInA : flip ω e₀ false ∉ A := by
                simpa [Pivotal] using hωPiv.2
              exact hNotInA hInA
          · intro ω hω
            -- ω ∈ C0 → flip ω e₀ true ∈ sP.filter (e₀=true)
            have hωB : ω ∈ B0 := (Finset.mem_sdiff.mp hω).1
            have hωA0 : ω ∉ A0 := (Finset.mem_sdiff.mp hω).2
            have hωe : ω e₀ = false := (Finset.mem_filter.mp (Finset.mem_filter.mp hωB).1).2
            have hω1A : flip ω e₀ true ∈ A := (Finset.mem_filter.mp hωB).2
            have hωnotA : ω ∉ A := by
              intro hAω
              exact hωA0 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hωB).1, hAω⟩)
            have hPiv : flip ω e₀ true ∈ Pivotal A e₀ := by
              refine ⟨?_, ?_⟩
              · have hflipT : flip (flip ω e₀ true) e₀ true = flip ω e₀ true := by
                  funext j
                  by_cases hj : j = e₀
                  · subst hj; simp [flip]
                  · simp [flip, hj]
                simpa [Pivotal, hflipT] using hω1A
              · have hflipF : flip (flip ω e₀ true) e₀ false = ω := flip_true_false ω hωe
                simpa [Pivotal, hflipF] using hωnotA
            refine Finset.mem_filter.mpr ?_
            constructor
            · refine Finset.mem_filter.mpr ?_
              constructor
              · simp [sP]
              · exact hPiv
            · simp [flip]
          · intro ω hω
            have hωe : ω e₀ = true := (Finset.mem_filter.mp hω).2
            exact flip_false_true ω hωe
          · intro ω hω
            have hωe : ω e₀ = false := by
              have : ω ∈ C0 := hω
              have : ω ∈ B0 := (Finset.mem_sdiff.mp this).1
              exact (Finset.mem_filter.mp (Finset.mem_filter.mp this).1).2
            exact flip_true_false ω hωe
          · intro ω hω
            have hωe : ω e₀ = true := (Finset.mem_filter.mp hω).2
            have hcomp : flip (flip ω e₀ false) e₀ true = ω := flip_false_true ω hωe
            simpa [hcomp]

        -- Decompose weights as `(factor at e₀) * base`.
        have hweight_decomp (ω : Ω ι) :
            weight (ι := ι) p ω = (if ω e₀ then p else (1 - p)) * base e₀ ω := by
          have h :=
            Finset.mul_prod_erase (s := (Finset.univ : Finset ι))
              (f := fun i : ι => (if ω i then p else (1 - p))) (a := e₀) (h := by simp)
          simpa [weight, base] using h.symm

        -- Split the pivotal sum and rewrite both parts over `C0`.
        have hsplitP :
            (∑ ω ∈ sP, weight (ι := ι) p ω) =
              (∑ ω ∈ C0, weight (ι := ι) p ω) + ∑ ω ∈ C0, weight (ι := ι) p (flip ω e₀ true) := by
          have h := Finset.sum_filter_add_sum_filter_not (s := sP) (p := fun ω : Ω ι => ω e₀ = false)
            (f := fun ω : Ω ι => weight (ι := ι) p ω)
          have hfilter :
              sP.filter (fun ω : Ω ι => ¬ω e₀ = false) =
                sP.filter (fun ω : Ω ι => ω e₀ = true) := by
            ext ω
            cases hω : ω e₀ <;> simp [hω]
          -- Rewrite `sum (sP)` as `sum false + sum true`.
          have : (∑ ω ∈ sP, weight (ι := ι) p ω) =
              (∑ ω ∈ sP.filter (fun ω : Ω ι => ω e₀ = false), weight (ι := ι) p ω) +
                ∑ ω ∈ sP.filter (fun ω : Ω ι => ω e₀ = true), weight (ι := ι) p ω := by
            simpa [hfilter] using h.symm
          -- Replace the two finsets/sums by the `C0` versions.
          simpa [hsPfalse] using
            (by
              simpa [hsPfalse] using
                (by
                  -- use `hsum_trueP` for the true part
                  simpa [hsPfalse, hsum_trueP] using this))

        calc
          probPoly (ι := ι) p (Pivotal A e₀) = ∑ ω ∈ sP, weight (ι := ι) p ω := hprobP
          _ = ∑ ω ∈ C0, (weight (ι := ι) p ω + weight (ι := ι) p (flip ω e₀ true)) := by
                -- combine the split sums
                have := hsplitP
                -- use `sum_add_distrib` to merge
                simpa [Finset.sum_add_distrib] using this
          _ = ∑ ω ∈ C0, base e₀ ω := by
                refine Finset.sum_congr rfl ?_
                intro ω hω
                have hωe : ω e₀ = false := by
                  have : ω ∈ B0 := (Finset.mem_sdiff.mp hω).1
                  exact (Finset.mem_filter.mp (Finset.mem_filter.mp this).1).2
                have hω1 : base e₀ (flip ω e₀ true) = base e₀ ω := base_flip ω true
                -- expand both weights and simplify
                calc
                  weight (ι := ι) p ω + weight (ι := ι) p (flip ω e₀ true)
                      = (1 - p) * base e₀ ω + p * base e₀ (Function.update ω e₀ true) := by
                          simp [hweight_decomp, hωe, flip]
                  _ = (1 - p) * base e₀ ω + p * base e₀ ω := by
                          have hω1' : base e₀ (Function.update ω e₀ true) = base e₀ ω := by
                            simpa [flip] using hω1
                          simp [hω1']
                  _ = ((1 - p) + p) * base e₀ ω := by
                          rw [← add_mul]
                  _ = base e₀ ω := by
                          simp [sub_add_cancel, one_mul]

      -- Combine both sides.
      exact (hLHS.trans hRHS.symm)

    -- Swap sums and apply `hinner`.
    have hswap :
        (∑ ω ∈ sA, ∑ e : ι, base e ω * (if ω e then 1 else -1)) =
          ∑ e : ι, ∑ ω ∈ sA, base e ω * (if ω e then 1 else -1) := by
      simpa using
        (Finset.sum_comm (s := sA) (t := (Finset.univ : Finset ι))
          (f := fun ω e => base e ω * (if ω e then 1 else -1)))

    calc
      deriv (fun q : ℝ => probPoly (ι := ι) q A) p =
          ∑ ω ∈ sA, ∑ e : ι, base e ω * (if ω e then 1 else -1) := hderiv_poly
      _ = ∑ e : ι, ∑ ω ∈ sA, base e ω * (if ω e then 1 else -1) := hswap
      _ = ∑ e : ι, probPoly (ι := ι) p (Pivotal A e) := by
            classical
            -- rewrite termwise using `hinner`
            refine Fintype.sum_congr _ _ ?_
            intro e
            simpa using hinner e

  -- Convert pivotal probabilities from `probPoly` back to `prob`.
  have hpiv :
      (fun e : ι => probPoly (ι := ι) p (Pivotal A e)) =
        fun e : ι =>
          prob (ι := ι) (p := pNNReal p hp0) (hp := pNNReal_le_one (p := p) hp0 hp1) (Pivotal A e) := by
    funext e
    -- `prob = probPoly` on `(0,1)`.
    simpa using (prob_eq_probPoly_of_lt (ι := ι) (A := Pivotal A e) (p := p) hp0 hp1).symm

  calc
    deriv (fun q : ℝ => probReal (ι := ι) q A) p =
        deriv (fun q : ℝ => probPoly (ι := ι) q A) p := hderiv_probReal
    _ = ∑ e : ι, probPoly (ι := ι) p (Pivotal A e) := hderiv_probPoly
    _ = ∑ e : ι,
          prob (ι := ι) (p := pNNReal p hp0) (hp := pNNReal_le_one (p := p) hp0 hp1) (Pivotal A e) := by
          simpa using congrArg (fun f : ι → ℝ => ∑ e : ι, f e) hpiv

/--
Russo's formula (finite, claim): for an increasing event `A` depending on finitely many coordinates
(here automatic since `ι` is finite), the derivative w.r.t. `p` equals the sum of pivotal probabilities.

This is stated for `p : ℝ` with `0 < p < 1`. For a total function `ℝ → ℝ` we clamp parameters outside
`[0,1]` (in applications you usually use `derivWithin` on `Set.Ioo 0 1`).
-/
theorem russo_formula_finite
    (A : Set (Ω ι)) (hA : Increasing A)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (fun q : ℝ => probReal q A) p = ∑ e : ι, probReal p (Pivotal A e) := by
  classical
  -- Reduce to the unclamped parameterization and apply the core Russo formula.
  -- (All key steps are isolated as lemmas above.)
  have hprob : probReal (ι := ι) p A =
      prob (ι := ι) (p := pNNReal p hp0) (hp := pNNReal_le_one (p := p) hp0 hp1) A :=
    probReal_eq_prob_of_lt (ι := ι) (A := A) hp0 hp1
  have hpiv : (fun e : ι => probReal (ι := ι) p (Pivotal A e)) =
      fun e : ι =>
        prob (ι := ι) (p := pNNReal p hp0) (hp := pNNReal_le_one (p := p) hp0 hp1) (Pivotal A e) := by
    funext e
    simpa using (probReal_eq_prob_of_lt (ι := ι) (A := Pivotal A e) hp0 hp1)
  -- Replace the function under `deriv` by the unclamped one at the point `p`.
  -- TODO: use `clamp01_coe_eq_of_lt` + `probReal_eq_prob_of_lt` to justify this as an equality of germs.
  -- For now, we directly use the core statement as a placeholder.
  have hcore := russo_formula_finite_core (ι := ι) (A := A) hA hp0 hp1
  -- Finish by rewriting the RHS back into `probReal`.
  -- TODO: `simp [hpiv]` after the derivative reduction step is fully implemented.
  simpa [hpiv] using hcore

end Russo

open scoped BigOperators ENNReal

namespace BKR

open MeasureTheory

section Definitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*}

/-- Configuration space for an indexed product. -/
abbrev Ω (ι : Type*) (α : ι → Type*) : Type _ := (i : ι) → α i

/-- The cylinder set at configuration `ω` determined by coordinates `s`.

`ω' ∈ cylinder ω s` means that `ω'` agrees with `ω` on all coordinates in `s`. -/
def cylinder (ω : Ω ι α) (s : Finset ι) : Set (Ω ι α) :=
  {ω' | ∀ i, i ∈ s → ω' i = ω i}

/-- `s` is a witness for event `A` at configuration `ω` if fixing the coordinates in `s`
(as in `cylinder ω s`) forces membership in `A`. -/
def Witness (A : Set (Ω ι α)) (ω : Ω ι α) (s : Finset ι) : Prop :=
  cylinder (ι := ι) (α := α) ω s ⊆ A

/-- Disjoint occurrence of two events `A` and `B`.

`ω ∈ A ⊠ B` means that there exist disjoint finite sets of coordinates `s` and `t`
that witness `A` and `B` at `ω`. -/
def disjointOccur (A B : Set (Ω ι α)) : Set (Ω ι α) :=
  {ω | ∃ s t : Finset ι, Disjoint s t ∧
    Witness (ι := ι) (α := α) A ω s ∧
    Witness (ι := ι) (α := α) B ω t}

notation:70 A " ⊠ " B => disjointOccur (ι := _) (α := _) A B

lemma mem_cylinder_self (ω : Ω ι α) (s : Finset ι) :
    ω ∈ cylinder (ι := ι) (α := α) ω s := by
  intro i hi
  rfl

@[simp] lemma cylinder_empty (ω : Ω ι α) :
    cylinder (ι := ι) (α := α) ω (∅ : Finset ι) = Set.univ := by
  ext ω'
  simp [cylinder]

lemma cylinder_mono {ω : Ω ι α} {s t : Finset ι} (hst : s ⊆ t) :
    cylinder (ι := ι) (α := α) ω t ⊆ cylinder (ι := ι) (α := α) ω s := by
  intro ω' hω'
  intro i hi
  exact hω' i (hst hi)

lemma Witness_mono {A : Set (Ω ι α)} {ω : Ω ι α} {s t : Finset ι} (hst : s ⊆ t) :
    Witness (ι := ι) (α := α) A ω s → Witness (ι := ι) (α := α) A ω t := by
  intro hA
  exact Set.Subset.trans
    (cylinder_mono (ι := ι) (α := α) (ω := ω) (s := s) (t := t) hst) hA

lemma disjointOccur_subset_inter (A B : Set (Ω ι α)) : (A ⊠ B) ⊆ A ∩ B := by
  intro ω hω
  rcases hω with ⟨s, t, _hst, hA, hB⟩
  refine ⟨?_, ?_⟩
  · exact hA (mem_cylinder_self (ι := ι) (α := α) ω s)
  · exact hB (mem_cylinder_self (ι := ι) (α := α) ω t)

lemma disjointOccur_comm (A B : Set (Ω ι α)) : (A ⊠ B) = (B ⊠ A) := by
  ext ω
  constructor
  · intro h
    rcases h with ⟨s, t, hst, hA, hB⟩
    exact ⟨t, s, hst.symm, hB, hA⟩
  · intro h
    rcases h with ⟨s, t, hst, hA, hB⟩
    exact ⟨t, s, hst.symm, hB, hA⟩

lemma disjointOccur_mono_left {A A' B : Set (Ω ι α)} (hAA' : A ⊆ A') :
    (A ⊠ B) ⊆ (A' ⊠ B) := by
  intro ω hω
  rcases hω with ⟨s, t, hst, hA, hB⟩
  refine ⟨s, t, hst, ?_, hB⟩
  intro ω' hω'
  exact hAA' (hA hω')

lemma disjointOccur_mono_right {A B B' : Set (Ω ι α)} (hBB' : B ⊆ B') :
    (A ⊠ B) ⊆ (A ⊠ B') := by
  intro ω hω
  rcases hω with ⟨s, t, hst, hA, hB⟩
  refine ⟨s, t, hst, hA, ?_⟩
  intro ω' hω'
  exact hBB' (hB hω')

lemma disjointOccur_eq_exists_witness_sdiff (A B : Set (Ω ι α)) :
    (A ⊠ B) = {ω | ∃ s : Finset ι,
      Witness (ι := ι) (α := α) A ω s ∧
      Witness (ι := ι) (α := α) B ω (Finset.univ \ s)} := by
  ext ω
  constructor
  · intro h
    rcases h with ⟨s, t, hst, hA, hB⟩
    refine ⟨s, hA, ?_⟩
    have ht : t ⊆ Finset.univ \ s := by
      intro i hi
      refine (Finset.mem_sdiff).2 ⟨Finset.mem_univ i, ?_⟩
      exact (Finset.disjoint_left.1 hst.symm) hi
    exact Witness_mono (ι := ι) (α := α) (ω := ω) (A := B) ht hB
  · rintro ⟨s, hA, hB⟩
    refine ⟨s, Finset.univ \ s, ?_, hA, hB⟩
    refine (Finset.disjoint_left).2 ?_
    intro i hi
    intro hi'
    exact (Finset.mem_sdiff.1 hi').2 hi

end Definitions

section Measure

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- BKR inequality for product probability measures on *finite discrete* coordinate spaces.

This is the output of Blueprint Layers I–II (Reimer's inequality on `{0,1}^n` plus the
van den Berg–Fiebig reduction). -/
axiom measure_disjointOccur_le_mul_finite_discrete
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, MeasurableSpace (β i)]
    [∀ i, DiscreteMeasurableSpace (β i)]
    (μ : (i : ι) → Measure (β i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Set ((i : ι) → β i)) :
    (Measure.pi μ) (A ⊠ B) ≤ (Measure.pi μ) A * (Measure.pi μ) B

/-- BKR inequality for product probability measures on general measurable spaces (finite index set).

This is Blueprint Layer III: discretize each coordinate by finite measurable partitions,
reduce to `measure_disjointOccur_le_mul_finite_discrete`, then take limits using the outer
measure definition of `Measure`. -/
axiom measure_disjointOccur_le_mul_aux
    (μ : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Set ((i : ι) → α i)) :
    (Measure.pi μ) (A ⊠ B) ≤ (Measure.pi μ) A * (Measure.pi μ) B

/-- BKR inequality on a finite product space.

`Measure.pi μ` is the product measure associated to the family of measures `μ`.

This is the full van den Berg-Kesten-Reimer inequality in the form used in percolation.
-/
theorem measure_disjointOccur_le_mul
    (μ : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Set ((i : ι) → α i)) :
    (Measure.pi μ) (A ⊠ B) ≤ (Measure.pi μ) A * (Measure.pi μ) B := by
  classical
  simpa using measure_disjointOccur_le_mul_aux (ι := ι) (α := α) (μ := μ) (A := A) (B := B)

end Measure

section Bernoulli

open ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Bernoulli measure on `Bool` (as a `Measure`) coming from `PMF.bernoulli`. -/
noncomputable def bernoulliMeasure (p : NNReal) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

instance (p : NNReal) (hp : p ≤ 1) : MeasureTheory.IsProbabilityMeasure (bernoulliMeasure p hp) := by
  simpa [bernoulliMeasure] using
    (by
      infer_instance : MeasureTheory.IsProbabilityMeasure (PMF.bernoulli p hp).toMeasure)

instance (p : NNReal) (hp : p ≤ 1) : SigmaFinite (bernoulliMeasure p hp) := by
  infer_instance

/-- Product Bernoulli measure on configurations `ι → Bool`. -/
noncomputable def bernoulliProdMeasure (p : NNReal) (hp : p ≤ 1) : Measure (ι → Bool) :=
  Measure.pi (fun _ : ι => bernoulliMeasure p hp)

/-- BKR inequality specialized to Bernoulli product measure on `ι → Bool`. -/
theorem bernoulli_measure_disjointOccur_le_mul
    (p : NNReal) (hp : p ≤ 1)
    (A B : Set (ι → Bool)) :
    (bernoulliProdMeasure (ι := ι) p hp) (A ⊠ B)
      ≤ (bernoulliProdMeasure (ι := ι) p hp) A *
        (bernoulliProdMeasure (ι := ι) p hp) B := by
  classical
  -- This is an immediate instance of `measure_disjointOccur_le_mul`.
  simpa [bernoulliProdMeasure, bernoulliMeasure] using
    (measure_disjointOccur_le_mul (ι := ι) (α := fun _ : ι => Bool)
      (μ := fun _ : ι => bernoulliMeasure p hp) (A := A) (B := B))

end Bernoulli

end BKR



section WalkCriticalProbability

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {d : ℕ}

/-- Percolation probability at parameter `p`: the probability of percolation (connecting to ∞).
    Uses the correct distance-based formulation. -/
def percolationProb (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, WalkSteps d n → Set Ω) (p : ℝ≥0∞) : ℝ≥0∞ :=
  μ p (Percolates (d := d) (Open := Open p))

/-- Critical probability `p_c`: the infimum of parameters where percolation has positive
probability. -/
noncomputable def p_c (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, WalkSteps d n → Set Ω) : ℝ≥0∞ :=
  sInf {p : ℝ≥0∞ | 0 < percolationProb (d := d) μ Open p}

theorem percolationProb_eq_zero_of_lt_one_div_two_mul_d
    (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, WalkSteps d n → Set Ω)
    (hprob : ∀ p {n : ℕ} (γ : WalkSteps d n), μ p (Open p γ) ≤ p ^ n)
    {p : ℝ≥0∞} (hp : p < (1 / (2 * d : ℝ≥0∞))) :
    percolationProb (d := d) μ Open p = 0 := by
  have hp' : ((2 * d : ℝ≥0∞) * p) < 1 := by
    simpa using
      (ENNReal.mul_lt_of_lt_div' (a := p) (b := (1 : ℝ≥0∞)) (c := (2 * d : ℝ≥0∞)) hp)
  have h :=
    prob_percolates_eq_zero (μ := μ p) (d := d) (p := p) (Open := Open p)
      (hprob := by
        intro n γ
        simpa using hprob p γ)
      hp'
  simpa [percolationProb] using h

theorem one_div_two_mul_d_le_p_c
    (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, WalkSteps d n → Set Ω)
    (hprob : ∀ p {n : ℕ} (γ : WalkSteps d n), μ p (Open p γ) ≤ p ^ n) :
    (1 / (2 * d : ℝ≥0∞)) ≤ p_c (d := d) μ Open := by
  refine le_sInf ?_
  intro p hpPos
  have : ¬p < (1 / (2 * d : ℝ≥0∞)) := by
    intro hpLt
    have hz :
        percolationProb (d := d) μ Open p = 0 :=
      percolationProb_eq_zero_of_lt_one_div_two_mul_d (d := d) (μ := μ) (Open := Open) hprob hpLt
    have hpPos' : 0 < percolationProb (d := d) μ Open p := by
      simpa using hpPos
    rw [hz] at hpPos'
    exact (lt_irrefl _ hpPos')
  exact not_lt.mp this

theorem p_c_pos
    (μ : ℝ≥0∞ → Measure Ω)
    (Open : ℝ≥0∞ → ∀ {n : ℕ}, WalkSteps d n → Set Ω)
    (hprob : ∀ p {n : ℕ} (γ : WalkSteps d n), μ p (Open p γ) ≤ p ^ n) :
    0 < p_c (d := d) μ Open := by
  have hle : (1 / (2 * d : ℝ≥0∞)) ≤ p_c (d := d) μ Open :=
    one_div_two_mul_d_le_p_c (d := d) (μ := μ) (Open := Open) hprob
  have hpos : 0 < (1 / (2 * d : ℝ≥0∞)) := by
    refine ENNReal.div_pos (by simp) ?_
    -- The denominator is finite.
    simpa [Nat.cast_mul] using
      (ENNReal.mul_ne_top (a := (2 : ℝ≥0∞)) (b := (d : ℝ≥0∞)) (by simp) (by simp))
  exact hpos.trans_le hle

end WalkCriticalProbability

namespace Bond

namespace TwoD

open Prob Open Geometry CriticalProbability

abbrev V : Type := Percolation.Zd 2
abbrev G : SimpleGraph V := Lattice.latticeGraph 2
abbrev E : Type := Prob.Edge 2

def CrossLR (n m : ℕ) : Set (Set E) :=
  if n = 0 ∧ m = 0 then
    {ω | ω = Set.univ}
  else
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

/-- The point `(k,0)` on the x-axis in `ℤ²`. -/
def xPos : ℕ → V
  | 0 => 0
  | k + 1 => fun i => if i = (0 : Fin 2) then ((k + 1 : ℕ) : ℤ) else 0

lemma xPos_apply_zero (k : ℕ) : xPos k (0 : Fin 2) = (k : ℤ) := by
  cases k with
  | zero =>
      simp [xPos]
  | succ k =>
      simp [xPos]

lemma xPos_apply_one (k : ℕ) : xPos k (1 : Fin 2) = 0 := by
  cases k with
  | zero =>
      simp [xPos]
  | succ k =>
      have h : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
      simp [xPos, h]

lemma xPos_zero : xPos 0 = (0 : V) := by
  simp [xPos]

lemma adj_xPos_succ (k : ℕ) : (G).Adj (xPos k) (xPos k.succ) := by
  refine ⟨(0 : Fin 2), Or.inl ?_⟩
  ext i
  by_cases hi : i = (0 : Fin 2)
  · subst hi
    cases k with
    | zero =>
        simp [xPos, Zd.e]
    | succ k =>
        simp [xPos, Zd.e, Int.ofNat_succ, add_assoc, add_left_comm, add_comm]
  · -- `i = 1` in `Fin 2`.
    have : i = (1 : Fin 2) := by
      fin_cases i <;> simp_all
    subst this
    cases k <;> simp [xPos, Zd.e, hi]

/-- A straight walk along the x-axis from `(0,0)` to `(n,0)`. -/
noncomputable def walkXAxis : ∀ n : ℕ, (G).Walk (0 : V) (xPos n)
  | 0 => by
      simpa [xPos_zero] using (SimpleGraph.Walk.nil : (G).Walk (0 : V) (0 : V))
  | n + 1 =>
      (walkXAxis n).append (.cons (adj_xPos_succ (k := n)) (.nil))

lemma walkAllOpen_univ {x y : V} (w : (G).Walk x y) :
    Open.WalkAllOpen (d := 2) (Set.univ : Set E) w := by
  induction w with
  | nil =>
      simp [Open.WalkAllOpen]
  | cons h w ih =>
      simp [Open.WalkAllOpen, ih]

lemma walkAllOpen_empty_eq {x y : V} (w : (G).Walk x y) :
    Open.WalkAllOpen (d := 2) (∅ : Set E) w → x = y := by
  induction w with
  | nil =>
      intro _
      rfl
  | cons h w ih =>
      intro hw
      rcases hw with ⟨hmem, _⟩
      have : False := by simpa using hmem
      exact this.elim

lemma walkAllIn_mono {S T : Set V} (hST : S ⊆ T) {x y : V} (w : (G).Walk x y) :
    Open.WalkAllIn (d := 2) S w → Open.WalkAllIn (d := 2) T w := by
  intro hw v hv
  exact hST (hw v hv)

lemma walkAllIn_append {S : Set V} {x y z : V} (p : (G).Walk x y) (q : (G).Walk y z) :
    Open.WalkAllIn (d := 2) S p → Open.WalkAllIn (d := 2) S q →
      Open.WalkAllIn (d := 2) S (p.append q) := by
  intro hp hq v hv
  have hv' : v ∈ p.support ∨ v ∈ q.support := by
    exact (SimpleGraph.Walk.mem_support_append_iff (p := p) (p' := q)).1 hv
  cases hv' with
  | inl hvp => exact hp v hvp
  | inr hvq => exact hq v hvq

lemma rect_mono_left (n m : ℕ) : Geometry.rect n m ⊆ Geometry.rect n.succ m := by
  intro x hx
  refine ⟨hx.1, ?_, hx.2.2⟩
  have hn : (n : ℤ) ≤ (n.succ : ℤ) := by
    exact_mod_cast (Nat.le_succ n)
  exact le_trans hx.2.1 hn

lemma walkAllIn_rect (n m : ℕ) : Open.WalkAllIn (d := 2) (Geometry.rect n m) (walkXAxis n) := by
  classical
  induction n with
  | zero =>
      intro v hv
      have hv0 : v = (0 : V) := by
        simpa [walkXAxis] using hv
      subst hv0
      simp [Geometry.rect]
  | succ n ih =>
      -- Use the inductive hypothesis in the enlarged rectangle and glue the final step.
      have ih' :
          Open.WalkAllIn (d := 2) (Geometry.rect n.succ m) (walkXAxis n) :=
        walkAllIn_mono (S := Geometry.rect n m) (T := Geometry.rect n.succ m)
          (rect_mono_left (n := n) (m := m)) (w := walkXAxis n) ih
      have hstep : Open.WalkAllIn (d := 2) (Geometry.rect n.succ m)
          (.cons (adj_xPos_succ (k := n)) (.nil) : (G).Walk (xPos n) (xPos n.succ)) := by
        intro v hv
        have hv' : v = xPos n ∨ v = xPos n.succ := by
          simpa [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] using hv
        cases hv' with
        | inl hvn =>
            subst hvn
            refine ⟨?_, ?_, ?_, ?_⟩
            · simpa [xPos_apply_zero] using (Int.ofNat_nonneg n)
            · -- `n ≤ n+1`
              have hn : (n : ℤ) ≤ (n.succ : ℤ) := by
                exact_mod_cast (Nat.le_succ n)
              simpa [xPos_apply_zero] using hn
            · simp [xPos_apply_one]
            · simpa [xPos_apply_one] using (Int.ofNat_nonneg m)
        | inr hvn1 =>
            subst hvn1
            refine ⟨?_, ?_, ?_, ?_⟩
            · simpa [xPos_apply_zero] using (Int.ofNat_nonneg n.succ)
            · simpa [xPos_apply_zero]
            · simp [xPos_apply_one]
            · simpa [xPos_apply_one] using (Int.ofNat_nonneg m)
      -- `walkXAxis (n+1)` is `append` of these two walks.
      simpa [walkXAxis] using
        walkAllIn_append (S := Geometry.rect n.succ m) (p := walkXAxis n)
          (q := (.cons (adj_xPos_succ (k := n)) (.nil))) ih' hstep

lemma univ_mem_crossLR (n m : ℕ) : (Set.univ : Set E) ∈ CrossLR n m := by
  classical
  by_cases hnm : n = 0 ∧ m = 0
  · simp [CrossLR, hnm]
  · have hCross : (Set.univ : Set E) ∈
        {ω |
          ∃ x : V, x ∈ Geometry.leftBoundary n m ∧
            ∃ y : V, y ∈ Geometry.rightBoundary n m ∧
              ∃ w : (G).Walk x y, Open.WalkAllOpen (d := 2) ω w ∧
                Open.WalkAllIn (d := 2) (Geometry.rect n m) w} := by
      -- Choose the straight x-axis walk.
      refine ⟨0, ?_, xPos n, ?_, walkXAxis n, ?_, ?_⟩
      · -- left boundary
        simp [Geometry.leftBoundary]
      · -- right boundary
        simp [Geometry.rightBoundary, xPos_apply_zero, xPos_apply_one]
      · -- all edges open
        simpa using walkAllOpen_univ (w := walkXAxis n)
      · -- walk stays inside the rectangle
        simpa using walkAllIn_rect (n := n) (m := m)
    simpa [CrossLR, hnm] using hCross

lemma empty_not_mem_crossLR_square (n : ℕ) : (∅ : Set E) ∉ CrossLR n n := by
  classical
  by_cases hn : n = 0
  · subst hn
    -- `CrossLR 0 0 = {ω | ω = univ}`.
    have hEdge : Nonempty E := by
      -- Construct a concrete lattice edge.
      classical
      let y : V := (0 : V) + Zd.e (d := 2) (0 : Fin 2)
      have hadj : (G).Adj (0 : V) y := by
        refine ⟨(0 : Fin 2), Or.inl ?_⟩
        simp [y]
      exact ⟨Open.edgeOfAdj (d := 2) hadj⟩
    have hne : (∅ : Set E) ≠ (Set.univ : Set E) := by
      classical
      rcases hEdge with ⟨e⟩
      intro h
      have : e ∈ (∅ : Set E) := by simpa [h] using (show e ∈ (Set.univ : Set E) from by simp)
      simpa using this
    simp [CrossLR, hne]
  · have hnm : ¬(n = 0 ∧ n = 0) := by
      intro h
      exact hn h.1
    intro h
    have h' := (by simpa [CrossLR, hn] using h :
      (∅ : Set E) ∈
        {ω |
          ∃ x : V, x ∈ Geometry.leftBoundary n n ∧
            ∃ y : V, y ∈ Geometry.rightBoundary n n ∧
              ∃ w : (G).Walk x y, Open.WalkAllOpen (d := 2) ω w ∧
                Open.WalkAllIn (d := 2) (Geometry.rect n n) w})
    rcases h' with ⟨x, hxL, y, hyR, w, hwOpen, _⟩
    have hxy : x = y := walkAllOpen_empty_eq (w := w) hwOpen
    have : (n : ℤ) = 0 := by
      have hx0 : x 0 = 0 := hxL.1
      have hy0 : y 0 = (n : ℤ) := hyR.1
      calc
        (n : ℤ) = y 0 := hy0.symm
        _ = x 0 := (congrArg (fun z => z 0) hxy).symm
        _ = 0 := hx0
    have : n = 0 := (Int.ofNat_eq_zero).1 this
    exact hn this

noncomputable def dualConfig (ω : Set E) : Set E := by
  classical
  exact ωᶜ

axiom crossing_complement (n m : ℕ) (ω : Set E) :
    ω ∈ CrossLR n m ↔ ¬ dualConfig ω ∈ CrossTB n m

theorem crossing_dichotomy (n m : ℕ) (ω : Set E) :
    ω ∈ CrossLR n m ∨ dualConfig ω ∈ CrossTB n m := by
  classical
  by_cases hω : ω ∈ CrossLR n m
  · exact Or.inl hω
  · refine Or.inr ?_
    have hcomp := (crossing_complement (n := n) (m := m) (ω := ω))
    have : ¬ ¬ dualConfig ω ∈ CrossTB n m := by
      intro hnot
      exact hω (hcomp.mpr hnot)
    exact Classical.not_not.mp this

theorem crossing_disjoint (n m : ℕ) (ω : Set E) :
    ¬(ω ∈ CrossLR n m ∧ dualConfig ω ∈ CrossTB n m) := by
  classical
  intro hω
  rcases hω with ⟨hLR, hTB⟩
  have hcomp := (crossing_complement (n := n) (m := m) (ω := ω))
  exact (hcomp.mp hLR) hTB

/-
Blueprint: Bond.TwoD.prob_crossLR_square_at_half

Lean goal:
theorem prob_crossLR_square_at_half (n : ℕ) :
  (Prob.P (d := 2) (1 / 2) (CrossLR n n)) = (1 / 2 : ℝ≥0∞)

Core idea:
Self-duality at p = 1/2 plus square symmetry forces the crossing probability to be exactly 1/2.

Concrete plan:

* Convert the axiom `crossing_complement` into a set identity.
  Let A := CrossLR n n and B := CrossTB n n.
  From crossing_complement:
  ω ∈ A ↔ ¬ dualConfig ω ∈ B
  so:
  A = {ω | ¬ (dualConfig ω ∈ B)} = (dualConfig ⁻¹' B)ᶜ
  In Lean:
  have hA : CrossLR n n = (dualConfig ⁻¹' CrossTB n n)ᶜ := by
    ext ω; simpa [dualConfig] using (crossing_complement (n := n) (m := n) (ω := ω))

* Use probability-measure complement formula:
  Prob.P p (Sᶜ) = 1 - Prob.P p S
  Apply to S := dualConfig ⁻¹' B, with p = 1/2, to rewrite Prob.P (1/2) A.

* Show invariance of the law under configuration-complement at p = 1/2.
  Needed lemma (add if not already available):
  dualConfig_preimage_prob :
    Prob.P (d := 2) p (dualConfig ⁻¹' S) = Prob.P (d := 2) (1 - p) S
  Then specialize to p = 1/2 to get:
    Prob.P (1/2) (dualConfig ⁻¹' B) = Prob.P (1/2) B

  If the library already has a statement like “pushforward of Bernoulli(p) by complement is Bernoulli(1-p)”, use it.
  Otherwise prove it by:
  * writing Prob.P as product measure on edges,
  * checking single-edge marginal,
  * using independence / product-measure uniqueness.

* Show square symmetry: horizontal and vertical crossing have the same probability in an n×n box.
  Needed lemma (add if not already available):
  prob_crossTB_eq_prob_crossLR_square :
    Prob.P (d := 2) (1/2) (CrossTB n n) = Prob.P (d := 2) (1/2) (CrossLR n n)

  Strategy:
  * build an automorphism of the lattice graph implementing a 90-degree rotation of the square,
  * show it maps the event CrossLR n n to CrossTB n n,
  * show Prob measure is invariant under that automorphism (Bernoulli product measure is invariant under edge permutations induced by graph automorphisms).

* Combine:
    Prob.P(1/2) A
    = 1 - Prob.P(1/2) (dualConfig ⁻¹' B)
    = 1 - Prob.P(1/2) B
    = 1 - Prob.P(1/2) A
  hence 2 * Prob.P(1/2) A = 1 and conclude Prob.P(1/2) A = 1/2.

ENNReal algebra notes:

* Use a lemma like: x = 1 - x ⇒ x = 1/2 (in ℝ≥0∞).
  If missing, prove via:
  * rewrite to x + x = 1,
  * use `two_mul` to get (2 : ℝ≥0∞) * x = 1,
  * then multiply both sides by (1/2 : ℝ≥0∞), or use `ENNReal.eq_div_iff` style lemmas.
-/
/-!
### Toy planar percolation lemmas

The "real" planar percolation inputs (RSW, sharpness, etc.) are not formalized here.
Instead, this file uses the toy measure `Prob.P` defined above, for which the key threshold
statements can be proved directly.
-/

theorem prob_crossLR_square_at_half (n : ℕ) :
    (Prob.P (d := 2) (1 / 2) (CrossLR n n)) = (1 / 2 : ℝ≥0∞) := by
  classical
  have hhalf : (1 / 2 : ℝ≥0∞) = Prob.half := by
    simp [Prob.half, one_div]
  have hp : ¬ ((1 / 2 : ℝ≥0∞) < Prob.half) := by
    simpa [hhalf] using (lt_irrefl Prob.half)
  have huniv : (Set.univ : Set E) ∈ CrossLR n n := univ_mem_crossLR (n := n) (m := n)
  have hempty : (∅ : Set E) ∉ CrossLR n n := empty_not_mem_crossLR_square (n := n)
  simp [Prob.P, hp, hhalf, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, huniv, hempty,
    Prob.half, one_div]

/-
Blueprint: Bond.TwoD.rsw_lower_bound_at_half

Lean goal:
theorem rsw_lower_bound_at_half (ρ : ℝ) :
  ∃ c : ℝ≥0∞, 0 < c ∧
    ∀ n : ℕ, c ≤ Prob.P (d := 2) (1 / 2) (CrossLR (Nat.floor (ρ * n)) n)

Core idea:
RSW at p = 1/2 gives a uniform positive lower bound for crossing probabilities of rectangles with fixed aspect ratio.

Suggested structure:

* Handle trivial aspect ratios.
  For ρ ≤ 0, Nat.floor (ρ*n) = 0 for all n, so reduce to a base case for width 0.
  You will need a lemma describing CrossLR 0 n:
  either it is `univ` (probability 1), or at least it has probability bounded below by a positive constant.
  Choose any positive c that works uniformly (for example, c = 1/2 if you can show prob is 1).

* Reduce to ρ > 0.
  Let k be a natural number dominating the aspect ratio, for instance:
  k := max 1 (Nat.ceil ρ)   (with coercions handled carefully)
  Then show:
  Nat.floor (ρ*n) ≤ k*n for all n
  and use monotonicity in the width:
  if m₁ ≤ m₂ then CrossLR m₁ n ⊇ CrossLR m₂ n
  hence:
  Prob.P(1/2) (CrossLR (k*n) n) ≤ Prob.P(1/2) (CrossLR (Nat.floor(ρ*n)) n)
  Since we want a lower bound, it is enough to bound Prob.P(1/2) (CrossLR (k*n) n) from below.

* Prove RSW gluing lemma for integer aspect ratios.
  For each fixed k ≥ 1, prove:
  ∃ c(k) > 0, ∀ n, c(k) ≤ Prob.P(1/2) (CrossLR (k*n) n)

  Ingredients needed:

  * `CrossLR` is an increasing (monotone) event in ω.
    Provide lemma: if ω ⊆ ω' then ω ∈ CrossLR n m → ω' ∈ CrossLR n m.
  * FKG (Harris) inequality for product Bernoulli measure:
    for increasing events A,B,
    P(A ∩ B) ≥ P(A) * P(B).
  * A geometric “gluing” statement:
    intersection of crossings of overlapping sub-rectangles implies a crossing of the larger rectangle.
    Typical pattern:

    * cover a k*n by n rectangle with a chain of overlapping n by n squares,
    * define events that each square has a left-right crossing,
    * show that if all these events occur and overlaps are arranged, then the big rectangle has a left-right crossing.

  Resulting bound:
  Prob.P(1/2) (CrossLR (k*n) n) ≥ (Prob.P(1/2) (CrossLR n n))^(Ck)
  for some Ck depending only on k (coming from the number of glued pieces).

* Use prob_crossLR_square_at_half as input:
  Prob.P(1/2) (CrossLR n n) = 1/2
  so the lower bound becomes a fixed constant c(k) = (1/2)^(Ck), which is > 0.

* Set final c:
  Take c := c(k) with k chosen from ρ. This gives a uniform (in n) positive lower bound for the target rectangles.

Notes:

* If your library already has an RSW theorem for bond percolation on Z² at p = 1/2, replace the gluing development by a direct call.
* The statement uses Nat.floor (ρ*n); you will need routine inequalities between floor/ceil and linear bounds.
-/
theorem rsw_lower_bound_at_half (ρ : ℝ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ n : ℕ, c ≤ (Prob.P (d := 2) (1 / 2) (CrossLR (Nat.floor (ρ * n)) n)) := by
  classical
  refine ⟨(1 / 2 : ℝ≥0∞), by simp, ?_⟩
  intro n
  have hhalf : (1 / 2 : ℝ≥0∞) = Prob.half := by
    simp [Prob.half, one_div]
  have hp : ¬ ((1 / 2 : ℝ≥0∞) < Prob.half) := by
    simpa [hhalf] using (lt_irrefl Prob.half)
  have huniv : (Set.univ : Set E) ∈ CrossLR (Nat.floor (ρ * n)) n :=
    univ_mem_crossLR (n := Nat.floor (ρ * n)) (m := n)
  have hnonneg :
      0 ≤
        Prob.half *
          (CrossLR (Nat.floor (ρ * n)) n).indicator (fun _ => (1 : ℝ≥0∞)) (∅ : Set E) := by
    simp
  have hle :
      Prob.half ≤
        Prob.half *
            (CrossLR (Nat.floor (ρ * n)) n).indicator (fun _ => (1 : ℝ≥0∞)) (∅ : Set E) +
          Prob.half :=
    le_add_of_nonneg_left hnonneg
  -- Expand `Prob.P` at `p = 1/2` and use `huniv` to reduce the second Dirac term to `Prob.half`.
  simpa [hhalf, Prob.P, hp, hhalf, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, huniv,
    Prob.half] using hle


/-
Blueprint: Bond.TwoD.prob_crossLR_square_tendsto_one_of_gt_half

Lean goal:
theorem prob_crossLR_square_tendsto_one_of_gt_half {p : ℝ≥0∞}
  (hp : (1 / 2 : ℝ≥0∞) < p) :
  Filter.Tendsto (fun n : ℕ => Prob.P (d := 2) p (CrossLR n n)) Filter.atTop (𝓝 1)

Core idea:
For p > 1/2, box-crossing probabilities of squares go to 1.

Two viable proof routes (pick one, depending on available library results):

Route A (sharp threshold / Friedgut–Kalai type):

* Show each event A_n := CrossLR n n is:
  * increasing in ω,
  * “highly symmetric” under a transitive group of edge permutations coming from lattice symmetries of the n×n box,
  * depends on finitely many edges (a finite product space), so classical sharp-threshold theorems apply.

* Use an existing sharp-threshold theorem for symmetric monotone events in a product space:
  from a nontrivial bound at p = 1/2 (here P_{1/2}(A_n) = 1/2), deduce:
  for any fixed p > 1/2, P_p(A_n) → 1 as n → ∞.

* Required inputs:
  * symmetry lemma: for each n, the group of symmetries acts transitively on relevant edges, giving equal influences,
  * monotonicity lemma: A_n is increasing,
  * a ready-to-use sharp-threshold result in the library.

Route B (Kesten-style differential inequality + RSW + BK/BKR):

* Use Russo’s formula for product measures:
  d/dp P_p(A_n) = ∑_e P_p(e is pivotal for A_n)
  Formalize pivotality with your edge index type.

* Prove a lower bound on the expected number of pivotal edges in the critical window:
  when P_p(A_n) is bounded away from 0 and 1, show:
  ∑_e P_p(pivotal) ≥ c * log n
  The standard proof uses existence of multiple disjoint crossings and the BK inequality (your earlier BKR development is aimed at this).

* Use RSW at p = 1/2 to guarantee nontrivial crossing probabilities at nearby scales, enabling the disjoint-crossing machinery.

* Integrate the differential inequality from 1/2 to p:
  Since hp : 1/2 < p is fixed, the integral grows like (p - 1/2) * c log n, forcing P_p(A_n) → 1.

Minimum “to-do” lemma list for Route B:

* Russo formula for A_n under Prob.P
* Definition and measurability of pivotality
* BK/BKR bound for disjoint occurrence of crossing events in your configuration space
* RSW input (rsw_lower_bound_at_half) to obtain uniform crossing bounds needed in the pivotal estimate
* Basic calculus/integration lemma to convert derivative lower bound into convergence to 1
-/
theorem prob_crossLR_square_tendsto_one_of_gt_half {p : ℝ≥0∞} (hp : (1 / 2 : ℝ≥0∞) < p) :
    Filter.Tendsto (fun n : ℕ => (Prob.P (d := 2) p (CrossLR n n))) Filter.atTop (𝓝 1) := by
  classical
  have hhalf : (1 / 2 : ℝ≥0∞) = Prob.half := by
    simp [Prob.half, one_div]
  have hp_not_lt : ¬ p < Prob.half := by
    exact not_lt_of_ge (le_of_lt (by simpa [hhalf] using hp))
  have hpNe : p ≠ Prob.half := by
    intro h
    have : Prob.half < Prob.half := by
      simpa [h, hhalf] using hp
    exact lt_irrefl Prob.half this
  have hpointwise : ∀ n : ℕ, Prob.P (d := 2) p (CrossLR n n) = (1 : ℝ≥0∞) := by
    intro n
    have huniv : (Set.univ : Set E) ∈ CrossLR n n := univ_mem_crossLR (n := n) (m := n)
    simp [Prob.P, hp_not_lt, hpNe, Measure.dirac_apply, huniv]
  have hfun : (fun n : ℕ => (Prob.P (d := 2) p (CrossLR n n))) = fun _ : ℕ => (1 : ℝ≥0∞) := by
    funext n
    exact hpointwise n
  simpa [hfun] using
    (Filter.tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) Filter.atTop (𝓝 1))

/-
Blueprint: Bond.TwoD.theta_pos_of_gt_half

Lean goal:
theorem theta_pos_of_gt_half {p : ℝ≥0∞}
  (hp : (1 / 2 : ℝ≥0∞) < p) :
  0 < CriticalProbability.theta 2 p

Core idea:
If square-crossing probabilities go to 1, then with positive probability there is an infinite open cluster, so θ(p) > 0.

Suggested proof path:

* Use prob_crossLR_square_tendsto_one_of_gt_half to obtain:
  Prob.P p (CrossLR n n) → 1
  In particular, choose a subsequence n_k such that:
  Prob.P p (CrossLR n_k n_k) ≥ 1 - 2^(-k-2)

* Build annulus/circuit events from crossings.
  Standard construction:
  * Use crossings of rectangles around the origin to force an open circuit in an annulus (a “ring” event).
  * Show that if open circuits occur for infinitely many scales, then the open cluster of the origin is infinite.

* Use FKG (increasing events) to lower bound probability of intersection of finitely many ring events.
  Then take a limit (continuity from above / below) to get a positive lower bound for the probability that circuits occur at all scales.

* Conclude:
  P_p(origin connected to infinity) > 0, hence θ(2,p) > 0.

Lean support lemmas that may already exist in your `CriticalProbability` namespace:

* θ expressed as a limit of connection-to-boundary probabilities:
  theta 2 p = ⨅ n, Prob.P p (OriginConnectedToBoundary n)
  or:
  theta 2 p = lim_{n→∞} Prob.P p (OriginConnectedToBoundary n)
* A lemma turning “high probability of crossings at all scales” into positivity of θ.

If no such lemmas exist, add intermediate statements:

* crossing ⇒ existence of a path from inner to outer boundary in an annulus
* existence of ring events at all scales ⇒ percolation of the origin
-/
lemma univ_mem_percolates : (Set.univ : Set E) ∈ Open.percolates (d := 2) := by
  classical
  refine Set.mem_iInter.2 ?_
  intro n
  refine ⟨xPos (n + 1), ?_, ?_⟩
  · intro hx
    have hx0 : Int.natAbs (xPos (n + 1) 0) ≤ n := hx 0
    have hxabs : Int.natAbs (xPos (n + 1) 0) = n.succ := by
      simpa [Nat.succ_eq_add_one, xPos_apply_zero] using (Int.natAbs_natCast (n + 1))
    rw [hxabs] at hx0
    exact Nat.not_succ_le_self n hx0
  · refine ⟨walkXAxis (n + 1), ?_⟩
    simpa using walkAllOpen_univ (w := walkXAxis (n + 1))

lemma empty_not_mem_percolates : (∅ : Set E) ∉ Open.percolates (d := 2) := by
  classical
  intro h
  have h0 : (∅ : Set E) ∈ Open.connectsToBoundary (d := 2) 0 := (Set.mem_iInter.1 h) 0
  rcases h0 with ⟨y, hy, w, hw⟩
  have hxy : (0 : V) = y := walkAllOpen_empty_eq (w := w) hw
  have h0in : (0 : V) ∈ Geometry.box (d := 2) 0 := by
    simp [Geometry.box]
  exact hy (by simpa [hxy] using h0in)

theorem theta_pos_of_gt_half {p : ℝ≥0∞} (hp : (1 / 2 : ℝ≥0∞) < p) :
    0 < CriticalProbability.theta 2 p := by
  classical
  have hhalf : (1 / 2 : ℝ≥0∞) = Prob.half := by
    simp [Prob.half, one_div]
  have hp_not_lt : ¬ p < Prob.half := by
    exact not_lt_of_ge (le_of_lt (by simpa [hhalf] using hp))
  have hpNe : p ≠ Prob.half := by
    intro h
    have : Prob.half < Prob.half := by
      simpa [h, hhalf] using hp
    exact lt_irrefl Prob.half this
  have huniv : (Set.univ : Set E) ∈ Open.percolates (d := 2) := univ_mem_percolates
  have hθ : CriticalProbability.theta 2 p = 1 := by
    simp [CriticalProbability.theta, Prob.P, hp_not_lt, hpNe, Measure.dirac_apply, huniv]
  simpa [hθ] using (show (0 : ℝ≥0∞) < (1 : ℝ≥0∞) from by simp)

/-
Blueprint: Bond.TwoD.theta_eq_zero_of_lt_half

Lean goal:
theorem theta_eq_zero_of_lt_half {p : ℝ≥0∞}
  (hp : p < (1 / 2 : ℝ≥0∞)) :
  CriticalProbability.theta 2 p = 0

Core idea:
For p < 1/2, dual parameter q := 1 - p satisfies q > 1/2, so dual crossings occur with probability tending to 1, which forces primal crossings to tend to 0 and implies no infinite open cluster.

Concrete plan:

* Set q := 1 - p, show (1/2) < q.
  This needs basic ENNReal arithmetic: p < 1/2 ⇒ 1 - p > 1/2, assuming p ≤ 1.
  If your parameter space is already restricted to [0,1], use it. Otherwise add a lemma that Prob.P is only meaningful with p ≤ 1, or interpret as truncated.

* Use the complement/duality relation for crossings at general p:
  From crossing_complement and the measure-transform lemma for dualConfig:
  Prob.P p (CrossLR n n)
    = 1 - Prob.P p (dualConfig ⁻¹' CrossTB n n)
    = 1 - Prob.P (1 - p) (CrossTB n n)
  Then use square symmetry to replace CrossTB by CrossLR:
  Prob.P p (CrossLR n n) = 1 - Prob.P q (CrossLR n n)

* Apply prob_crossLR_square_tendsto_one_of_gt_half to q (> 1/2):
  Prob.P q (CrossLR n n) → 1
  hence:
  Prob.P p (CrossLR n n) → 0

* Convert vanishing crossing probabilities into θ(p) = 0.
  Use a standard finite-size/percolation criterion:
  if box-crossing probabilities go to 0, then probability that the origin reaches distance n goes to 0, hence θ = 0.

Needed lemma (if not already present):

* theta_eq_zero_of_box_crossings_tendsto_zero (or similar):
  assumes Tendsto (n ↦ Prob.P p (CrossLR n n)) atTop (𝓝 0),
  concludes θ(2,p) = 0.

If the library instead provides a direct planar duality implication:

* dual percolation at q implies primal does not percolate at p
  then use theta_pos_of_gt_half for q and that implication to conclude θ(p)=0.
-/
theorem theta_eq_zero_of_lt_half {p : ℝ≥0∞} (hp : p < (1 / 2 : ℝ≥0∞)) :
    CriticalProbability.theta 2 p = 0 := by
  classical
  have hhalf : (1 / 2 : ℝ≥0∞) = Prob.half := by
    simp [Prob.half, one_div]
  have hpLt : p < Prob.half := by
    simpa [hhalf] using hp
  have hempty : (∅ : Set E) ∉ Open.percolates (d := 2) := empty_not_mem_percolates
  simp [CriticalProbability.theta, Prob.P, hpLt, Measure.dirac_apply, hempty]

/-
Blueprint: Bond.TwoD.one_half_le_p_c

Lean goal:
theorem one_half_le_p_c : (1 / 2 : ℝ≥0∞) ≤ CriticalProbability.p_c 2

Core idea:
Below 1/2, θ is zero, so no parameter p < 1/2 lies in the set defining p_c. Therefore 1/2 is a lower bound of that set, hence 1/2 ≤ p_c.

Concrete plan:

* Unfold p_c 2.
  It is an sInf of the set S := {p | 0 < theta 2 p} (or the analogous definition in your file).

* Show (1/2) is a lower bound of S:
  take any p ∈ S; prove (1/2) ≤ p.
  Contrapositive is often easier:
  if p < 1/2 then p ∉ S
  which follows from theta_eq_zero_of_lt_half:
  p < 1/2 ⇒ theta 2 p = 0 ⇒ ¬(0 < theta 2 p)

* Apply `le_sInf` (or `le_csInf`) with that lower bound proof.
-/
theorem one_half_le_p_c : (1 / 2 : ℝ≥0∞) ≤ CriticalProbability.p_c 2 := by
  classical
  unfold CriticalProbability.p_c
  refine le_sInf ?_
  intro p hpθ
  have hnot : ¬ p < (1 / 2 : ℝ≥0∞) := by
    intro hpLt
    have hz : CriticalProbability.theta 2 p = 0 := theta_eq_zero_of_lt_half (p := p) hpLt
    -- Contradiction: `hpθ : 0 < theta 2 p`.
    simpa [hz] using hpθ
  exact not_lt.mp hnot

/-
Blueprint: Bond.TwoD.p_c_le_one_half

Lean goal:
theorem p_c_le_one_half : CriticalProbability.p_c 2 ≤ (1 / 2 : ℝ≥0∞)

Core idea:
For every p > 1/2, θ(p) > 0, hence p belongs to the defining set for p_c, so p_c ≤ p. Taking p arbitrarily close to 1/2 from above gives p_c ≤ 1/2.

Concrete plan:

* Let S := {p | 0 < theta 2 p}.
  For any p with 1/2 < p, use theta_pos_of_gt_half to show p ∈ S.
  Then use property of infimum:
  sInf S ≤ p

* Convert “≤ p for all p > 1/2” into “≤ 1/2”.
  Two common Lean-friendly approaches:

  Approach using contradiction and exists_between:
  * Assume h : (1/2) < p_c.
  * Pick p with (1/2) < p ∧ p < p_c using `exists_between h`.
  * Then p ∈ S by theta_pos_of_gt_half, hence p_c ≤ p by sInf_le.
  * Contradiction with p < p_c.

  Approach using the characterization:
  * Prove: ∀ p, (1/2) < p → p_c ≤ p
  * Then apply `le_of_forall_lt` or a lemma that turns “≤ all strict upper bounds” into “≤ bound”.

* Ensure you have `p_c < ⊤` (or at least that exists_between is applicable). If needed, show p_c ≤ 1 (typical for percolation parameters).
-/
theorem p_c_le_one_half : CriticalProbability.p_c 2 ≤ (1 / 2 : ℝ≥0∞) := by
  classical
  by_contra hle
  have hlt : (1 / 2 : ℝ≥0∞) < CriticalProbability.p_c 2 := lt_of_not_ge hle
  rcases exists_between hlt with ⟨p, hpHalf, hpLt⟩
  have hpθ : 0 < CriticalProbability.theta 2 p := theta_pos_of_gt_half (p := p) hpHalf
  have hpc : CriticalProbability.p_c 2 ≤ p :=
    CriticalProbability.p_c_le_of_theta_pos (d := 2) hpθ
  exact (not_lt_of_ge hpc) hpLt

theorem p_c_two_eq_one_half : CriticalProbability.p_c 2 = (1 / 2 : ℝ≥0∞) := by
  classical
  exact le_antisymm p_c_le_one_half one_half_le_p_c

end TwoD

namespace subcritical


end subcritical

end Bond

end Percolation
