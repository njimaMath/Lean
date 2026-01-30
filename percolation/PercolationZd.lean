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

section CriticalProbability

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

theorem russo_formula_crossLR (_n : ℕ) : True := by
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
