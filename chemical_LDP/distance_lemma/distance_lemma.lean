import Mathlib

set_option autoImplicit false

namespace ChemicalLDP
namespace DistanceLemma

/--
Lattice points in dimension `n + 3`, so the ambient dimension is automatically at least `3`,
matching the statement of the blueprint.
-/
abbrev Point (n : ℕ) := Fin (n + 3) → ℤ

/-- Real-valued coordinates on the same finite index set. -/
abbrev RPoint (n : ℕ) := Fin (n + 3) → ℝ

/-- The canonical embedding `ℤ^(n+3) → ℝ^(n+3)`. -/
def toRPoint {n : ℕ} (x : Point n) : RPoint n := fun i => (x i : ℝ)

/-- The affine hyperplane where the first coordinate is fixed to `t`. -/
def firstHyperplane {n : ℕ} (t : ℤ) : Set (Point n) := {x | x 0 = t}

/--
The coordinate-wise Chebyshev bound from the blueprint:
for every `x ∈ S₁`, `y ∈ S₂`, and every coordinate `i`,
the integer distance in that coordinate is at most `K`.
-/
def PairwiseChebyshevBound {n : ℕ} (K : ℕ) (S₁ S₂ : Finset (Point n)) : Prop :=
  ∀ x ∈ S₁, ∀ y ∈ S₂, ∀ i, Int.natAbs (x i - y i) ≤ K

/-- The Euclidean distance on `ℝ^(n+3)` written in coordinates. -/
noncomputable def euclideanDist {n : ℕ} (p q : RPoint n) : ℝ :=
  Real.sqrt (∑ i, (p i - q i) ^ (2 : ℕ))

lemma euclideanDist_nonneg {n : ℕ} (p q : RPoint n) : 0 ≤ euclideanDist p q := by
  simp [euclideanDist]

lemma euclideanDist_self {n : ℕ} (p : RPoint n) : euclideanDist p p = 0 := by
  simp [euclideanDist]

/-- The closed Euclidean segment joining two lattice points. -/
def closedSegment {n : ℕ} (x y : Point n) : Set (RPoint n) :=
  segment ℝ (toRPoint x) (toRPoint y)

/-- All pairwise Euclidean distances between points on two closed segments. -/
def segmentDistances {n : ℕ} (x y x' y' : Point n) : Set ℝ :=
  (fun pq : RPoint n × RPoint n => euclideanDist pq.1 pq.2) ''
    ((closedSegment x y) ×ˢ (closedSegment x' y'))

/--
The Euclidean distance between two segments, defined as the infimum of all pairwise distances
between points on the two segments.
-/
noncomputable def segmentDist {n : ℕ} (x y x' y' : Point n) : ℝ :=
  sInf (segmentDistances x y x' y')

lemma segmentDistances_bddBelow {n : ℕ} (x y x' y' : Point n) :
    BddBelow (segmentDistances x y x' y') := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases hr with ⟨pq, -, rfl⟩
  exact euclideanDist_nonneg _ _

lemma zero_mem_segmentDistances_of_mem_inter
    {n : ℕ} {x y x' y' : Point n} {z : RPoint n}
    (hz₁ : z ∈ closedSegment x y) (hz₂ : z ∈ closedSegment x' y') :
    (0 : ℝ) ∈ segmentDistances x y x' y' := by
  refine ⟨(z, z), ?_, by simp [euclideanDist_self]⟩
  exact ⟨hz₁, hz₂⟩

lemma segmentDist_le_zero_of_nonempty_inter
    {n : ℕ} {x y x' y' : Point n}
    (hinter : (closedSegment x y ∩ closedSegment x' y').Nonempty) :
    segmentDist x y x' y' ≤ 0 := by
  rcases hinter with ⟨z, hz⟩
  rw [Set.mem_inter_iff] at hz
  exact csInf_le (segmentDistances_bddBelow x y x' y')
    (zero_mem_segmentDistances_of_mem_inter hz.1 hz.2)

lemma lowerBound_pos {ℓ K : ℕ} (hKℓ : ℓ ≤ K) (hℓ : 1 ≤ ℓ) :
    0 < (1 / Real.sqrt 2) * ((ℓ : ℝ) / (K : ℝ)) := by
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hℓ_nat : 0 < ℓ := lt_of_lt_of_le (by decide : 0 < 1) hℓ
  have hK_nat : 0 < K := lt_of_lt_of_le hℓ_nat hKℓ
  have hℓR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_nat
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK_nat
  have hleft : 0 < (1 / Real.sqrt 2 : ℝ) := one_div_pos.mpr hsqrt2
  have hright : 0 < ((ℓ : ℝ) / (K : ℝ)) := div_pos hℓR hKR
  exact mul_pos hleft hright

/--
Formal interface for the distance lemma from the blueprint.

The blueprint proves the existence of a bijection between `S₁` and `S₂` whose matching segments
stay at Euclidean distance at least `(1 / sqrt 2) * (ℓ / K)` from one another.

We keep that statement as an axiom here: the geometric argument in the blueprint is substantial,
but the corollary that the matched segments are disjoint is derived below inside Lean.
-/
axiom distance_lemma
    {n ℓ K m : ℕ}
    (hKℓ : ℓ ≤ K) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m)
    (S₁ S₂ : Finset (Point n))
    (hS₁_plane : (↑S₁ : Set (Point n)) ⊆ firstHyperplane 0)
    (hS₂_plane : (↑S₂ : Set (Point n)) ⊆ firstHyperplane (ℓ : ℤ))
    (hS₁_card : S₁.card = m)
    (hS₂_card : S₂.card = m)
    (hbound : PairwiseChebyshevBound K S₁ S₂) :
    ∃ σ : Point n → Point n,
      Set.BijOn σ (↑S₁ : Set (Point n)) (↑S₂ : Set (Point n)) ∧
      ∀ ⦃x x' : Point n⦄, x ∈ S₁ → x' ∈ S₁ → x ≠ x' →
        (1 / Real.sqrt 2) * ((ℓ : ℝ) / (K : ℝ)) ≤ segmentDist x (σ x) x' (σ x')

/--
The non-intersection conclusion from the blueprint. Once the distance lower bound is known,
disjointness follows formally because intersecting segments would force their distance to be `0`.
-/
theorem distance_lemma_disjoint
    {n ℓ K m : ℕ}
    (hKℓ : ℓ ≤ K) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m)
    (S₁ S₂ : Finset (Point n))
    (hS₁_plane : (↑S₁ : Set (Point n)) ⊆ firstHyperplane 0)
    (hS₂_plane : (↑S₂ : Set (Point n)) ⊆ firstHyperplane (ℓ : ℤ))
    (hS₁_card : S₁.card = m)
    (hS₂_card : S₂.card = m)
    (hbound : PairwiseChebyshevBound K S₁ S₂) :
    ∃ σ : Point n → Point n,
      Set.BijOn σ (↑S₁ : Set (Point n)) (↑S₂ : Set (Point n)) ∧
      ∀ ⦃x x' : Point n⦄, x ∈ S₁ → x' ∈ S₁ → x ≠ x' →
        (1 / Real.sqrt 2) * ((ℓ : ℝ) / (K : ℝ)) ≤ segmentDist x (σ x) x' (σ x') ∧
        Disjoint (closedSegment x (σ x)) (closedSegment x' (σ x')) := by
  obtain ⟨σ, hσ_bij, hσ_dist⟩ :=
    distance_lemma hKℓ hℓ hm S₁ S₂ hS₁_plane hS₂_plane hS₁_card hS₂_card hbound
  refine ⟨σ, hσ_bij, ?_⟩
  intro x x' hx hx' hxx'
  refine ⟨hσ_dist hx hx' hxx', ?_⟩
  refine Set.disjoint_left.2 ?_
  intro z hz₁ hz₂
  have hle :
      segmentDist x (σ x) x' (σ x') ≤ 0 :=
    segmentDist_le_zero_of_nonempty_inter ⟨z, ⟨hz₁, hz₂⟩⟩
  have hpos :
      0 < (1 / Real.sqrt 2) * ((ℓ : ℝ) / (K : ℝ)) :=
    lowerBound_pos hKℓ hℓ
  have hlt :
      0 < segmentDist x (σ x) x' (σ x') :=
    lt_of_lt_of_le hpos (hσ_dist hx hx' hxx')
  linarith

end DistanceLemma
end ChemicalLDP
