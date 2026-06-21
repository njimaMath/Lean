import Mathlib

open scoped BigOperators

namespace DisjointPaths

-- ============================================================
-- Section 1: Lattice primitives
-- ============================================================

-- Shell geometry on `ℤ^d`.
abbrev Zd (d : Nat) := Fin d -> Int

namespace Zd

variable {d : Nat}

def e (i : Fin d) : Zd d := fun j => if j = i then 1 else 0

@[simp] lemma e_apply_self (i : Fin d) : e (d := d) i i = 1 := by
  simp [e]

@[simp] lemma e_apply_ne {i j : Fin d} (h : j ≠ i) : e (d := d) i j = 0 := by
  simp [e, h]

def l1Norm (x : Zd d) : Nat :=
  ∑ i, Int.natAbs (x i)

def sphere (n : Nat) : Set (Zd d) :=
  {x | l1Norm x = n}

def nonzeroCoords (x : Zd d) : Finset (Fin d) :=
  Finset.univ.filter fun i => x i ≠ 0

@[simp] lemma mem_nonzeroCoords {x : Zd d} {i : Fin d} :
    i ∈ nonzeroCoords x ↔ x i ≠ 0 := by
  simp [nonzeroCoords]

end Zd

variable {d : Nat}

-- Nearest-neighbor adjacency in the lattice.
def Adj (x y : Zd d) : Prop :=
  ∃ i : Fin d, y = x + Zd.e i ∨ y = x - Zd.e i

lemma adj_symm {x y : Zd d} : Adj x y → Adj y x := by
  rintro ⟨i, rfl | rfl⟩
  · refine ⟨i, Or.inr ?_⟩
    ext j
    by_cases h : j = i
    · subst h
      simp [Zd.e]
    · simp [Zd.e, h]
  · refine ⟨i, Or.inl ?_⟩
    ext j
    by_cases h : j = i
    · subst h
      simp [Zd.e]
    · simp [Zd.e, h]

lemma adj_irrefl (x : Zd d) : ¬ Adj x x := by
  intro h
  rcases h with ⟨i, h | h⟩
  · have hi := congrFun h i
    simp [Zd.e] at hi
  · have hi := congrFun h i
    simp [Zd.e] at hi
    linarith

def latticeGraph (d : Nat) : SimpleGraph (Zd d) where
  Adj := Adj
  symm := by
    intro x y h
    exact adj_symm h
  loopless := ⟨adj_irrefl⟩

-- ============================================================
-- Section 2: Path objects and configuration predicates
-- ============================================================

-- Fixed-length lattice paths.
structure FinitePath (d n : Nat) where
  toVertex : Fin (n + 1) → Zd d
  adjacent' : ∀ i : Fin n, Adj (toVertex i.castSucc) (toVertex i.succ)

namespace FinitePath

variable {n : Nat}

instance : CoeFun (FinitePath d n) (fun _ => Fin (n + 1) → Zd d) := ⟨FinitePath.toVertex⟩

@[simp] lemma adjacent (gamma : FinitePath d n) (i : Fin n) :
    Adj (gamma i.castSucc) (gamma i.succ) :=
  gamma.adjacent' i

def start (gamma : FinitePath d n) : Zd d := gamma 0

def finish (gamma : FinitePath d n) : Zd d := gamma ⟨n, Nat.lt_succ_self n⟩

@[simp] lemma start_def (gamma : FinitePath d n) : gamma.start = gamma 0 := rfl

@[simp] lemma finish_def (gamma : FinitePath d n) :
    gamma.finish = gamma ⟨n, Nat.lt_succ_self n⟩ := rfl

def length (_gamma : FinitePath d n) : Nat := n

@[simp] lemma length_eq (gamma : FinitePath d n) : gamma.length = n := rfl

def vertexSet (gamma : FinitePath d n) : Set (Zd d) :=
  Set.range gamma

def staysIn (s : Set (Zd d)) (gamma : FinitePath d n) : Prop :=
  ∀ i, gamma i ∈ s

def IsSelfAvoiding (gamma : FinitePath d n) : Prop :=
  Function.Injective gamma

def nil (x : Zd d) : FinitePath d 0 where
  toVertex _ := x
  adjacent' := by
    intro i
    exact Fin.elim0 i

@[simp] lemma nil_start (x : Zd d) : (nil (d := d) x).start = x := rfl

@[simp] lemma nil_finish (x : Zd d) : (nil (d := d) x).finish = x := rfl

end FinitePath

-- Variable-length path specifications.
structure PathSpec (d : Nat) where
  len : Nat
  path : FinitePath d len

namespace PathSpec

def start (gamma : PathSpec d) : Zd d :=
  gamma.path.start

def finish (gamma : PathSpec d) : Zd d :=
  gamma.path.finish

def vertexAt (gamma : PathSpec d) (k : Nat) (hk : k <= gamma.len) : Zd d :=
  gamma.path ⟨k, Nat.lt_succ_of_le hk⟩

def vertexSet (gamma : PathSpec d) : Set (Zd d) :=
  gamma.path.vertexSet

def staysIn (s : Set (Zd d)) (gamma : PathSpec d) : Prop :=
  gamma.path.staysIn s

def edgeSet (gamma : PathSpec d) : Set (Zd d × Zd d) :=
  {e | ∃ i : Fin gamma.len,
      e = (gamma.path i.castSucc, gamma.path i.succ) ∨
        e = (gamma.path i.succ, gamma.path i.castSucc)}

def EdgeDisjoint (gamma gamma' : PathSpec d) : Prop :=
  Disjoint gamma.edgeSet gamma'.edgeSet

def EndpointFarFrom (r : ℝ) (gamma gamma' : PathSpec d) : Prop :=
  ∀ z ∈ gamma'.vertexSet, r ≤ dist gamma.finish z

end PathSpec

-- Configuration predicates and counting targets used in the blueprint.
def axisPoint (m : Int) (i : Fin d) : Zd d :=
  fun j => if j = i then m else 0

def IsAxisPoint (m : Int) (x : Zd d) : Prop :=
  ∃ i : Fin d, x = axisPoint (d := d) m i

def IsSignedAxisPoint (m : Nat) (x : Zd d) : Prop :=
  IsAxisPoint (d := d) (m : Int) x ∨ IsAxisPoint (d := d) (-(m : Int)) x

@[simp] lemma neg_axisPoint (m : Int) (i : Fin d) :
    -axisPoint (d := d) m i = axisPoint (d := d) (-m) i := by
  ext j
  by_cases h : j = i
  · subst h
    simp [axisPoint]
  · simp [axisPoint, h]

@[simp] lemma isSignedAxisPoint_neg_iff {m : Nat} {x : Zd d} :
    IsSignedAxisPoint (d := d) m (-x) ↔ IsSignedAxisPoint (d := d) m x := by
  constructor <;> intro h
  · rcases h with h | h
    · rcases h with ⟨i, hi⟩
      right
      refine ⟨i, ?_⟩
      simpa using congrArg Neg.neg hi
    · rcases h with ⟨i, hi⟩
      left
      refine ⟨i, ?_⟩
      simpa using congrArg Neg.neg hi
  · rcases h with h | h
    · rcases h with ⟨i, hi⟩
      right
      refine ⟨i, ?_⟩
      simpa using congrArg Neg.neg hi
    · rcases h with ⟨i, hi⟩
      left
      refine ⟨i, ?_⟩
      simpa using congrArg Neg.neg hi

def Nonnegative (x : Zd d) : Prop :=
  ∀ i, 0 ≤ x i

def DifferentOrthants (x y : Zd d) : Prop :=
  ∃ i, x i * y i < 0

def positiveCoords (x : Zd d) : Finset (Fin d) :=
  Finset.univ.filter fun i => 0 < x i

@[simp] lemma mem_positiveCoords {x : Zd d} {i : Fin d} :
    i ∈ positiveCoords x ↔ 0 < x i := by
  simp [positiveCoords]

noncomputable def requiredInnerPathCount (n : Nat) (x : Zd d) : Nat := by
  classical
  exact if IsSignedAxisPoint (d := d) n x then
    2 * d - 3
  else
    2 * d - (Zd.nonzeroCoords x).card - 1

noncomputable def requiredOuterPathCount (n : Nat) (x : Zd d) : Nat := by
  classical
  exact if IsSignedAxisPoint (d := d) (n + 1) x then
    1
  else
    (Zd.nonzeroCoords x).card - 1

@[simp] lemma requiredInnerPathCount_neg (n : Nat) (x : Zd d) :
    requiredInnerPathCount (d := d) n (-x) = requiredInnerPathCount (d := d) n x := by
  classical
  have hnonzero : Zd.nonzeroCoords (-x) = Zd.nonzeroCoords x := by
    ext i
    simp [Zd.nonzeroCoords]
  by_cases haxis : IsSignedAxisPoint (d := d) n x
  · simp [requiredInnerPathCount, haxis]
  · simp [requiredInnerPathCount, haxis]
    rw [hnonzero]

@[simp] lemma requiredOuterPathCount_neg (n : Nat) (x : Zd d) :
    requiredOuterPathCount (d := d) n (-x) = requiredOuterPathCount (d := d) n x := by
  classical
  have hnonzero : Zd.nonzeroCoords (-x) = Zd.nonzeroCoords x := by
    ext i
    simp [Zd.nonzeroCoords]
  by_cases haxis : IsSignedAxisPoint (d := d) (n + 1) x
  · simp [requiredOuterPathCount, haxis]
  · simp [requiredOuterPathCount, haxis]
    rw [hnonzero]

/-- The two shells that the blueprint paths are allowed to visit. -/
def shellUnion (n : Nat) : Set (Zd d) :=
  Zd.sphere n ∪ Zd.sphere (n + 1)

def endpointSeparationRadius (δ : ℝ) (n : Nat) : ℝ :=
  δ ^ 3 * (n + 1 : ℝ)

/--
Large-`n` hypothesis used repeatedly in the blueprint to guarantee that a
maximal coordinate on `Zd.sphere n` dominates the path scale `δ ^ 2 * (n + 1)`.

Note: the original definition only required
`4 * δ ^ 2 * (n + 1 : ℝ) < (n : ℝ) / (d : ℝ)`. This was insufficient: for
small positive `δ` with small `n` (e.g. `d = 3, n = 1, δ = 1/100`),
`SufficientlyLargeN` was satisfied but the path-length upper bound
`⌊2d · δ² · (n+1)⌋ = 0` forced all paths to have length 0, making the
pairwise endpoint-separation condition `δ³(n+1) ≤ dist(finish, z)` impossible
to satisfy when ≥ 2 paths share the same starting point.

The second conjunct `0 < δ → 2 ≤ ⌊δ²(n+1)⌋` fixes this by ensuring spreading
paths have length ≥ 2 whenever the separation radius is positive.
-/
def SufficientlyLargeN (n : Nat) (δ : ℝ) : Prop :=
  4 * δ ^ 2 * (n + 1 : ℝ) < (n : ℝ) / (d : ℝ) ∧
  (0 < δ → 2 ≤ Nat.floor (δ ^ 2 * (n + 1 : ℝ)))

structure PathBundle (d n : Nat) (δ : ℝ) (x : Zd d) where
  paths : List (PathSpec d)
  starts_at : ∀ gamma ∈ paths, gamma.start = x
  length_lower :
    ∀ gamma ∈ paths, Nat.floor (δ ^ 2 * (n + 1 : ℝ)) ≤ gamma.len
  length_upper :
    ∀ gamma ∈ paths, gamma.len ≤ Nat.floor (((2 * d : Nat) : ℝ) * δ ^ 2 * (n + 1 : ℝ))
  stays_on_shells :
    ∀ gamma ∈ paths, gamma.staysIn (shellUnion (d := d) n)
  pairwise_edge_disjoint :
    paths.Pairwise PathSpec.EdgeDisjoint

/--
`DisjointPathConfiguration d n δ xn xnp1` packages the full family promised by
the blueprint: an inner bundle starting at `xn`, an outer bundle starting at
`xnp1`, the prescribed path counts, and the required edge- and
endpoint-separation properties.
-/
structure DisjointPathConfiguration (d n : Nat) (δ : ℝ) (xn xnp1 : Zd d) where
  inner : PathBundle d n δ xn
  outer : PathBundle d n δ xnp1
  inner_count :
    inner.paths.length = requiredInnerPathCount (d := d) n xn
  outer_count :
    outer.paths.length = requiredOuterPathCount (d := d) n xnp1
  cross_edge_disjoint :
    ∀ gamma ∈ inner.paths, ∀ gamma' ∈ outer.paths, PathSpec.EdgeDisjoint gamma gamma'
  inner_endpoint_separated :
    inner.paths.Pairwise fun gamma gamma' =>
      PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
        PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma
  outer_endpoint_separated :
    outer.paths.Pairwise fun gamma gamma' =>
      PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
        PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma
  cross_endpoint_separated :
    ∀ gamma ∈ inner.paths, ∀ gamma' ∈ outer.paths,
      PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
        PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma

/-- Formal statement of the main existence claim in `blueprint_disjoint.txt`. -/
def HasDesiredDisjointPaths (n : Nat) (δ : ℝ) (xn xnp1 : Zd d) : Prop :=
  Nonempty (DisjointPathConfiguration d n δ xn xnp1)

namespace Zd

@[simp] lemma l1Norm_neg (x : Zd d) : l1Norm (-x) = l1Norm x := by
  simp [l1Norm]

@[simp] lemma nonzeroCoords_neg (x : Zd d) : nonzeroCoords (-x) = nonzeroCoords x := by
  ext i
  simp [nonzeroCoords]

@[simp] lemma mem_sphere_neg {n : Nat} {x : Zd d} :
    -x ∈ sphere (d := d) n ↔ x ∈ sphere (d := d) n := by
  simp [sphere]

end Zd

namespace FinitePath

variable {n : Nat}

/-- Reflect a finite lattice path through the origin. -/
def neg (gamma : FinitePath d n) : FinitePath d n where
  toVertex i := -gamma i
  adjacent' i := by
    rcases gamma.adjacent i with ⟨j, h | h⟩
    · refine ⟨j, Or.inr ?_⟩
      rw [h]
      ext k
      change -(gamma.toVertex i.castSucc k + Zd.e j k) =
        -gamma.toVertex i.castSucc k - Zd.e j k
      ring
    · refine ⟨j, Or.inl ?_⟩
      rw [h]
      ext k
      change -(gamma.toVertex i.castSucc k - Zd.e j k) =
        -gamma.toVertex i.castSucc k + Zd.e j k
      ring

@[simp] lemma neg_apply (gamma : FinitePath d n) (i : Fin (n + 1)) :
    gamma.neg i = -gamma i := rfl

end FinitePath

namespace PathSpec

/-- Reflect a path specification through the origin. -/
def neg (gamma : PathSpec d) : PathSpec d where
  len := gamma.len
  path := gamma.path.neg

@[simp] lemma neg_len (gamma : PathSpec d) : gamma.neg.len = gamma.len := rfl

@[simp] lemma neg_start (gamma : PathSpec d) : gamma.neg.start = -gamma.start := rfl

@[simp] lemma neg_finish (gamma : PathSpec d) : gamma.neg.finish = -gamma.finish := rfl

lemma mem_vertexSet_neg {gamma : PathSpec d} {z : Zd d} :
    z ∈ gamma.neg.vertexSet ↔ -z ∈ gamma.vertexSet := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [PathSpec.neg, FinitePath.neg]⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hneg := congrArg Neg.neg hi
    simpa [PathSpec.neg, FinitePath.neg] using hneg

lemma mem_edgeSet_neg {gamma : PathSpec d} {e : Zd d × Zd d} :
    e ∈ gamma.neg.edgeSet ↔ (-e.1, -e.2) ∈ gamma.edgeSet := by
  constructor
  · rintro ⟨i, h | h⟩
    · refine ⟨i, Or.inl ?_⟩
      have hneg := congrArg (fun p : Zd d × Zd d => (-p.1, -p.2)) h
      simpa [PathSpec.edgeSet, PathSpec.neg, FinitePath.neg] using hneg
    · refine ⟨i, Or.inr ?_⟩
      have hneg := congrArg (fun p : Zd d × Zd d => (-p.1, -p.2)) h
      simpa [PathSpec.edgeSet, PathSpec.neg, FinitePath.neg] using hneg
  · rintro ⟨i, h | h⟩
    · refine ⟨i, Or.inl ?_⟩
      have hneg := congrArg (fun p : Zd d × Zd d => (-p.1, -p.2)) h
      simpa [PathSpec.edgeSet, PathSpec.neg, FinitePath.neg] using hneg
    · refine ⟨i, Or.inr ?_⟩
      have hneg := congrArg (fun p : Zd d × Zd d => (-p.1, -p.2)) h
      simpa [PathSpec.edgeSet, PathSpec.neg, FinitePath.neg] using hneg

lemma edgeDisjoint_neg_iff {gamma gamma' : PathSpec d} :
    PathSpec.EdgeDisjoint gamma.neg gamma'.neg ↔ PathSpec.EdgeDisjoint gamma gamma' := by
  constructor
  · intro h
    refine Set.disjoint_left.2 ?_
    intro e he he'
    have hdisj := Set.disjoint_left.1 h
    have he_neg : (-e.1, -e.2) ∈ gamma.neg.edgeSet := by
      apply (mem_edgeSet_neg (gamma := gamma) (e := (-e.1, -e.2))).2
      simpa
    have he'_neg : (-e.1, -e.2) ∈ gamma'.neg.edgeSet := by
      apply (mem_edgeSet_neg (gamma := gamma') (e := (-e.1, -e.2))).2
      simpa
    exact hdisj he_neg he'_neg
  · intro h
    refine Set.disjoint_left.2 ?_
    intro e he he'
    have hdisj := Set.disjoint_left.1 h
    have he_orig : (-e.1, -e.2) ∈ gamma.edgeSet :=
      (mem_edgeSet_neg (gamma := gamma) (e := e)).1 he
    have he'_orig : (-e.1, -e.2) ∈ gamma'.edgeSet :=
      (mem_edgeSet_neg (gamma := gamma') (e := e)).1 he'
    exact hdisj he_orig he'_orig

lemma endpointFarFrom_neg_iff {r : ℝ} {gamma gamma' : PathSpec d} :
    PathSpec.EndpointFarFrom r gamma.neg gamma'.neg ↔
      PathSpec.EndpointFarFrom r gamma gamma' := by
  constructor
  · intro h z hz
    have hzneg : -z ∈ gamma'.neg.vertexSet := by
      have hz' : -(-z) ∈ gamma'.vertexSet := by simpa
      exact (mem_vertexSet_neg (gamma := gamma') (z := -z)).2 hz'
    have hdist := h (-z) hzneg
    exact (dist_neg_neg gamma.finish z) ▸ hdist
  · intro h z hz
    have hzneg : -z ∈ gamma'.vertexSet := (mem_vertexSet_neg (gamma := gamma')).1 hz
    have hdist := h (-z) hzneg
    have hrewrite : dist gamma.finish (-z) = dist (-gamma.finish) z := by
      simpa using (dist_neg_neg gamma.finish (-z)).symm
    exact hrewrite ▸ hdist

lemma staysIn_shellUnion_neg_iff {n : Nat} {gamma : PathSpec d} :
    gamma.neg.staysIn (shellUnion (d := d) n) ↔
      gamma.staysIn (shellUnion (d := d) n) := by
  constructor <;> intro h i <;>
    simpa [PathSpec.staysIn, PathSpec.neg, FinitePath.neg, shellUnion, Zd.sphere]
      using h i

end PathSpec

namespace PathBundle

/-- Reflect an entire path bundle through the origin. -/
def neg {n : Nat} {δ : ℝ} {x : Zd d} (bundle : PathBundle d n δ x) :
    PathBundle d n δ (-x) where
  paths := bundle.paths.map PathSpec.neg
  starts_at := by
    intro gamma hgamma
    rcases List.mem_map.1 hgamma with ⟨gamma0, hgamma0, rfl⟩
    change -gamma0.start = -x
    exact congrArg Neg.neg (bundle.starts_at gamma0 hgamma0)
  length_lower := by
    intro gamma hgamma
    rcases List.mem_map.1 hgamma with ⟨gamma0, hgamma0, rfl⟩
    simpa [PathSpec.neg] using bundle.length_lower gamma0 hgamma0
  length_upper := by
    intro gamma hgamma
    rcases List.mem_map.1 hgamma with ⟨gamma0, hgamma0, rfl⟩
    simpa [PathSpec.neg] using bundle.length_upper gamma0 hgamma0
  stays_on_shells := by
    intro gamma hgamma
    rcases List.mem_map.1 hgamma with ⟨gamma0, hgamma0, rfl⟩
    exact (PathSpec.staysIn_shellUnion_neg_iff (d := d) (n := n) (gamma := gamma0)).2
      (bundle.stays_on_shells gamma0 hgamma0)
  pairwise_edge_disjoint := by
    exact List.Pairwise.map PathSpec.neg
      (fun gamma gamma' h =>
        (PathSpec.edgeDisjoint_neg_iff (gamma := gamma) (gamma' := gamma')).2 h)
      bundle.pairwise_edge_disjoint

end PathBundle

namespace DisjointPathConfiguration

/-- Reflect a full disjoint-path configuration through the origin. -/
def neg {n : Nat} {δ : ℝ} {xn xnp1 : Zd d}
    (cfg : DisjointPathConfiguration d n δ xn xnp1) :
    DisjointPathConfiguration d n δ (-xn) (-xnp1) where
  inner := cfg.inner.neg
  outer := cfg.outer.neg
  inner_count := by
    simpa [PathBundle.neg] using cfg.inner_count
  outer_count := by
    simpa [PathBundle.neg] using cfg.outer_count
  cross_edge_disjoint := by
    intro gamma hgamma gamma' hgamma'
    rcases List.mem_map.1 hgamma with ⟨gamma0, hgamma0, rfl⟩
    rcases List.mem_map.1 hgamma' with ⟨gamma1, hgamma1, rfl⟩
    exact (PathSpec.edgeDisjoint_neg_iff (gamma := gamma0) (gamma' := gamma1)).2
      (cfg.cross_edge_disjoint gamma0 hgamma0 gamma1 hgamma1)
  inner_endpoint_separated := by
    exact List.Pairwise.map PathSpec.neg
      (fun gamma gamma' h => by
        rcases h with ⟨hleft, hright⟩
        exact ⟨(PathSpec.endpointFarFrom_neg_iff (gamma := gamma) (gamma' := gamma')).2 hleft,
          (PathSpec.endpointFarFrom_neg_iff (gamma := gamma') (gamma' := gamma)).2 hright⟩)
      cfg.inner_endpoint_separated
  outer_endpoint_separated := by
    exact List.Pairwise.map PathSpec.neg
      (fun gamma gamma' h => by
        rcases h with ⟨hleft, hright⟩
        exact ⟨(PathSpec.endpointFarFrom_neg_iff (gamma := gamma) (gamma' := gamma')).2 hleft,
          (PathSpec.endpointFarFrom_neg_iff (gamma := gamma') (gamma' := gamma)).2 hright⟩)
      cfg.outer_endpoint_separated
  cross_endpoint_separated := by
    intro gamma hgamma gamma' hgamma'
    rcases List.mem_map.1 hgamma with ⟨gamma0, hgamma0, rfl⟩
    rcases List.mem_map.1 hgamma' with ⟨gamma1, hgamma1, rfl⟩
    rcases cfg.cross_endpoint_separated gamma0 hgamma0 gamma1 hgamma1 with ⟨hleft, hright⟩
    exact ⟨(PathSpec.endpointFarFrom_neg_iff (gamma := gamma0) (gamma' := gamma1)).2 hleft,
      (PathSpec.endpointFarFrom_neg_iff (gamma := gamma1) (gamma' := gamma0)).2 hright⟩

end DisjointPathConfiguration

lemma hasDesiredDisjointPaths_neg
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 →
      HasDesiredDisjointPaths (d := d) n δ (-xn) (-xnp1) := by
  rintro ⟨cfg⟩
  exact ⟨cfg.neg⟩

-- ============================================================
-- Section 3: Blueprint overview and separation lemma
-- ============================================================

/-
Blueprint overview.

Assume `d >= 3`. The blueprint aims to show that for `xn ∈ Zd.sphere n`,
`xnp1 ∈ Zd.sphere (n + 1)`, and `δ <= 1 / (8d)`, one can build:

* `2 * d - |{i | xn i ≠ 0}| - 1` paths from `xn` when `xn` is not a signed axis
  point,
* `2 * d - 3` paths from `xn` when `xn = ± n e_i`,
* `|{j | xnp1 j ≠ 0}| - 1` paths from `xnp1` when `xnp1` is not a signed axis
  point on the outer shell,
* one path from `xnp1` when `xnp1 = ± (n + 1) e_j`,

such that the whole family is edge-disjoint, stays inside
`Zd.sphere n ∪ Zd.sphere (n + 1)`, has length between
`floor (δ^2 * (n + 1))` and `floor (2 * d * δ^2 * (n + 1))`, and has endpoints
at distance at least `δ^3 * (n + 1)` from the union of all the other paths.

The blueprint also uses, for all sufficiently large `n`, the observation that
`xn` has a coordinate larger than `n / d > 4 * δ^2 * (n + 1)`. We package this
large-`n` input below as `SufficientlyLargeN n δ`.

The roadmap is:

1. Reduce to convenient normal forms by permuting coordinates and reflecting
   signs, since only the relative position of `xn` and `xnp1` matters.
2. Build each family so different paths move away in different coordinate
   directions, which gives edge-disjointness and the required path counts.
3. Separate the endpoints by choosing a comparison coordinate whose gap grows
   along the two paths.
-/

/--
After the first `floor (δ^3 (n+1))` steps, the `i`-th coordinate gap grows by
at least one every `2 * d` steps.
-/
def TailCoordinateDifferenceGrows (δ : ℝ) (n : Nat) (i : Fin d)
    (gamma gamma' : PathSpec d) : Prop :=
  ∀ t : Nat,
    Nat.floor (δ ^ 3 * (n + 1 : ℝ)) ≤ t →
    t + 2 * d ≤ Nat.min gamma.len gamma'.len →
      ∃ hgamma_t : t ≤ gamma.len,
        ∃ hgamma'_t : t ≤ gamma'.len,
          ∃ hgamma_step : t + 2 * d ≤ gamma.len,
            ∃ hgamma'_step : t + 2 * d ≤ gamma'.len,
              Int.natAbs
                  ((gamma.vertexAt (t + 2 * d) hgamma_step i) -
                    (gamma'.vertexAt (t + 2 * d) hgamma'_step i)) ≥
                Int.natAbs
                    ((gamma.vertexAt t hgamma_t i) -
                      (gamma'.vertexAt t hgamma'_t i)) + 1

/--
Auxiliary endpoint condition carried by the current skeleton: the endpoint of
`gamma` is already separated from every point of `gamma'` in the `i`-th
coordinate.
-/
def EndpointCoordinateGap (δ : ℝ) (n : Nat) (i : Fin d)
    (gamma gamma' : PathSpec d) : Prop :=
  ∀ z ∈ gamma'.vertexSet,
    endpointSeparationRadius δ n ≤ |gamma.finish i - z i|

/--
Placeholder bundle of separation data abstracted from the blueprint. The final
formal argument should derive `EndpointCoordinateGap` from
`TailCoordinateDifferenceGrows`; for now we keep both ingredients explicit so
the later case stubs can state exactly what they use.
-/
def CoordinateDifferenceGrows (δ : ℝ) (n : Nat) (i : Fin d)
    (gamma gamma' : PathSpec d) : Prop :=
  TailCoordinateDifferenceGrows (d := d) δ n i gamma gamma' ∧
    EndpointCoordinateGap (d := d) δ n i gamma gamma'

/-
Suppose `gamma` and `gamma'` both have length at least `δ^2 * (n + 1)`, and
there is some coordinate `i` such that after the first
`floor (δ^3 * (n + 1))` steps, the difference of the `i`-th coordinates grows
by at least one every `2 * d` steps. Then the endpoint of `gamma` is at
distance at least `δ^3 * (n + 1)` from the whole path `gamma'`. If the same
monotonic-growth condition also holds after swapping the roles of `gamma` and
`gamma'` (possibly using a different coordinate), then the endpoint of
`gamma'` is likewise at distance at least `δ^3 * (n + 1)` from the whole path
`gamma`.

Blueprint proof sketch: from the growth assumption, the endpoint of `gamma` is
separated from the tail of `gamma'` by at least
`(δ^2 - δ^3) * (n + 1) / (2 * d)` in the chosen coordinate, which is at least
`2 * δ^3 * (n + 1)` under the smallness bound on `δ`. The initial segment of
`gamma'` of length `floor (δ^3 * (n + 1))` lies inside the
`δ^3 * (n + 1)`-neighborhood of the remaining tail, so the same lower bound
still leaves the endpoint of `gamma` at distance at least `δ^3 * (n + 1)` from
all of `gamma'`. The second conclusion is the same argument with the two paths
interchanged.
-/
/-- Blueprint separation lemma extracted from the coordinate-gap condition. -/
lemma path_separation
    {n : Nat} {δ : ℝ} {gamma gamma' : PathSpec d}
    (_hgamma : Nat.floor (δ ^ 2 * (n + 1 : ℝ)) ≤ gamma.len)
    (_hgamma' : Nat.floor (δ ^ 2 * (n + 1 : ℝ)) ≤ gamma'.len)
    (hsep : ∃ i : Fin d, CoordinateDifferenceGrows (d := d) δ n i gamma gamma') :
    PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
      ((∃ i : Fin d, CoordinateDifferenceGrows (d := d) δ n i gamma' gamma) →
        PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma) := by
  constructor
  · rcases hsep with ⟨i, -, hcoord⟩
    intro z hz
    have hcoord' : endpointSeparationRadius δ n ≤ dist (gamma.finish i) (z i) := by
      simpa [Int.dist_eq] using hcoord z hz
    exact le_trans hcoord' (dist_le_pi_dist gamma.finish z i)
  · intro hsep'
    rcases hsep' with ⟨i, -, hcoord⟩
    intro z hz
    have hcoord' : endpointSeparationRadius δ n ≤ dist (gamma'.finish i) (z i) := by
      simpa [Int.dist_eq] using hcoord z hz
    exact le_trans hcoord' (dist_le_pi_dist gamma'.finish z i)

-- ============================================================
-- Section 4: Blueprint case hypotheses
-- ============================================================

/-- Blueprint Case 1: `xn` and `xnp1` lie in different orthants. -/
def Case1Hypothesis (xn xnp1 : Zd d) : Prop :=
  DifferentOrthants xn xnp1

/-- Blueprint Case 2: `xnp1` is a positive axis point and `xn j > 0`. -/
def Case2Hypothesis (n : Nat) (xn xnp1 : Zd d) : Prop :=
  ∃ j : Fin d,
    Nonnegative xn ∧
      Nonnegative xnp1 ∧
        xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j ∧
          2 ≤ (positiveCoords xn).card ∧
            0 < xn j

/-- Blueprint Case 3: `xnp1` is a positive axis point and `xn j = 0`. -/
def Case3Hypothesis (n : Nat) (xn xnp1 : Zd d) : Prop :=
  ∃ j : Fin d,
    Nonnegative xn ∧
      Nonnegative xnp1 ∧
        xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j ∧
          2 ≤ (positiveCoords xn).card ∧
            xn j = 0

/-- Blueprint Case 4: both boundary points are axis points. -/
def Case4Hypothesis (n : Nat) (xn xnp1 : Zd d) : Prop :=
  ∃ i j : Fin d,
    xn = axisPoint (d := d) (n : Int) i ∧
      xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j

/-- Blueprint Case 5: `xnp1 = xn + e_j`, excluding the axis-point subcase. -/
def Case5Hypothesis (n : Nat) (xn xnp1 : Zd d) : Prop :=
  ∃ j : Fin d,
    Nonnegative xn ∧
      Nonnegative xnp1 ∧
        xnp1 = xn + Zd.e j ∧
          xn ≠ axisPoint (d := d) (n : Int) j

/--
Blueprint Case 6: `xnp1` has at least two positive coordinates and is farther
than one edge from `xn`.
-/
def Case6Hypothesis (xn xnp1 : Zd d) : Prop :=
  Nonnegative xn ∧
    Nonnegative xnp1 ∧
      2 ≤ (positiveCoords xnp1).card ∧
        2 ≤ Zd.l1Norm (xn - xnp1)

-- ============================================================
-- Section 5: Blueprint case stubs
-- ============================================================

/-- When δ = 0, HasDesiredDisjointPaths holds trivially: paths have length 0
    and the separation radius is 0, so all conditions are vacuously satisfied. -/
lemma hasDesiredDisjointPaths_of_delta_zero
    {n : Nat} {xn xnp1 : Zd d}
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1)) :
    HasDesiredDisjointPaths (d := d) n 0 xn xnp1 := by
  sorry

end DisjointPaths
