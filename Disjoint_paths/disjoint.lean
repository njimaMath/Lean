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


/-
Choose `r` with `xn r * xnp1 r < 0`. After permuting coordinates and
reflecting signs, the blueprint assumes
`xn = (xn 1, ..., xn k, 0, ..., 0)` with all displayed coordinates positive.
Let `J = {j | xnp1 j ≠ 0}`. Let `p` maximize `|xn p|` and let `q` maximize
`|xnp1 q|`. Using the large-coordinate observation, both `p` and `q` can serve
as reservoir coordinates while the paths remain on `Zd.sphere n ∪ Zd.sphere
  (n + 1)`.

For each `i ≠ p`, the inner family from `xn` alternates a move in the `i`
direction with a compensating move in direction `-e_p`: use `+e_i` when
`i <= k`, and use `-e_i` when `i > k`. For each `j ∈ J \ {q}`, the outer
family from `xnp1` increases the modulus of coordinate `j` while decreasing the
modulus of coordinate `q`. If `xnp1` is itself an axis point, the single outer
path is obtained by choosing any `j ≠ q`.

These paths move in distinct coordinate directions, so each family is
edge-disjoint and satisfies the monotone coordinate-gap hypothesis used in
`path_separation`. The `r`-th coordinates of the inner and outer families keep
opposite signs throughout, which makes the combined collection disjoint.

There are then two endpoint-separation subcases.

* If `xn r >= 3 * δ^2 * (n + 1)`, compare the `r`-th coordinates directly to
  obtain cross-family endpoint separation.
* If `xn r < 3 * δ^2 * (n + 1)`, then `p ≠ r`; extend each inner path by
  alternating `+e_r` and `-e_p` for another `δ^2 * (n + 1)` steps so the
  endpoints acquire positive `r`-coordinate at least `δ^2 * (n + 1)`, while
  every outer path keeps negative `r`-coordinate.
-/
/--
Intermediate Case 1 stub for the endpoint-separation subcase where the chosen
opposite-sign coordinate `r` of `xn` is already at least
`3 * δ^2 * (n + 1)`.

In this branch, the blueprint obtains the cross-family endpoint separation
directly by comparing `r`-th coordinates, without the extra extension used in
the complementary subcase.
-/
lemma exists_disjoint_paths_case1_large_coordinate
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {r : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hr_neg : xnp1 r < 0)
    (hr_large : 3 * δ ^ 2 * (n + 1 : ℝ) ≤ (xn r : ℝ)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry


lemma exists_disjoint_paths_case1_small_coordinate
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {r : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hr_pos : 0 < xn r)
    (hr_neg : xnp1 r < 0)
    (hr_small : 3 * δ ^ 2 * (n + 1 : ℝ) > (xn r : ℝ)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

/-- Case 1 stub: `xn` and `xnp1` lie in different orthants. -/

lemma exists_disjoint_paths_case1
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (horth : DifferentOrthants xn xnp1) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  rcases horth with ⟨r, hr⟩
  by_cases hr_neg : xnp1 r < 0
  · have hr_pos : 0 < xn r := by
      by_contra hxn_nonpos
      have hxn_nonpos' : xn r ≤ 0 := le_of_not_gt hxn_nonpos
      have hprod_nonneg : 0 ≤ xn r * xnp1 r := by
        by_cases hxr : xn r = 0
        · simp [hxr]
        · have hxn_neg : xn r < 0 := lt_of_le_of_ne hxn_nonpos' (by
            intro hx0
            exact hxr hx0)
          exact le_of_lt (Int.mul_pos_of_neg_of_neg hxn_neg hr_neg)
      exact (not_lt_of_ge hprod_nonneg) hr
    by_cases hr_large : 3 * δ ^ 2 * (n + 1 : ℝ) ≤ (xn r : ℝ)
    · exact exists_disjoint_paths_case1_large_coordinate
        hd hδ_nonneg hδ hlarge hxn hxnp1 hr_neg hr_large
    · exact exists_disjoint_paths_case1_small_coordinate
        hd hδ_nonneg hδ hlarge hxn hxnp1 hr_pos hr_neg (lt_of_not_ge hr_large)
  · have hr_pos_np1 : 0 < xnp1 r := by
      have hxnp1_nonneg : 0 ≤ xnp1 r := le_of_not_gt hr_neg
      have hxnp1_ne : xnp1 r ≠ 0 := by
        intro hx0
        have hr' := hr
        simp [hx0] at hr'
      exact lt_of_le_of_ne hxnp1_nonneg (by
        intro hx0
        exact hxnp1_ne hx0.symm)
    have hxn_neg : xn r < 0 := by
      by_contra hxn_nonneg
      have hxn_nonneg' : 0 ≤ xn r := le_of_not_gt hxn_nonneg
      have hprod_nonneg : 0 ≤ xn r * xnp1 r :=
        Int.mul_nonneg hxn_nonneg' (le_of_lt hr_pos_np1)
      exact (not_lt_of_ge hprod_nonneg) hr
    have hxn_neg_sphere : (-xn) ∈ Zd.sphere n := by
      simpa using hxn
    have hxnp1_neg_sphere : (-xnp1) ∈ Zd.sphere (n + 1) := by
      simpa using hxnp1
    have hr_neg_neg : (-xnp1) r < 0 := by
      change -(xnp1 r) < 0
      omega
    have hr_pos_neg : 0 < (-xn) r := by
      change 0 < -(xn r)
      omega
    by_cases hr_large : 3 * δ ^ 2 * (n + 1 : ℝ) ≤ (((-xn) r : Int) : ℝ)
    · have hneg_cfg : HasDesiredDisjointPaths (d := d) n δ (-xn) (-xnp1) :=
        exists_disjoint_paths_case1_large_coordinate
          hd hδ_nonneg hδ hlarge hxn_neg_sphere hxnp1_neg_sphere hr_neg_neg hr_large
      simpa using
        (hasDesiredDisjointPaths_neg (d := d) (n := n) (δ := δ)
          (xn := -xn) (xnp1 := -xnp1) hneg_cfg)
    · have hneg_cfg : HasDesiredDisjointPaths (d := d) n δ (-xn) (-xnp1) :=
        exists_disjoint_paths_case1_small_coordinate
          hd hδ_nonneg hδ hlarge hxn_neg_sphere hxnp1_neg_sphere hr_pos_neg hr_neg_neg
          (lt_of_not_ge hr_large)
      simpa using
        (hasDesiredDisjointPaths_neg (d := d) (n := n) (δ := δ)
          (xn := -xn) (xnp1 := -xnp1) hneg_cfg)

/-
From this point on the blueprint reduces to the same-orthant situation by
reflections, so the remaining cases assume both `xn` and `xnp1` are
nonnegative.
-/

/-
After reordering coordinates, the blueprint reduces to `j = 1` and
`xn = (xn 1, ..., xn k, 0, ..., 0)` with `k >= 2`, all displayed coordinates
positive, and `xn 2` maximal among coordinates `2, ..., d`.

The outer path `gamma_{n+1}^{(1)}` starts from `xnp1` and alternates `-e_1`
and `-e_2`. For the inner family from `xn`, use:

* `+e_i` then `-e_1` for `2 <= i <= k`,
* `+e_i` then `-e_1` for the positive-direction path when `i > k`,
* `-e_i` then `-e_1` for the negative-direction path when `i > k`,

continuing until the first coordinate becomes zero.

If `xn 1 >= δ^2 * (n + 1)`, the construction continues directly up to
`δ^2 * (n + 1)` steps. The blueprint separates the paths by tracking:

* the second coordinate, which is nonpositive and decreasing only on the outer
  path,
* the `i`-th coordinate, which is increasing only on `gamma_n^{(i,+)}`,
* for `i > k`, the `i`-th coordinate, which is decreasing only on
  `gamma_n^{(i,-)}`.

If `xn 1 < δ^2 * (n + 1)`, the inner paths first stop on the face `x 1 = 0`.
Call these stopping points `hatγ_n^{(i,±)}`. Since `xn 2` is maximal, their
second coordinates are still at least `δ^2 * (n + 1)`. The blueprint then
extends them using coordinate `2` as the new reservoir:

* `gamma_n^{(2,+)}` continues by `-e_1` and `-e_2`,
* `gamma_n^{(i,+)}` for `i >= 3` continues by `+e_i` and `-e_2`,
* `gamma_n^{(i,-)}` continues by `-e_i` and `-e_2`.

The distinguishing coordinate patterns remain intact, and the outer path stays
separated from the inner family by the first or second coordinate.
-/
/--
Intermediate Case 2 stub for the branch where the distinguished coordinate
`xn j` already has size at least `δ^2 * (n + 1)`.

In this branch, the blueprint keeps coordinate `j` as the reservoir
throughout: the inner paths run directly for `δ^2 * (n + 1)` steps, and the
outer axis path is separated from the inner family by the characteristic
coordinate behavior recorded in the case discussion above.
-/
lemma exists_disjoint_paths_case2_large_j_coordinate
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (haxis : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hcard : 2 ≤ (positiveCoords xn).card)
    (hj_large : δ ^ 2 * (n + 1 : ℝ) ≤ (xn j : ℝ)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry



lemma exists_disjoint_paths_case2_small_j_coordinate
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (haxis : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hcard : 2 ≤ (positiveCoords xn).card)
    (hj : 0 < xn j)
    (hj_small : δ ^ 2 * (n + 1 : ℝ) > (xn j : ℝ)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

/-
Case 2 stub: `xnp1` is a positive axis point and `xn j > 0`.
-/
lemma exists_disjoint_paths_case2
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (haxis : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hcard : 2 ≤ (positiveCoords xn).card)
    (hj : 0 < xn j) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  by_cases hj_large : δ ^ 2 * (n + 1 : ℝ) ≤ (xn j : ℝ);
  · apply exists_disjoint_paths_case2_large_j_coordinate hd hδ_nonneg hδ hlarge hxn hxnp1 hnonneg_n hnonneg_np1 haxis hcard hj_large;
  · apply exists_disjoint_paths_case2_small_j_coordinate hd hδ_nonneg hδ hlarge hxn hxnp1 hnonneg_n hnonneg_np1 haxis hcard hj (by
    exact not_le.mp hj_large)

/-
After reordering, the blueprint takes `j = 1` and
`xn = (0, xn 2, ..., xn k, 0, ..., 0)` with `k >= 2`, all displayed
coordinates positive, and `xn 2` maximal.

The outer path is the same as in Case 2. The inner family begins with short
prefixes that land on the face `x 1 = 0`:

* for `2 <= i <= k - 1`, use `+e_i` then `-e_{i+1}`,
* for `i = k`, use `+e_k` then `-e_2`,
* for `i > k`, use `± e_i` then `-e_2`.

These prefixes are edge-disjoint and end on `Zd.sphere n ∩ {x | x 1 = 0}`.
From those stopping points, the blueprint reuses the Case 2 continuation on the
face `x 1 = 0`.
-/
/--
Intermediate Case 3 core stub: constructs the shared inner/outer family coming
from the short prefixes and the reused Case 2 continuation on the `j`-zero
face, before the final extra inner path is added.
-/
lemma exists_disjoint_paths_case3_core
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (haxis : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hcard : 2 ≤ (positiveCoords xn).card)
    (hj0 : xn j = 0) :
    ∃ inner : PathBundle d n δ xn, ∃ outer : PathBundle d n δ xnp1,
      inner.paths.length = requiredInnerPathCount (d := d) n xn - 1 ∧
        outer.paths.length = requiredOuterPathCount (d := d) n xnp1 ∧
          (∀ gamma ∈ inner.paths, ∀ gamma' ∈ outer.paths,
            PathSpec.EdgeDisjoint gamma gamma') ∧
            inner.paths.Pairwise (fun gamma gamma' =>
              PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
                PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma) ∧
              outer.paths.Pairwise (fun gamma gamma' =>
                PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
                  PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma) ∧
                (∀ gamma ∈ inner.paths, ∀ gamma' ∈ outer.paths,
                  PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma gamma' ∧
                    PathSpec.EndpointFarFrom (endpointSeparationRadius δ n) gamma' gamma) := by
  sorry

/-

Because `xn` has an extra zero coordinate compared with Case 2, one additional
inner path is needed. It is
`gamma_n^{(1,+)}`, obtained by alternating `+e_1` and `-e_2` up to
`δ^2 * (n + 1)` steps. Since `xn 2` is maximal, this path stays on the allowed
shells. Its first coordinate is positive and increasing, while the other inner
paths have nonpositive first coordinate, and the outer path is separated from
it by the first coordinate as in Case 2.
-/
/--
Case 3 stub: once the core family is in place, the remaining step is to add the
extra inner path `gamma_n^{(1,+)}` and recover the missing inner-path count.
-/
lemma exists_disjoint_paths_case3
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (haxis : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hcard : 2 ≤ (positiveCoords xn).card)
    (hj0 : xn j = 0) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

/-
If `xn = n e_i` and `xnp1 = (n + 1) e_j` with `i ≠ j`, the blueprint reduces
to `i = 2`, `j = 1` and reuses the Case 3 construction, except that there is
no `gamma_n^{(2,+)}` path.

If `i = j`, the blueprint reduces to `i = j = 1` and reuses the Case 2
construction with the formal role of `k = 2`, even though `xn 2 = 0`. This is
done to avoid the intersection that would occur if one instead used the
negative `2`-direction path against the outer axis path.

Either way, the blueprint obtains one outer path from `xnp1` and `2 * d - 3`
inner paths from `xn`, all satisfying the shell, length, disjointness, and
endpoint-separation requirements.
-/
/--
Intermediate Case 4 stub for the branch `i ≠ j`, where the blueprint reuses
the Case 3 construction except for the absent `gamma_n^{(2,+)}` path.
-/
lemma exists_disjoint_paths_case4_distinct_axes
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {i j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (haxis_n : xn = axisPoint (d := d) (n : Int) i)
    (haxis_np1 : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hij : i ≠ j) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

/--
Intermediate Case 4 stub for the branch `i = j`, where the blueprint reuses
the Case 2 construction with the formal role of `k = 2`.
-/
lemma exists_disjoint_paths_case4_same_axis
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {i j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (haxis_n : xn = axisPoint (d := d) (n : Int) i)
    (haxis_np1 : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j)
    (hij : i = j) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

/-- Case 4 stub: both points are axis points. -/
lemma exists_disjoint_paths_case4
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {i j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (haxis_n : xn = axisPoint (d := d) (n : Int) i)
    (haxis_np1 : xnp1 = axisPoint (d := d) ((n + 1 : Nat) : Int) j) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  by_cases hij : i = j
  · exact exists_disjoint_paths_case4_same_axis hd hδ_nonneg hδ hlarge hxn hxnp1 haxis_n haxis_np1 hij
  · exact exists_disjoint_paths_case4_distinct_axes hd hδ_nonneg hδ hlarge hxn hxnp1 haxis_n haxis_np1 hij

/-
The remaining same-orthant analysis splits according to whether `xn` and
`xnp1` are neighbors. In the nonnegative orthant, the neighbor case is exactly
`xnp1 = xn + e_j` for some coordinate `j`.

After reordering coordinates, the blueprint takes `j = 1` and
`xn = (xn 1, ..., xn k, 0, ..., 0)` with the coordinates `2, ..., k` positive
and `xn 2` maximal among coordinates `2, ..., d`. Then
`xnp1 = xn + e_1`, and the outer family is indexed by `J = {2, ..., k}`.

The inner family is constructed exactly as in Cases 2 and 3. For each `j ∈ J`,
the first part of the outer path `gamma_{n+1}^{(j)}` alternates `-e_j` and
`+e_1`, either for `floor (δ^2 * (n + 1))` steps or until the `j`-th
coordinate reaches zero. If that happens early, the path is extended from the
stopping point using a reservoir coordinate `p` with large enough value.

When `xn 1 >= δ^2 * (n + 1)`, the blueprint may take `p = 1`. The path family
is then separated by unique coordinate behavior:

* for `2 <= i <= d`, the `i`-th coordinate increases only along
  `gamma_n^{(i,+)}`,
* for `2 <= j <= k`, the `j`-th coordinate decreases only along
  `gamma_{n+1}^{(j)}`,
* for `k + 1 <= i <= d`, the `i`-th coordinate decreases only along
  `gamma_n^{(i,-)}`.

When `xn 1 < δ^2 * (n + 1)`, these unique-coordinate arguments remain valid
only from coordinate `3` onward, so the blueprint isolates
`gamma_{n+1}^{(2)}` and `gamma_n^{(2,+)}`. Since `xn 2 > n / d`, one can take
`p = 2`, so `gamma_{n+1}^{(2)}` keeps its long first part, increasing the first
coordinate and decreasing the second every two steps. The other outer paths
either keep the second coordinate fixed on their first part or keep the first
coordinate fixed on their extension, which is enough for `path_separation`.
Likewise, the first coordinates of the inner paths are nonincreasing, while the
extended part of `gamma_n^{(2,+)}` is the only one with negative first
coordinate decreasing every two steps.

If `xn 1 = 0`, the blueprint adds one extra inner path `gamma_n^{(1,-)}` by
repeating the `2 * d - 2` step cycle
`-e_1, -e_2, +e_3, -e_2, +e_4, -e_2, ..., +e_d, -e_2`.
This path is the only one for which the first and second coordinates both
decrease while all later coordinates increase on each full cycle. That
distinguishes it from the other inner paths, and the outer paths keep
nondecreasing first coordinate in this subcase.

Intermediate Case 5 stub for the normalized branch `0 < xn j`, corresponding
to the blueprint subcase `x_n(1) > 0` after reordering coordinates.

This packages the main neighbor-case construction before the residual
`xn j = 0` branch adds the extra inner path discussed in the blueprint.
-/
lemma exists_disjoint_paths_case5_positive_neighbor_coordinate
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (hneigh : xnp1 = xn + Zd.e j)
    (hnot_axis : xn ≠ axisPoint (d := d) (n : Int) j)
    (hj_pos : 0 < xn j) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

/-- Case 5 stub: `xnp1 = xn + e_j`, excluding the axis-point subcase. -/
lemma exists_disjoint_paths_case5
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {j : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (hneigh : xnp1 = xn + Zd.e j)
    (hnot_axis : xn ≠ axisPoint (d := d) (n : Int) j) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  by_cases hj : 0 < xn j
  · exact
      exists_disjoint_paths_case5_positive_neighbor_coordinate
        hd hδ_nonneg hδ hlarge hxn hxnp1 hnonneg_n hnonneg_np1 hneigh hnot_axis hj
  · have hj_zero : xn j = 0 := by
      exact le_antisymm (le_of_not_gt hj) (hnonneg_n j)
    sorry

/-
This is the remaining same-orthant case where `xnp1` has at least two positive
coordinates and `|xn - xnp1|_1 >= 2`. After reordering coordinates, the
blueprint assumes:

* `xnp1 1 - xn 1 >= 1`,
* `xn = (xn 1, ..., xn k, 0, ..., 0)` with coordinates `2, ..., k` positive,
* `xn 2` is maximal among coordinates `2, ..., d`,
* `J = {j in {2, ..., d} | xnp1 j > 0}`,
* there exists `r in {2, ..., k}` with `xn r > xnp1 r`.

When `xn ≠ n e_2`, the inner family is built as in Case 5, and the outer paths
start as in Case 5 as well.

If `xnp1 1 < (1 - 2 * d * δ^2) * (n + 1)`, choose `p ≠ 1` with
`xnp1 p > 2 * δ^2 * (n + 1)` and extend each stopped outer path by repeating
`-e_j, -e_p, +e_1, -e_p`.
Then the inner first coordinates decrease while the outer first coordinates are
nondecreasing, which gives the needed cross-family separation.

If `xnp1 1 >= (1 - 2 * d * δ^2) * (n + 1)`, the blueprint first alternates
`-e_j` and `-e_r` until the `r`-th coordinate vanishes (unless `j = r`), then
repeats `-e_j, -e_1, -e_r, -e_1`.
The intended comparison coordinate is `r`. The blueprint itself notes a gap
here: in one subcase inherited from Case 5, some inner-path extensions may also
decrease the `r`-th coordinate, so a later formal proof will need either a
different comparison coordinate or a refined extension scheme.

If additionally `xn 1 = 0`, the blueprint adds an extra inner path
`gamma_n^{(1,-)}` with cycle `-e_1, -e_2, +e_3, -e_2`. This path has negative,
strictly decreasing first coordinate, while the relevant competing paths keep
nonnegative first coordinate or have endpoints already separated in the first
coordinate. In the final leftover subcase `xn = n e_2`, the same construction
is used but `gamma_n^{(2,+)}` is omitted, and the extra path keeps the desired
count `2 * d - 3`.
-/
/-- Case 6 stub: `xnp1` has at least two positive coordinates and lies farther than one edge away. -/
lemma exists_disjoint_paths_case6
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1)
    (hcard : 2 ≤ (positiveCoords xnp1).card)
    (hdist : 2 ≤ Zd.l1Norm (xn - xnp1)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  sorry

-- ============================================================
-- Section 5.5: Sign-flip reduction infrastructure
-- ============================================================

/-- Coordinate-wise sign flip by a sign vector `s`. -/
def signFlip (s : Fin d → Int) (x : Zd d) : Zd d := fun i => s i * x i

/-
A ±1 sign flip preserves sphere membership.
-/
lemma signFlip_mem_sphere {s : Fin d → Int} (hs : ∀ i, s i = 1 ∨ s i = -1)
    {n : Nat} {x : Zd d} (hx : x ∈ Zd.sphere n) :
    signFlip s x ∈ Zd.sphere n := by
  unfold Zd.sphere at*;
  unfold signFlip; simp_all +decide [ Zd.l1Norm ] ;
  exact Eq.trans ( Finset.sum_congr rfl fun i _ => by rcases hs i with ha | ha <;> rw [ ha ] <;> norm_num ) hx

@[simp] lemma signFlip_signFlip {s : Fin d → Int} (hs : ∀ i, s i = 1 ∨ s i = -1)
    (x : Zd d) : signFlip s (signFlip s x) = x := by
  ext i; unfold signFlip; rcases hs i with ( h | h ) <;> simp +decide [ h ] ;

lemma signFlip_adj {s : Fin d → Int} (hs : ∀ i, s i = 1 ∨ s i = -1)
    {x y : Zd d} : Adj (signFlip s x) (signFlip s y) ↔ Adj x y := by
  unfold Adj;
  unfold signFlip Zd.e;
  constructor <;> rintro ⟨ i, hi | hi ⟩ <;> use i <;> simp_all +decide [ funext_iff ];
  · grind;
  · grind;
  · grind;
  · grind +splitIndPred

@[simp] lemma signFlip_nonzeroCoords {s : Fin d → Int} (hs : ∀ i, s i = 1 ∨ s i = -1)
    (x : Zd d) : Zd.nonzeroCoords (signFlip s x) = Zd.nonzeroCoords x := by
  ext i; simp [signFlip, hs];
  cases hs i <;> simp +decide [ * ]

lemma signFlip_isSignedAxisPoint {s : Fin d → Int} (hs : ∀ i, s i = 1 ∨ s i = -1)
    {m : Nat} {x : Zd d} :
    IsSignedAxisPoint (d := d) m (signFlip s x) ↔ IsSignedAxisPoint (d := d) m x := by
  constructor <;> rintro ⟨ i, hi ⟩;
  · have := congr_fun hi i; simp_all +decide [ signFlip, axisPoint ] ;
    cases hs i <;> simp_all +decide [ IsSignedAxisPoint ];
    · left; use i; ext j; by_cases hj : j = i <;> simp_all +decide [ signFlip, axisPoint ] ;
      replace hi := congr_fun hi j; simp_all +decide [ signFlip, axisPoint ] ;
      cases hs j <;> aesop;
    · right; use i; ext j; by_cases hj : j = i <;> simp_all +decide [ axisPoint ] ;
      · grind;
      · replace hi := congr_fun hi j; simp_all +decide [ signFlip, axisPoint ] ;
        cases hs j <;> aesop;
  · obtain ⟨ i, hi ⟩ := ‹IsAxisPoint ( -m : ℤ ) ( signFlip s x ) ›;
    have := congr_fun hi i; simp_all +decide [ signFlip ] ;
    cases hs i <;> simp_all +decide [ axisPoint ];
    · refine' Or.inr ⟨ i, _ ⟩;
      ext j; by_cases hj : j = i <;> simp_all +decide [ axisPoint ] ;
      replace hi := congr_fun hi j; simp_all +decide [ signFlip, axisPoint ] ;
      exact hi.resolve_left ( by cases hs j <;> linarith );
    · refine' Or.inl ⟨ i, _ ⟩;
      ext j; replace hi := congr_fun hi j; by_cases hj : j = i <;> simp_all +decide [ axisPoint ] ;
      cases hs j <;> simp_all +decide [ signFlip ];
  · cases hs i <;> [ left; right ] <;> use i <;> ext j <;> simp +decide [ *, axisPoint, signFlip ];
    · grind;
    · grind;
  · obtain ⟨ i, rfl ⟩ := ‹IsAxisPoint ( -m : ℤ ) x›;
    unfold IsSignedAxisPoint;
    cases hs i <;> simp +decide [ *, IsAxisPoint ];
    · exact Or.inr ⟨ i, by ext j; by_cases hj : j = i <;> simp +decide [ *, signFlip, axisPoint ] ⟩;
    · exact Or.inl ⟨ i, by ext j; by_cases hj : j = i <;> simp +decide [ *, signFlip, axisPoint ] ⟩

@[simp] lemma requiredInnerPathCount_signFlip {s : Fin d → Int}
    (hs : ∀ i, s i = 1 ∨ s i = -1) (n : Nat) (x : Zd d) :
    requiredInnerPathCount (d := d) n (signFlip s x) =
      requiredInnerPathCount (d := d) n x := by
  unfold requiredInnerPathCount;
  rw [ signFlip_isSignedAxisPoint hs, signFlip_nonzeroCoords hs ]

@[simp] lemma requiredOuterPathCount_signFlip {s : Fin d → Int}
    (hs : ∀ i, s i = 1 ∨ s i = -1) (n : Nat) (x : Zd d) :
    requiredOuterPathCount (d := d) n (signFlip s x) =
      requiredOuterPathCount (d := d) n x := by
  unfold requiredOuterPathCount;
  -- Apply the lemma that states IsSignedAxisPoint is preserved under sign flips.
  have h_isSignedAxisPoint : IsSignedAxisPoint (n + 1) (signFlip s x) ↔ IsSignedAxisPoint (n + 1) x := by
    exact signFlip_isSignedAxisPoint hs
  aesop

lemma signFlip_dist {s : Fin d → Int} (hs : ∀ i, s i = 1 ∨ s i = -1)
    (x y : Zd d) : dist (signFlip s x) (signFlip s y) = dist x y := by
  simp +decide [ dist_eq_norm, Pi.norm_def ];
  congr! 2 with i ; cases hs i <;> simp +decide [ *, signFlip ] ; ring;
  rw [ ← nnnorm_neg ] ; ring;

lemma signFlip_shellUnion {s : Fin d → Int} (hs : ∀ i, s i = 1 ∨ s i = -1)
    {n : Nat} {x : Zd d} : signFlip s x ∈ shellUnion (d := d) n ↔
      x ∈ shellUnion (d := d) n := by
  simp_all +decide [ shellUnion, Zd.l1Norm ];
  simp +decide only [Zd.sphere];
  unfold signFlip; simp +decide [ Zd.l1Norm, abs_mul ];
  grind

namespace FinitePath

/-- Apply a ±1 sign flip to a finite lattice path. -/
def applySignFlip {n : Nat} (s : Fin d → Int) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (gamma : FinitePath d n) : FinitePath d n where
  toVertex i := signFlip s (gamma i)
  adjacent' i := (signFlip_adj hs).mpr (gamma.adjacent i)

@[simp] lemma applySignFlip_apply {n : Nat} {s : Fin d → Int} {hs : ∀ i, s i = 1 ∨ s i = -1}
    {gamma : FinitePath d n} (i : Fin (n + 1)) :
    (gamma.applySignFlip s hs) i = signFlip s (gamma i) := rfl

end FinitePath

namespace PathSpec

/-- Apply a ±1 sign flip to a path specification. -/
def applySignFlip (s : Fin d → Int) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (gamma : PathSpec d) : PathSpec d where
  len := gamma.len
  path := gamma.path.applySignFlip s hs

@[simp] lemma applySignFlip_len {s : Fin d → Int} {hs : ∀ i, s i = 1 ∨ s i = -1}
    (gamma : PathSpec d) : (gamma.applySignFlip s hs).len = gamma.len := rfl

@[simp] lemma applySignFlip_start {s : Fin d → Int} {hs : ∀ i, s i = 1 ∨ s i = -1}
    (gamma : PathSpec d) :
    (gamma.applySignFlip s hs).start = signFlip s gamma.start := rfl

@[simp] lemma applySignFlip_finish {s : Fin d → Int} {hs : ∀ i, s i = 1 ∨ s i = -1}
    (gamma : PathSpec d) :
    (gamma.applySignFlip s hs).finish = signFlip s gamma.finish := rfl

lemma mem_vertexSet_applySignFlip {s : Fin d → Int} {hs : ∀ i, s i = 1 ∨ s i = -1}
    {gamma : PathSpec d} {z : Zd d} :
    z ∈ (gamma.applySignFlip s hs).vertexSet ↔ signFlip s z ∈ gamma.vertexSet := by
  -- By definition of applySignFlip, we have that z ∈ (applySignFlip s hs gamma).vertexSet if and only if there exists some i such that signFlip s (gamma.path i) = z.
  simp [PathSpec.vertexSet, applySignFlip];
  constructor <;> intro h <;> cases' h with i hi;
  · exact ⟨ i, by aesop ⟩;
  · use i;
    convert congr_arg ( fun x => signFlip s x ) hi using 1;
    exact Eq.symm ( signFlip_signFlip hs z )

lemma mem_edgeSet_applySignFlip {s : Fin d → Int} {hs : ∀ i, s i = 1 ∨ s i = -1}
    {gamma : PathSpec d} {e : Zd d × Zd d} :
    e ∈ (gamma.applySignFlip s hs).edgeSet ↔
      (signFlip s e.1, signFlip s e.2) ∈ gamma.edgeSet := by
  constructor
  · rintro ⟨i, h | h⟩
    · refine ⟨i, Or.inl ?_⟩
      have hflip := congrArg (fun p : Zd d × Zd d => (signFlip s p.1, signFlip s p.2)) h
      simpa [PathSpec.edgeSet, PathSpec.applySignFlip, FinitePath.applySignFlip,
        signFlip_signFlip hs] using hflip
    · refine ⟨i, Or.inr ?_⟩
      have hflip := congrArg (fun p : Zd d × Zd d => (signFlip s p.1, signFlip s p.2)) h
      simpa [PathSpec.edgeSet, PathSpec.applySignFlip, FinitePath.applySignFlip,
        signFlip_signFlip hs] using hflip
  · rintro ⟨i, h | h⟩
    · refine ⟨i, Or.inl ?_⟩
      have hflip := congrArg (fun p : Zd d × Zd d => (signFlip s p.1, signFlip s p.2)) h
      simpa [PathSpec.edgeSet, PathSpec.applySignFlip, FinitePath.applySignFlip,
        signFlip_signFlip hs] using hflip
    · refine ⟨i, Or.inr ?_⟩
      have hflip := congrArg (fun p : Zd d × Zd d => (signFlip s p.1, signFlip s p.2)) h
      simpa [PathSpec.edgeSet, PathSpec.applySignFlip, FinitePath.applySignFlip,
        signFlip_signFlip hs] using hflip

lemma edgeDisjoint_applySignFlip {s : Fin d → Int} {hs : ∀ i, s i = 1 ∨ s i = -1}
    {gamma gamma' : PathSpec d} :
    EdgeDisjoint (gamma.applySignFlip s hs) (gamma'.applySignFlip s hs) ↔
      EdgeDisjoint gamma gamma' := by
  constructor
  · intro h
    refine Set.disjoint_left.2 ?_
    intro e he he'
    have hdisj := Set.disjoint_left.1 h
    have he_flip : (signFlip s e.1, signFlip s e.2) ∈ (gamma.applySignFlip s hs).edgeSet := by
      apply (mem_edgeSet_applySignFlip (s := s) (hs := hs)
        (gamma := gamma) (e := (signFlip s e.1, signFlip s e.2))).2
      simpa [signFlip_signFlip hs] using he
    have he'_flip : (signFlip s e.1, signFlip s e.2) ∈ (gamma'.applySignFlip s hs).edgeSet := by
      apply (mem_edgeSet_applySignFlip (s := s) (hs := hs)
        (gamma := gamma') (e := (signFlip s e.1, signFlip s e.2))).2
      simpa [signFlip_signFlip hs] using he'
    exact hdisj he_flip he'_flip
  · intro h
    refine Set.disjoint_left.2 ?_
    intro e he he'
    have hdisj := Set.disjoint_left.1 h
    have he_orig : (signFlip s e.1, signFlip s e.2) ∈ gamma.edgeSet :=
      (mem_edgeSet_applySignFlip (s := s) (hs := hs) (gamma := gamma) (e := e)).1 he
    have he'_orig : (signFlip s e.1, signFlip s e.2) ∈ gamma'.edgeSet :=
      (mem_edgeSet_applySignFlip (s := s) (hs := hs) (gamma := gamma') (e := e)).1 he'
    exact hdisj he_orig he'_orig

lemma endpointFarFrom_applySignFlip {s : Fin d → Int} {hs : ∀ i, s i = 1 ∨ s i = -1}
    {r : ℝ} {gamma gamma' : PathSpec d} :
    EndpointFarFrom r (gamma.applySignFlip s hs) (gamma'.applySignFlip s hs) ↔
      EndpointFarFrom r gamma gamma' := by
  constructor <;> intro hr;
  · intro z hz;
    convert hr ( signFlip s z ) ?_ using 1;
    · rw [ ← signFlip_dist hs ];
      rfl;
    · obtain ⟨ i, hi ⟩ := hz;
      exact ⟨ i, by aesop ⟩;
  · intro z hz;
    convert hr ( signFlip s z ) _ using 1;
    · convert signFlip_dist hs _ _ using 2 ; aesop;
    · exact mem_vertexSet_applySignFlip.mp hz

lemma staysIn_shellUnion_applySignFlip {s : Fin d → Int} {hs : ∀ i, s i = 1 ∨ s i = -1}
    {n : Nat} {gamma : PathSpec d} :
    (gamma.applySignFlip s hs).staysIn (shellUnion (d := d) n) ↔
      gamma.staysIn (shellUnion (d := d) n) := by
  unfold staysIn;
  simp +decide only [FinitePath.staysIn, applySignFlip];
  simp +decide [ FinitePath.applySignFlip, signFlip_shellUnion hs ]

end PathSpec

namespace PathBundle

/-- Apply a ±1 sign flip to a path bundle. -/
def applySignFlip {n : Nat} {δ : ℝ} {x : Zd d}
    (s : Fin d → Int) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (bundle : PathBundle d n δ (signFlip s x)) :
    PathBundle d n δ x where
  paths := bundle.paths.map (fun p => p.applySignFlip s hs)
  starts_at := by
    intro gamma hgamma
    rcases List.mem_map.1 hgamma with ⟨g, hg, rfl⟩
    simp [bundle.starts_at g hg, signFlip_signFlip hs]
  length_lower := by
    intro gamma hgamma
    rcases List.mem_map.1 hgamma with ⟨g, hg, rfl⟩
    simpa using bundle.length_lower g hg
  length_upper := by
    intro gamma hgamma
    rcases List.mem_map.1 hgamma with ⟨g, hg, rfl⟩
    simpa using bundle.length_upper g hg
  stays_on_shells := by
    intro gamma hgamma
    rcases List.mem_map.1 hgamma with ⟨g, hg, rfl⟩
    exact (PathSpec.staysIn_shellUnion_applySignFlip (hs := hs)).mpr
      (bundle.stays_on_shells g hg)
  pairwise_edge_disjoint := by
    exact List.Pairwise.map _
      (fun g g' h => (PathSpec.edgeDisjoint_applySignFlip (hs := hs)).mpr h)
      bundle.pairwise_edge_disjoint

end PathBundle

/-
`HasDesiredDisjointPaths` is invariant under ±1 sign flips.
-/
lemma hasDesiredDisjointPaths_signFlip {s : Fin d → Int} (hs : ∀ i, s i = 1 ∨ s i = -1)
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} :
    HasDesiredDisjointPaths (d := d) n δ (signFlip s xn) (signFlip s xnp1) →
      HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  intro h
  obtain ⟨cfg⟩ := h;
  use PathBundle.applySignFlip s hs cfg.inner, PathBundle.applySignFlip s hs cfg.outer;
  all_goals norm_num [PathBundle.applySignFlip, cfg.inner_count, cfg.outer_count, cfg.cross_edge_disjoint, cfg.inner_endpoint_separated, cfg.outer_endpoint_separated, cfg.cross_endpoint_separated];
  any_goals rw [ List.pairwise_map ];
  any_goals rw [ requiredInnerPathCount_signFlip hs ];
  · exact requiredOuterPathCount_signFlip hs n xnp1;
  · exact fun gamma hgamma gamma' hgamma' => ( PathSpec.edgeDisjoint_applySignFlip ( hs := hs ) ).mpr ( cfg.cross_edge_disjoint gamma hgamma gamma' hgamma' );
  · exact List.Pairwise.imp ( fun h => by simp [ PathSpec.endpointFarFrom_applySignFlip ] at *; tauto ) cfg.inner_endpoint_separated;
  · exact List.Pairwise.imp_of_mem ( fun x y h => by simpa only [ PathSpec.endpointFarFrom_applySignFlip ] using h ) cfg.outer_endpoint_separated;
  · intro gamma hgamma gamma' hgamma'
    have := cfg.cross_endpoint_separated gamma hgamma gamma' hgamma'
    exact ⟨by
    exact PathSpec.endpointFarFrom_applySignFlip.mpr this.1, by
      exact PathSpec.endpointFarFrom_applySignFlip.mpr this.2⟩

/-
When two points are in the same orthant, a ±1 sign flip makes both nonneg.
-/
lemma same_orthant_nonneg_signFlip {xn xnp1 : Zd d}
    (h : ¬DifferentOrthants xn xnp1) :
    ∃ s : Fin d → Int, (∀ i, s i = 1 ∨ s i = -1) ∧
      Nonnegative (signFlip s xn) ∧ Nonnegative (signFlip s xnp1) := by
  refine' ⟨ fun i => if xn i < 0 ∨ xnp1 i < 0 then -1 else 1, _, _, _ ⟩ <;> norm_num [ Nonnegative ];
  · exact fun i hi => le_or_gt _ _;
  · -- By definition of signFlip, we need to show that for each i, the product of the sign and xn i is non-negative.
    intro i
    simp [signFlip];
    split_ifs <;> simp_all +decide [ DifferentOrthants ];
    cases ‹_› <;> nlinarith [ h i ];
  · intro i;
    by_cases hi : xn i < 0 <;> by_cases hi' : xnp1 i < 0 <;> simp +decide [ hi, hi', signFlip ];
    · linarith;
    · contrapose! h;
      exact ⟨ i, by nlinarith ⟩;
    · linarith;
    · linarith

/-
A nonneg point on `Zd.sphere n` with at most one positive coordinate is an
axis point `axisPoint (↑n) i` for some `i`.
-/
lemma nonneg_sphere_axis_of_card_le_one {x : Zd d} {n : Nat}
    (hd : 0 < d)
    (hx : x ∈ Zd.sphere n) (hnonneg : Nonnegative x)
    (hcard : (positiveCoords x).card ≤ 1) :
    ∃ i : Fin d, x = axisPoint (d := d) (n : Int) i := by
  by_cases h_all_zero : ∀ i, x i = 0;
  · simp_all +decide [ Zd.sphere ];
    simp_all +decide [ funext_iff, Zd.l1Norm ];
    exact ⟨ ⟨ 0, by linarith ⟩, fun i => by unfold axisPoint; aesop ⟩;
  · obtain ⟨i, hi⟩ : ∃ i : Fin d, x i ≠ 0 ∧ ∀ j : Fin d, j ≠ i → x j = 0 := by
      obtain ⟨i, hi⟩ : ∃ i : Fin d, x i ≠ 0 ∧ ∀ j : Fin d, j ∈ positiveCoords x → j = i := by
        obtain ⟨i, hi⟩ : ∃ i : Fin d, i ∈ positiveCoords x := by
          exact Exists.elim ( not_forall.mp h_all_zero ) fun i hi => ⟨ i, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, lt_of_le_of_ne ( hnonneg i ) ( Ne.symm hi ) ⟩ ⟩;
        exact ⟨ i, by aesop, fun j hj => by rw [ Finset.card_le_one_iff ] at hcard; aesop ⟩;
      exact ⟨ i, hi.1, fun j hj => le_antisymm ( le_of_not_gt fun hj' => hj <| hi.2 j <| Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hj' ⟩ ) ( hnonneg j ) ⟩;
    use i; ext j; by_cases hj : j = i <;> simp_all +decide [ Zd.sphere ] ;
    · simp_all +decide [ Zd.l1Norm, axisPoint ];
      rw [ ← hx, Finset.sum_eq_single i ] <;> simp_all +decide [ Int.natAbs_eq_iff ];
      rw [ abs_of_nonneg ( hnonneg i ) ];
    · unfold axisPoint; aesop;

/-
A nonneg point on a sphere that is not an axis point has ≥ 2 positive coords.
-/
lemma nonneg_sphere_not_axis_two_positive {x : Zd d} {n : Nat}
    (hd : 0 < d)
    (hx : x ∈ Zd.sphere n) (hnonneg : Nonnegative x)
    (hnot_axis : ∀ i : Fin d, x ≠ axisPoint (d := d) (n : Int) i) :
    2 ≤ (positiveCoords x).card := by
  have h := nonneg_sphere_axis_of_card_le_one hd hx hnonneg;
  exact not_lt.mp fun contra => by obtain ⟨ i, hi ⟩ := h ( by linarith ) ; exact hnot_axis i hi;

/-
Two nonneg points on adjacent spheres at `ℓ¹`-distance 1 are lattice
neighbors: `xnp1 = xn + e_j` for some coordinate `j`.
-/
lemma nonneg_sphere_neighbor_of_dist_one {xn xnp1 : Zd d} {n : Nat}
    (hxn : xn ∈ Zd.sphere n) (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn) (hnonneg_np1 : Nonnegative xnp1)
    (hdist : Zd.l1Norm (xn - xnp1) = 1) :
    ∃ j : Fin d, xnp1 = xn + Zd.e j := by
  obtain ⟨j, hj⟩ : ∃ j : Fin d, xn j ≠ xnp1 j ∧ ∀ i ∈ Finset.univ.erase j, xn i = xnp1 i := by
    -- Since the sum of absolute differences is 1, there must be exactly one index $j$ where $|x_j - x_{n+1,j}| = 1$.
    obtain ⟨j, hj⟩ : ∃ j : Fin d, Int.natAbs (xn j - xnp1 j) = 1 := by
      contrapose! hdist; simp_all +decide [ Zd.l1Norm ] ;
      by_contra h_contra;
      exact absurd ( h_contra ▸ Finset.sum_eq_zero fun i hi => Nat.eq_zero_of_le_zero ( Nat.le_of_not_lt fun hi' => hdist i <| by linarith [ Finset.single_le_sum ( fun a _ => Nat.zero_le ( Int.natAbs ( xn a - xnp1 a ) ) ) hi ] ) ) ( by norm_num );
    refine' ⟨ j, _, _ ⟩ <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · omega;
    · intro i hi; contrapose! hdist; simp_all +decide [ Zd.l1Norm, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ) ] ;
      exact ⟨ i, hi, sub_ne_zero_of_ne hdist ⟩;
  -- Since $xn$ and $xnp1$ are nonnegative and $xn j \ne xnp1 j$, we must have $xnp1 j = xn j + 1$.
  have hj_eq : xnp1 j = xn j + 1 := by
    have hj_eq : ∑ i, xn i = n ∧ ∑ i, xnp1 i = n + 1 := by
      simp_all +decide [ Zd.sphere, Zd.l1Norm ];
      exact ⟨ by simpa [ ← Int.natCast_inj, abs_of_nonneg ( hnonneg_n _ ) ] using hxn, by simpa [ ← Int.natCast_inj, abs_of_nonneg ( hnonneg_np1 _ ) ] using hxnp1 ⟩;
    rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ), Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ) ] at hj_eq;
    rw [ Finset.sum_congr rfl fun i hi => hj.2 i <| by aesop ] at hj_eq ; linarith;
  use j; ext i; by_cases hi : i = j <;> simp_all +decide [ Zd.e ] ;

/-
Points on distinct spheres have positive ℓ¹-distance.
-/
lemma sphere_l1_dist_pos {xn xnp1 : Zd d} {n : Nat}
    (hxn : xn ∈ Zd.sphere n) (hxnp1 : xnp1 ∈ Zd.sphere (n + 1)) :
    0 < Zd.l1Norm (xn - xnp1) := by
  -- By contradiction, assume that the ℓ¹ norm is zero.
  by_contra h_zero_norm
  have h_eq : xn = xnp1 := by
    simp_all +decide [ Zd.l1Norm ];
    exact funext fun i => sub_eq_zero.mp ( h_zero_norm i )
  rw [h_eq] at hxn
  simp_all +decide [ Zd.sphere ]

/-
If `xnp1 = xn + e_j` and `xnp1` has at least two positive coordinates, then
`xn` is not the axis point `axisPoint n j`.
-/
lemma neighbor_not_axis_of_card_ge_two {xn xnp1 : Zd d} {n : Nat} {j : Fin d}
    (hneigh : xnp1 = xn + Zd.e j)
    (hcard : 2 ≤ (positiveCoords xnp1).card)
    (hnonneg : Nonnegative xn) :
    xn ≠ axisPoint (d := d) (n : Int) j := by
  contrapose! hcard;
  rw [ Finset.card_eq_one.mpr ];
  · decide +kernel;
  · use j;
    ext i; simp [hneigh, hcard, positiveCoords];
    unfold axisPoint Zd.e; aesop;

/-- The nonneg case: dispatches to Cases 2–6. -/
lemma main_theorem_nonneg
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hnonneg_n : Nonnegative xn)
    (hnonneg_np1 : Nonnegative xnp1) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  by_cases h_axis_card : (positiveCoords xnp1).card ≤ 1
  · -- xnp1 is an axis point
    obtain ⟨j, hj⟩ := nonneg_sphere_axis_of_card_le_one (by omega) hxnp1 hnonneg_np1 h_axis_card
    by_cases h_xn_axis : ∃ i : Fin d, xn = axisPoint (d := d) (n : Int) i
    · -- Case 4: both are axis points
      obtain ⟨i, hi⟩ := h_xn_axis
      exact exists_disjoint_paths_case4 hd hδ_nonneg hδ hlarge hxn hxnp1 hi hj
    · -- xn is not an axis point
      push_neg at h_xn_axis
      have hcard : 2 ≤ (positiveCoords xn).card :=
        nonneg_sphere_not_axis_two_positive (by omega) hxn hnonneg_n h_xn_axis
      by_cases hj_pos : 0 < xn j
      · -- Case 2: xn j > 0
        exact exists_disjoint_paths_case2 hd hδ_nonneg hδ hlarge hxn hxnp1
          hnonneg_n hnonneg_np1 hj hcard hj_pos
      · -- Case 3: xn j = 0
        have hj_zero : xn j = 0 := le_antisymm (le_of_not_gt hj_pos) (hnonneg_n j)
        exact exists_disjoint_paths_case3 hd hδ_nonneg hδ hlarge hxn hxnp1
          hnonneg_n hnonneg_np1 hj hcard hj_zero
  · -- xnp1 has ≥ 2 positive coords
    push_neg at h_axis_card
    have hcard : 2 ≤ (positiveCoords xnp1).card := h_axis_card
    by_cases h_dist : Zd.l1Norm (xn - xnp1) < 2
    · -- Distance 1 (must be ≥ 1 by sphere_l1_dist_pos)
      have h_pos := sphere_l1_dist_pos hxn hxnp1
      have h_dist_1 : Zd.l1Norm (xn - xnp1) = 1 := by omega
      obtain ⟨j, hj⟩ := nonneg_sphere_neighbor_of_dist_one hxn hxnp1
        hnonneg_n hnonneg_np1 h_dist_1
      have h_not_axis : xn ≠ axisPoint (d := d) (n : Int) j :=
        neighbor_not_axis_of_card_ge_two hj hcard hnonneg_n
      exact exists_disjoint_paths_case5 hd hδ_nonneg hδ hlarge hxn hxnp1
        hnonneg_n hnonneg_np1 hj h_not_axis
    · -- Case 6: distance ≥ 2
      exact exists_disjoint_paths_case6 hd hδ_nonneg hδ hlarge hxn hxnp1
        hnonneg_n hnonneg_np1 hcard (by omega)

-- ============================================================
-- Section 5.7: Zigzag path construction for negative δ
-- ============================================================

/-- Vertex of a zigzag path alternating between `x` and `y`. -/
private def zigzagVertex (x y : Zd d) (k : Nat) : Zd d :=
  if k % 2 = 0 then x else y

private lemma zigzagVertex_zero (x y : Zd d) : zigzagVertex x y 0 = x := by
  simp [zigzagVertex]

private lemma zigzagVertex_mem {x y : Zd d} {S : Set (Zd d)}
    (hx : x ∈ S) (hy : y ∈ S) (k : Nat) : zigzagVertex x y k ∈ S := by
  unfold zigzagVertex; split <;> assumption

private lemma zigzagVertex_adj {x y : Zd d} (hadj : Adj x y) (k : Nat) :
    Adj (zigzagVertex x y k) (zigzagVertex x y (k + 1)) := by
  unfold zigzagVertex
  by_cases hk : k % 2 = 0
  · simp [hk, show (k + 1) % 2 ≠ 0 from by omega]; exact hadj
  · simp [show k % 2 ≠ 0 from hk, show (k + 1) % 2 = 0 from by omega]; exact adj_symm hadj

/-- A finite path that zigzags between two adjacent vertices. -/
private def zigzagFinitePath (x y : Zd d) (hadj : Adj x y) (len : Nat) : FinitePath d len where
  toVertex k := zigzagVertex x y k.val
  adjacent' k := by
    show Adj (zigzagVertex x y k.castSucc.val) (zigzagVertex x y k.succ.val)
    rw [Fin.val_castSucc, Fin.val_succ]
    exact zigzagVertex_adj hadj k.val

/-- A `PathSpec` wrapping a zigzag path. -/
private def zigzagPathSpec (x y : Zd d) (hadj : Adj x y) (len : Nat) : PathSpec d :=
  ⟨len, zigzagFinitePath x y hadj len⟩

private lemma zigzagPathSpec_start (x y : Zd d) (hadj : Adj x y) (len : Nat) :
    (zigzagPathSpec x y hadj len).start = x := by
  simp [zigzagPathSpec, PathSpec.start, FinitePath.start, zigzagFinitePath, zigzagVertex]

private lemma zigzagPathSpec_staysIn {x y : Zd d} (hadj : Adj x y) (len : Nat)
    {S : Set (Zd d)} (hx : x ∈ S) (hy : y ∈ S) :
    (zigzagPathSpec x y hadj len).staysIn S := by
  intro i; exact zigzagVertex_mem hx hy i.val

private lemma zigzagPathSpec_edgeSet_subset {x y : Zd d} (hadj : Adj x y) (len : Nat) :
    (zigzagPathSpec x y hadj len).edgeSet ⊆ {(x, y), (y, x)} := by
  unfold PathSpec.edgeSet;
  unfold zigzagPathSpec; unfold zigzagFinitePath; simp +decide [ zigzagVertex ] ;
  grind

private lemma zigzag_edgeDisjoint {x y₁ y₂ : Zd d}
    (hadj₁ : Adj x y₁) (hadj₂ : Adj x y₂) (len₁ len₂ : Nat) (hy : y₁ ≠ y₂) :
    PathSpec.EdgeDisjoint (zigzagPathSpec x y₁ hadj₁ len₁) (zigzagPathSpec x y₂ hadj₂ len₂) := by
  apply Set.disjoint_of_subset_left (zigzagPathSpec_edgeSet_subset hadj₁ len₁)
  apply Set.disjoint_of_subset_right (zigzagPathSpec_edgeSet_subset hadj₂ len₂)
  rw [Set.disjoint_left]
  intro e he1 he2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he1 he2
  rcases he1 with rfl | rfl <;> rcases he2 with h | h <;>
    (try { simp [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hy rfl }) <;>
    (try { exact hy (Prod.mk.inj h).1 }) <;>
    (try { exact hy (Prod.mk.inj h).2.symm })

/-- The "up" neighbor of `x` at coordinate `i`: increases L1 norm by 1. -/
private def upNeighbor (x : Zd d) (i : Fin d) : Zd d :=
  if 0 ≤ x i then x + Zd.e i else x - Zd.e i

/-- The "down" neighbor of `x` at coordinate `i` (for zero coords): `x - e_i`. -/
private def downNeighbor (x : Zd d) (i : Fin d) : Zd d := x - Zd.e i

private lemma upNeighbor_adj (x : Zd d) (i : Fin d) : Adj x (upNeighbor x i) := by
  unfold upNeighbor; split
  · exact ⟨i, Or.inl rfl⟩
  · exact ⟨i, Or.inr rfl⟩

private lemma upNeighbor_sphere {x : Zd d} {m : Nat}
    (hx : x ∈ Zd.sphere m) (i : Fin d) :
    upNeighbor x i ∈ Zd.sphere (m + 1) := by
  change Zd.l1Norm (upNeighbor x i) = m + 1
  change Zd.l1Norm x = m at hx
  unfold Zd.l1Norm at hx ⊢
  by_cases hi : 0 ≤ x i
  · have hself : Int.natAbs (upNeighbor x i i) = Int.natAbs (x i) + 1 := by
      simpa [upNeighbor, hi, Zd.e] using
        (Int.natAbs_add_of_nonneg (a := x i) (b := 1) hi (by norm_num : (0 : Int) ≤ 1))
    have hrest :
        Finset.sum (Finset.univ.erase i) (fun j => Int.natAbs (upNeighbor x i j)) =
          Finset.sum (Finset.univ.erase i) (fun j => Int.natAbs (x j)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj' : j ≠ i := by
        exact (Finset.mem_erase.mp hj).1
      simp [upNeighbor, hi, Zd.e, hj']
    rw [← Finset.add_sum_erase Finset.univ (fun j => Int.natAbs (upNeighbor x i j))
      (Finset.mem_univ i)]
    rw [← Finset.add_sum_erase Finset.univ (fun j => Int.natAbs (x j))
      (Finset.mem_univ i)] at hx
    rw [hself, hrest]
    omega
  · have hneg : x i < 0 := lt_of_not_ge hi
    have hself : Int.natAbs (upNeighbor x i i) = Int.natAbs (x i) + 1 := by
      simpa [upNeighbor, hi, Zd.e, sub_eq_add_neg] using
        (Int.natAbs_add_of_nonpos (a := x i) (b := (-1 : Int)) (le_of_lt hneg)
          (by norm_num : (-1 : Int) ≤ 0))
    have hrest :
        Finset.sum (Finset.univ.erase i) (fun j => Int.natAbs (upNeighbor x i j)) =
          Finset.sum (Finset.univ.erase i) (fun j => Int.natAbs (x j)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj' : j ≠ i := by
        exact (Finset.mem_erase.mp hj).1
      simp [upNeighbor, hi, Zd.e, hj']
    rw [← Finset.add_sum_erase Finset.univ (fun j => Int.natAbs (upNeighbor x i j))
      (Finset.mem_univ i)]
    rw [← Finset.add_sum_erase Finset.univ (fun j => Int.natAbs (x j))
      (Finset.mem_univ i)] at hx
    rw [hself, hrest]
    omega

private lemma downNeighbor_adj (x : Zd d) (i : Fin d) : Adj x (downNeighbor x i) := by
  exact ⟨i, Or.inr rfl⟩

private lemma downNeighbor_sphere_of_zero {x : Zd d} {m : Nat}
    (hx : x ∈ Zd.sphere m) (i : Fin d) (hi : x i = 0) :
    downNeighbor x i ∈ Zd.sphere (m + 1) := by
  change Zd.l1Norm (downNeighbor x i) = m + 1
  change Zd.l1Norm x = m at hx
  unfold Zd.l1Norm at hx ⊢
  have hself : Int.natAbs (downNeighbor x i i) = 1 := by
    simp [downNeighbor, hi, Zd.e]
  have hrest :
      Finset.sum (Finset.univ.erase i) (fun j => Int.natAbs (downNeighbor x i j)) =
        Finset.sum (Finset.univ.erase i) (fun j => Int.natAbs (x j)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j ≠ i := by
      exact (Finset.mem_erase.mp hj).1
    simp [downNeighbor, Zd.e, hj']
  rw [← Finset.add_sum_erase Finset.univ (fun j => Int.natAbs (downNeighbor x i j))
    (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase Finset.univ (fun j => Int.natAbs (x j))
    (Finset.mem_univ i)] at hx
  rw [hi] at hx
  rw [hself, hrest]
  omega

private lemma upNeighbor_ne_of_ne {x : Zd d} (i j : Fin d) (hij : i ≠ j) :
    upNeighbor x i ≠ upNeighbor x j := by
  contrapose! hij; simp_all +decide [ Zd, Fin.ext_iff, funext_iff ] ;
  unfold upNeighbor at hij;
  unfold Zd.e at hij; specialize hij i; aesop;

private lemma downNeighbor_ne_of_ne {x : Zd d} (i j : Fin d) (hij : i ≠ j) :
    downNeighbor x i ≠ downNeighbor x j := by
  contrapose! hij with h;
  unfold downNeighbor at h;
  replace h := congr_fun h i; simp_all +decide [ sub_eq_add_neg, Zd.e ] ;

private lemma upNeighbor_ne_downNeighbor {x : Zd d} (i j : Fin d) (hi : x i = 0) :
    upNeighbor x i ≠ downNeighbor x j := by
  unfold upNeighbor downNeighbor;
  simp +decide [ funext_iff, hi ];
  use i;
  by_cases hij : i = j <;> simp_all +decide [ Zd.e ]

/-- Neighbor of `xnp1` on sphere `n`, for coordinate `j` with `xnp1 j ≠ 0`. -/
private def outerNeighbor (x : Zd d) (j : Fin d) : Zd d :=
  if 0 < x j then x - Zd.e j else x + Zd.e j

private lemma outerNeighbor_adj (x : Zd d) (j : Fin d) : Adj x (outerNeighbor x j) := by
  unfold outerNeighbor; split
  · exact ⟨j, Or.inr rfl⟩
  · exact ⟨j, Or.inl rfl⟩

private lemma outerNeighbor_sphere {x : Zd d} {m : Nat}
    (hx : x ∈ Zd.sphere (m + 1)) (j : Fin d) (hj : x j ≠ 0) :
    outerNeighbor x j ∈ Zd.sphere m := by
  unfold outerNeighbor;
  split_ifs <;> simp_all +decide [ Zd.sphere ];
  · unfold Zd.l1Norm at *;
    simp_all +decide [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ), Zd.e ];
    rw [ Finset.sum_congr rfl fun i hi => by aesop ] ; omega;
  · simp_all +decide [ Zd.l1Norm ];
    rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ) ] at *;
    rw [ Finset.sum_congr rfl fun i hi => by rw [ show Zd.e j i = 0 by exact if_neg ( by aesop ) ] ] ; norm_num [ Zd.e ] ; omega;

private lemma outerNeighbor_ne_of_ne {x : Zd d} (i j : Fin d)
    (hij : i ≠ j) (hi : x i ≠ 0) (hj : x j ≠ 0) :
    outerNeighbor x i ≠ outerNeighbor x j := by
  intro h_eq;
  unfold outerNeighbor at h_eq;
  split_ifs at h_eq <;> have := congr_fun h_eq i <;> simp_all +decide;
  · replace h_eq := congr_fun h_eq j ; simp_all +decide [ Zd.e ];
  · exact hij ( by simpa [ Zd.e ] using congr_fun h_eq.symm i )

/-- Cross edge-disjointness: inner zigzag on {xn, y} and outer zigzag on {xnp1, z}
    are edge-disjoint when y ≠ xnp1 (since xn ≠ xnp1). -/
private lemma cross_zigzag_edgeDisjoint {xn xnp1 y z : Zd d}
    (hxn_ne : xn ≠ xnp1) (hy_ne : y ≠ xnp1) (hz_ne : z ≠ xn)
    (hadj1 : Adj xn y) (hadj2 : Adj xnp1 z) (len₁ len₂ : Nat) :
    PathSpec.EdgeDisjoint (zigzagPathSpec xn y hadj1 len₁)
      (zigzagPathSpec xnp1 z hadj2 len₂) := by
  apply Set.disjoint_of_subset_left (zigzagPathSpec_edgeSet_subset hadj1 len₁)
  apply Set.disjoint_of_subset_right (zigzagPathSpec_edgeSet_subset hadj2 len₂)
  rw [Set.disjoint_left]
  intro e he1 he2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he1 he2
  rcases he1 with rfl | rfl <;> rcases he2 with h | h <;>
    simp [Prod.mk.injEq] at h <;>
    first
    | exact hxn_ne h.1
    | exact hy_ne h.1
    | exact hz_ne h.1.symm
    | (obtain ⟨rfl, rfl⟩ := h; exact hz_ne rfl)
    | exact hxn_ne h.2

/-- Points on different spheres are distinct. -/
private lemma sphere_ne {m₁ m₂ : Nat} {x y : Zd d}
    (hx : x ∈ Zd.sphere m₁) (hy : y ∈ Zd.sphere m₂) (hm : m₁ ≠ m₂) :
    x ≠ y := by
  intro heq; rw [heq] at hx; simp [Zd.sphere] at hx hy; omega

-- ============================================================
-- Section 5.8: Spreading path construction for nonneg δ
-- ============================================================

/-- Vertex of a spreading path: starting at `x`, the path alternates between
    moving in direction `d1` (on even→odd steps) and direction `d2` (on odd→even steps).
    After `k` steps, the vertex is `x + ⌈k/2⌉ * d1 + ⌊k/2⌋ * d2`. -/
private def spreadVertex (x d1 d2 : Zd d) (k : Nat) : Zd d :=
  fun j => x j + (↑((k + 1) / 2) : ℤ) * d1 j + (↑(k / 2) : ℤ) * d2 j

private lemma spreadVertex_zero (x d1 d2 : Zd d) : spreadVertex x d1 d2 0 = x := by
  ext j; simp [spreadVertex]

/-
The step from position k to k+1 adds d1 (if k is even) or d2 (if k is odd).
-/
private lemma spreadVertex_step (x d1 d2 : Zd d) (k : Nat) :
    spreadVertex x d1 d2 (k + 1) =
      if k % 2 = 0 then spreadVertex x d1 d2 k + d1
      else spreadVertex x d1 d2 k + d2 := by
  unfold spreadVertex;
  cases Nat.mod_two_eq_zero_or_one k <;> simp +decide [ *, Nat.add_div ];
  · ext j; norm_num [ Nat.add_mod, ‹k % 2 = 0› ] ; ring;
  · ext j; simp +decide [ *, Nat.add_mod ] ; ring

private lemma spreadVertex_adj (x : Zd d) {d1 d2 : Zd d}
    (h1 : ∃ i : Fin d, d1 = Zd.e i ∨ d1 = -Zd.e i)
    (h2 : ∃ i : Fin d, d2 = Zd.e i ∨ d2 = -Zd.e i)
    (k : Nat) :
    Adj (spreadVertex x d1 d2 k) (spreadVertex x d1 d2 (k + 1)) := by
  rw [ spreadVertex_step ];
  unfold Adj; aesop;

/-- A finite path that spreads in directions d1, d2 alternately. -/
private def spreadFinitePath (x : Zd d) {d1 d2 : Zd d}
    (h1 : ∃ i : Fin d, d1 = Zd.e i ∨ d1 = -Zd.e i)
    (h2 : ∃ i : Fin d, d2 = Zd.e i ∨ d2 = -Zd.e i)
    (len : Nat) : FinitePath d len where
  toVertex k := spreadVertex x d1 d2 k.val
  adjacent' k := by
    show Adj (spreadVertex x d1 d2 k.castSucc.val) (spreadVertex x d1 d2 k.succ.val)
    rw [Fin.val_castSucc, Fin.val_succ]
    exact spreadVertex_adj x h1 h2 k.val

/-- A `PathSpec` wrapping a spreading path. -/
private def spreadPathSpec (x : Zd d) {d1 d2 : Zd d}
    (h1 : ∃ i : Fin d, d1 = Zd.e i ∨ d1 = -Zd.e i)
    (h2 : ∃ i : Fin d, d2 = Zd.e i ∨ d2 = -Zd.e i)
    (len : Nat) : PathSpec d :=
  ⟨len, spreadFinitePath x h1 h2 len⟩

private lemma spreadPathSpec_start (x : Zd d) {d1 d2 : Zd d}
    (h1 : ∃ i : Fin d, d1 = Zd.e i ∨ d1 = -Zd.e i)
    (h2 : ∃ i : Fin d, d2 = Zd.e i ∨ d2 = -Zd.e i)
    (len : Nat) :
    (spreadPathSpec x h1 h2 len).start = x := by
  simp [spreadPathSpec, PathSpec.start, FinitePath.start, spreadFinitePath]
  ext j; simp [spreadVertex]

/-
The l1norm of x + m * e_i + m' * d2 when x is nonneg, i ≠ p, d2 = -e_p,
    and the reservoir coordinate has enough room.
-/
private lemma spreadVertex_l1norm_inner {x : Zd d} {i p : Fin d}
    (hip : i ≠ p) (hnonneg : Nonnegative x) (hx : x ∈ Zd.sphere n)
    {k : Nat} (hk : k / 2 ≤ Int.natAbs (x p)) :
    Zd.l1Norm (spreadVertex x (Zd.e i) (-Zd.e p) k) ∈
      ({n, n + 1} : Set Nat) := by
  have h_l1_norm : (spreadVertex x (Zd.e i) (-Zd.e p) k).l1Norm = n + (if k % 2 = 1 then 1 else 0) := by
    have h_sum : ∑ j, (spreadVertex x (Zd.e i) (-Zd.e p) k j).natAbs = ∑ j, (x j).natAbs + (if k % 2 = 1 then 1 else 0) := by
      have h_sum : ∑ j, (spreadVertex x (Zd.e i) (-Zd.e p) k j).natAbs = ∑ j ∈ Finset.univ \ {i, p}, (x j).natAbs + (x i + (k + 1) / 2).natAbs + (x p - k / 2).natAbs := by
        have h_sum : ∑ j, (spreadVertex x (Zd.e i) (-Zd.e p) k j).natAbs = ∑ j ∈ Finset.univ \ {i, p}, (x j).natAbs + ∑ j ∈ {i, p}, (spreadVertex x (Zd.e i) (-Zd.e p) k j).natAbs := by
          have h_sum : ∀ j ∈ Finset.univ \ {i, p}, (spreadVertex x (Zd.e i) (-Zd.e p) k j).natAbs = (x j).natAbs := by
            unfold spreadVertex; aesop;
          rw [ ← Finset.sum_sdiff ( Finset.subset_univ { i, p } ), Finset.sum_congr rfl h_sum ];
        simp_all +decide [ Finset.sum_pair, spreadVertex ];
        simp +decide [ Zd.e, hip, add_assoc ];
        rw [ if_neg ( Ne.symm hip ) ] ; ring;
      split_ifs <;> simp_all +decide [ Finset.sum_add_distrib ];
      · rw [ ← Finset.sum_sdiff ( Finset.subset_univ { i, p } ) ];
        rw [ Finset.sum_pair hip ];
        rw [ ← Int.natAbs_of_nonneg ( hnonneg i ), ← Int.natAbs_of_nonneg ( hnonneg p ) ];
        omega;
      · rw [ ← Finset.sum_sdiff ( Finset.subset_univ { i, p } ) ];
        rw [ Finset.sum_pair hip ];
        rw [ ← Int.natAbs_of_nonneg ( hnonneg i ), ← Int.natAbs_of_nonneg ( hnonneg p ) ];
        omega
    unfold Zd.l1Norm at *; aesop;
  split_ifs at h_l1_norm <;> simp +decide [ h_l1_norm ]

/-
Spreading paths with d1 = e_i, d2 = -e_p stay on shellUnion n
    when starting from sphere n with sufficient reservoir.
-/
private lemma spreadPathSpec_staysIn_inner {x : Zd d} {i p : Fin d}
    (hip : i ≠ p) (hnonneg : Nonnegative x) (hx : x ∈ Zd.sphere n)
    (hreservoir : len / 2 ≤ Int.natAbs (x p))
    (h1 : ∃ i' : Fin d, (Zd.e i : Zd d) = Zd.e i' ∨ (Zd.e i : Zd d) = -Zd.e i')
    (h2 : ∃ i' : Fin d, (-Zd.e p : Zd d) = Zd.e i' ∨ (-Zd.e p : Zd d) = -Zd.e i') :
    (spreadPathSpec x h1 h2 len).staysIn (shellUnion (d := d) n) := by
  intro i
  simp [shellUnion];
  convert spreadVertex_l1norm_inner hip hnonneg hx _;
  exact le_trans ( Nat.div_le_div_right ( Nat.le_of_lt_succ i.2 ) ) hreservoir

/-
The finish of an inner spreading path.
-/
private lemma spreadPathSpec_finish_inner {x : Zd d} {i p : Fin d} (hip : i ≠ p)
    {len : Nat}
    (h1 : ∃ i' : Fin d, (Zd.e i : Zd d) = Zd.e i' ∨ (Zd.e i : Zd d) = -Zd.e i')
    (h2 : ∃ i' : Fin d, (-Zd.e p : Zd d) = Zd.e i' ∨ (-Zd.e p : Zd d) = -Zd.e i') :
    (spreadPathSpec x h1 h2 len).finish i = x i + ↑((len + 1) / 2) := by
  unfold spreadPathSpec; simp +decide [ spreadFinitePath, spreadVertex ] ;
  unfold spreadVertex; simp +decide [ hip, Fin.ext_iff ] ;
  unfold PathSpec.finish; aesop;

/-
The i-th coordinate is unchanged on a spreading path whose active coordinate is j ≠ i
    and whose reservoir is p ≠ i.
-/
private lemma spreadVertex_coord_unchanged {x : Zd d} {act res : Fin d} {coord : Fin d}
    (hact : coord ≠ act) (hres : coord ≠ res) (k : Nat) :
    spreadVertex x (Zd.e act) (-Zd.e res) k coord = x coord := by
  -- By definition of spreadVertex, we have:
  simp [spreadVertex, Zd.e];
  aesop

/-
Endpoint separation between spreading paths with different active coordinates:
    If gamma uses active coordinate i₁ and gamma' uses active coordinate i₂ ≠ i₁,
    and both use reservoir p with p ≠ i₁ and p ≠ i₂, then every vertex of gamma'
    has i₁-coordinate equal to x(i₁), while gamma's endpoint has i₁-coordinate
    x(i₁) + (len+1)/2.
-/
private lemma spread_endpoint_separation {x : Zd d} {i₁ i₂ p : Fin d}
    (hi : i₁ ≠ i₂) (hp₁ : i₁ ≠ p) (hp₂ : i₂ ≠ p)
    {len : Nat} (hlen : 2 * (endpointSeparationRadius δ n).toNNReal ≤ len)
    (h1₁ : ∃ i' : Fin d, (Zd.e i₁ : Zd d) = Zd.e i' ∨ (Zd.e i₁ : Zd d) = -Zd.e i')
    (h2 : ∃ i' : Fin d, (-Zd.e p : Zd d) = Zd.e i' ∨ (-Zd.e p : Zd d) = -Zd.e i')
    (h1₂ : ∃ i' : Fin d, (Zd.e i₂ : Zd d) = Zd.e i' ∨ (Zd.e i₂ : Zd d) = -Zd.e i') :
    PathSpec.EndpointFarFrom (endpointSeparationRadius δ n)
      (spreadPathSpec x h1₁ h2 len) (spreadPathSpec x h1₂ h2 len) := by
  intro z hz;
  -- Apply the distance inequality to the i₁-coordinate.
  have h_dist_i₁ : |(spreadPathSpec x h1₁ h2 len).finish i₁ - z i₁| ≥ endpointSeparationRadius δ n := by
    -- By definition of `spreadPathSpec`, we know that `z i₁ = x i₁`.
    have hz_i₁ : z i₁ = x i₁ := by
      obtain ⟨ k, hk ⟩ := hz;
      rw [ ← hk ] ; apply spreadVertex_coord_unchanged; tauto; tauto;
    -- By definition of `spreadPathSpec`, we know that `(spreadPathSpec x h1₁ h2 len).finish i₁ = x i₁ + (len + 1) / 2`.
    have h_finish_i₁ : (spreadPathSpec x h1₁ h2 len).finish i₁ = x i₁ + (len + 1) / 2 := by
      convert spreadPathSpec_finish_inner hp₁ h1₁ h2 using 1;
    rw [ ← NNReal.coe_le_coe ] at * ; norm_num at *;
    rw [ h_finish_i₁, hz_i₁ ] ; norm_num [ abs_of_nonneg ];
    rw [ abs_of_nonneg ( by positivity ) ] ; norm_cast ; norm_num [ Nat.add_div ];
    split_ifs <;> norm_num at *;
    · cases max_cases ( endpointSeparationRadius δ n ) 0 <;> linarith [ show ( len : ℝ ) ≤ 2 * ( len / 2 : ℕ ) + 1 by norm_cast; linarith [ Nat.div_add_mod len 2, Nat.mod_lt len two_pos ] ];
    · cases max_cases ( endpointSeparationRadius δ n ) 0 <;> linarith [ show ( len : ℝ ) = 2 * ( len / 2 : ℕ ) by norm_cast; linarith [ Nat.mod_add_div len 2, show len % 2 = 0 from by omega ] ];
  refine' le_trans h_dist_i₁ _;
  convert dist_le_pi_dist ( spreadPathSpec x h1₁ h2 len |>.finish ) z i₁ using 1;
  unfold dist; aesop;

/-
Edge disjointness between spreading paths with different active coordinates
    and the same reservoir.
-/
private lemma spread_edgeDisjoint {x : Zd d} {i₁ i₂ p : Fin d}
    (hi : i₁ ≠ i₂) (hp₁ : i₁ ≠ p) (hp₂ : i₂ ≠ p)
    {len₁ len₂ : Nat}
    (h1₁ : ∃ i' : Fin d, (Zd.e i₁ : Zd d) = Zd.e i' ∨ (Zd.e i₁ : Zd d) = -Zd.e i')
    (h1₂ : ∃ i' : Fin d, (Zd.e i₂ : Zd d) = Zd.e i' ∨ (Zd.e i₂ : Zd d) = -Zd.e i')
    (h2 : ∃ i' : Fin d, (-Zd.e p : Zd d) = Zd.e i' ∨ (-Zd.e p : Zd d) = -Zd.e i') :
    PathSpec.EdgeDisjoint
      (spreadPathSpec x h1₁ h2 len₁) (spreadPathSpec x h1₂ h2 len₂) := by
  unfold PathSpec.EdgeDisjoint; simp +decide [ spreadPathSpec ] ;
  simp +decide [ Set.disjoint_left, spreadFinitePath ];
  intro a b ha hb;
  simp +decide [ PathSpec.edgeSet ] at ha hb;
  rcases ha with ⟨ i, hi | hi ⟩ <;> rcases hb with ⟨ j, hj | hj ⟩ <;> simp_all +decide only [spreadVertex];
  · unfold spreadVertex at *;
    have := congr_fun hi.1 i₁; have := congr_fun hi.2 i₁; simp_all +decide [ Zd.e ] ;
    omega;
  · unfold spreadVertex at *;
    have := congr_fun hi.1 i₁; have := congr_fun hi.2 i₁; simp_all +decide [ Zd.e ] ;
    omega;
  · have := congr_fun hi.1 i₁; have := congr_fun hi.2 i₁; simp_all +decide [ spreadVertex ] ;
    omega;
  · unfold spreadVertex at hi;
    have := congr_fun hi.1 i₁; have := congr_fun hi.1 i₂; have := congr_fun hi.1 p; simp_all +decide [ Zd.e ] ;
    omega

-- ============================================================
-- End of spreading path infrastructure
-- ============================================================

/-
The number of available inner neighbors (up + down for zero coords)
    is at least requiredInnerPathCount + 1.
-/
private lemma innerNeighborCount_sufficient {xn : Zd d} {n : Nat}
    (hd : 3 ≤ d) (hxn : xn ∈ Zd.sphere n) :
    requiredInnerPathCount (d := d) n xn + 1 ≤
      d + (Finset.univ.filter (fun i : Fin d => xn i = 0)).card := by
  unfold requiredInnerPathCount;
  split_ifs;
  · -- If xn is a signed axis point, then its nonzero coordinates are at most 1.
    have h_card_nonzero : (Zd.nonzeroCoords xn).card ≤ 1 := by
      obtain ⟨ i, hi ⟩ | ⟨ i, hi ⟩ := ‹IsSignedAxisPoint n xn› <;> simp_all +decide [ Zd.nonzeroCoords, IsAxisPoint ];
      · exact Finset.card_le_one.mpr fun x hx y hy => by unfold axisPoint at *; aesop;
      · exact Finset.card_le_one.mpr fun x hx y hy => by unfold axisPoint at *; aesop;
    rw [ show ( Finset.univ.filter fun i => xn i = 0 ) = Finset.univ \ Zd.nonzeroCoords xn from by ext; aesop ] ; simp +arith +decide [ Finset.card_sdiff, * ];
    omega;
  · rw [ show ( Finset.univ.filter fun i => xn i = 0 ) = Finset.univ \ xn.nonzeroCoords from ?_, Finset.card_sdiff ] <;> norm_num;
    · omega;
    · ext i; simp [Zd.nonzeroCoords]

/-
The number of available outer neighbors (nonzero coords)
    is at least requiredOuterPathCount.
-/
private lemma outerNeighborCount_sufficient {xnp1 : Zd d} {n : Nat}
    (hd : 3 ≤ d) (hxnp1 : xnp1 ∈ Zd.sphere (n + 1)) :
    requiredOuterPathCount (d := d) n xnp1 ≤
      (Finset.univ.filter (fun j : Fin d => xnp1 j ≠ 0)).card := by
  unfold requiredOuterPathCount;
  split_ifs;
  · by_contra h_empty;
    simp_all +decide [ Zd.l1Norm, Zd.sphere ];
  · exact Nat.sub_le _ _

/-
Cross edge-disjointness only needs xn ≠ xnp1 and y ≠ xnp1.
-/
private lemma cross_zigzag_edgeDisjoint' {xn xnp1 y z : Zd d}
    (hxn_ne : xn ≠ xnp1) (hy_ne : y ≠ xnp1)
    (hadj1 : Adj xn y) (hadj2 : Adj xnp1 z) (len₁ len₂ : Nat) :
    PathSpec.EdgeDisjoint (zigzagPathSpec xn y hadj1 len₁)
      (zigzagPathSpec xnp1 z hadj2 len₂) := by
  unfold PathSpec.EdgeDisjoint;
  rw [ Set.disjoint_left ];
  simp +decide [PathSpec.edgeSet, zigzagPathSpec];
  unfold zigzagFinitePath; simp +decide [ zigzagVertex ] ;
  grind

/-
There exist enough distinct neighbors of xn on sphere(n+1), all different from xnp1.
-/
private lemma inner_neighbors_exist {xn xnp1 : Zd d} {n : Nat}
    (hd : 3 ≤ d) (hxn : xn ∈ Zd.sphere n) (hxnp1 : xnp1 ∈ Zd.sphere (n + 1)) :
    ∃ (nbrs : Fin (requiredInnerPathCount (d := d) n xn) → Zd d),
      (Function.Injective nbrs) ∧
      (∀ i, Adj xn (nbrs i)) ∧
      (∀ i, nbrs i ∈ Zd.sphere (n + 1)) ∧
      (∀ i, nbrs i ≠ xnp1) := by
  -- Define the candidate set of neighbors.
  set candidateNbrs : Finset (Zd d) := Finset.image (fun i : Fin d => upNeighbor xn i) Finset.univ ∪ Finset.image (fun i : Fin d => downNeighbor xn i) (Finset.univ.filter (fun i : Fin d => xn i = 0)) with hc;
  -- By innerNeighborCount_sufficient, after removing xnp1 (at most 1 element), we have ≥ requiredInnerPathCount elements.
  have h_card : candidateNbrs.card ≥ requiredInnerPathCount n xn + 1 := by
    rw [ Finset.card_union_of_disjoint ];
    · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ];
      · have := innerNeighborCount_sufficient hd hxn; aesop;
      · intro i j hij; simp_all +decide [ funext_iff, Fin.ext_iff, downNeighbor ] ;
        specialize hij i ; simp_all +decide [ Zd.e ];
      · intro i j hij;
        contrapose! hij;
        exact upNeighbor_ne_of_ne (x := xn) i j hij;
    · rw [ Finset.disjoint_left ];
      simp +decide [ upNeighbor, downNeighbor ] at *;
      intro a x hx; split_ifs <;> intro H <;> have := congr_fun H x <;> simp_all +decide [ Zd.e ] ;
      · split_ifs at this;
      · replace H := congr_fun H a ; simp_all +decide [ Zd.e ];
  -- Let's choose any subset of candidateNbrs with cardinality requiredInnerPathCount n xn.
  obtain ⟨subsetNbrs, hsubsetNbrs⟩ : ∃ subsetNbrs : Finset (Zd d), subsetNbrs ⊆ candidateNbrs ∧ subsetNbrs.card = requiredInnerPathCount n xn ∧ xnp1 ∉ subsetNbrs := by
    by_cases h : xnp1 ∈ candidateNbrs;
    · have := Finset.exists_subset_card_eq ( show requiredInnerPathCount n xn ≤ ( candidateNbrs.erase xnp1 ).card from by rw [ Finset.card_erase_of_mem h ] ; omega );
      exact ⟨ this.choose, Finset.Subset.trans this.choose_spec.1 ( Finset.erase_subset _ _ ), this.choose_spec.2, fun hx => Finset.notMem_erase _ _ ( this.choose_spec.1 hx ) ⟩;
    · exact Exists.elim ( Finset.exists_subset_card_eq ( by linarith : requiredInnerPathCount n xn ≤ candidateNbrs.card ) ) fun s hs => ⟨ s, hs.1, hs.2, fun hs' => h <| hs.1 hs' ⟩;
  obtain ⟨nbrs, hn⟩ : ∃ nbrs : Fin (requiredInnerPathCount n xn) → Zd d, Function.Injective nbrs ∧ ∀ i, nbrs i ∈ subsetNbrs := by
    have := Finset.equivFinOfCardEq hsubsetNbrs.2.1;
    exact ⟨ _, Subtype.val_injective.comp this.symm.injective, fun i => this.symm i |>.2 ⟩;
  refine' ⟨ nbrs, hn.1, _, _, _ ⟩ <;> intro i <;> have := hn.2 i <;> simp_all +decide [ Finset.subset_iff ];
  · rcases hsubsetNbrs.1 ( hn.2 i ) with ( ⟨ a, ha ⟩ | ⟨ a, ha, ha' ⟩ ) <;> simp_all +decide [ upNeighbor, downNeighbor ];
    · split_ifs at ha <;> simp_all +decide [ Adj ];
      · exact ⟨ a, Or.inl ha.symm ⟩;
      · exact ⟨ a, Or.inr ha.symm ⟩;
    · exact ha'.symm ▸ downNeighbor_adj _ _;
  · rcases hsubsetNbrs.1 ( hn.2 i ) with ( ⟨ a, ha ⟩ | ⟨ a, ha, ha' ⟩ ) <;> simp_all +decide [ Zd.sphere ];
    · rw [ ← ha ] ; exact upNeighbor_sphere ( show xn ∈ Zd.sphere n from by simpa [ Zd.sphere ] using hxn ) a;
    · rw [ ← ha', downNeighbor_sphere_of_zero ] <;> aesop;
  · exact fun h => hsubsetNbrs.2.2 <| h ▸ hn.2 i

/-
There exist enough distinct neighbors of xnp1 on sphere(n).
-/
private lemma outer_neighbors_exist {xnp1 : Zd d} {n : Nat}
    (hd : 3 ≤ d) (hxnp1 : xnp1 ∈ Zd.sphere (n + 1)) :
    ∃ (nbrs : Fin (requiredOuterPathCount (d := d) n xnp1) → Zd d),
      (Function.Injective nbrs) ∧
      (∀ i, Adj xnp1 (nbrs i)) ∧
      (∀ i, nbrs i ∈ Zd.sphere n) := by
  -- Let's choose any $k$ distinct nonzero coordinates of $xnp1$.
  obtain ⟨ks, hks⟩ : ∃ ks : Fin (requiredOuterPathCount (d := d) n xnp1) → Fin d, Function.Injective ks ∧ ∀ i, xnp1 (ks i) ≠ 0 := by
    have h_outer_neighbor_count : requiredOuterPathCount (d := d) n xnp1 ≤ (Finset.univ.filter (fun j : Fin d => xnp1 j ≠ 0)).card := by
      exact outerNeighborCount_sufficient (d := d) (xnp1 := xnp1) hd hxnp1;
    have := Finset.exists_subset_card_eq h_outer_neighbor_count;
    cases' this with t ht;
    exact ⟨ fun i => t.orderEmbOfFin ( by aesop ) i, by aesop_cat, fun i => by simpa using ht.1 ( by aesop ) ⟩;
  refine' ⟨ fun i => outerNeighbor xnp1 ( ks i ), _, _, _ ⟩ <;> simp_all +decide [ Function.Injective ];
  · intro i j hij;
    have := hks.1 ( show ks i = ks j from ?_ ) ; aesop;
    exact Classical.not_not.1 fun hi => outerNeighbor_ne_of_ne _ _ hi ( hks.2 i ) ( hks.2 j ) hij;
  · exact fun i => outerNeighbor_adj xnp1 (ks i);
  · exact fun i => outerNeighbor_sphere hxnp1 ( ks i ) ( hks.2 i )

/-
Handle the degenerate case δ < 0.
-/
lemma main_theorem_neg_delta
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d}
    (hd : 3 ≤ d)
    (hδ_neg : δ < 0)
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  -- Set L = Nat.floor(δ²*(n+1)).
  set L := Nat.floor (δ ^ 2 * (n + 1)) with hL_def;
  -- Use inner_neighbors_exist and outer_neighbors_exist to get neighbor functions.
  obtain ⟨in_nbrs, in_inj, in_adj, in_sphere, in_ne⟩ := inner_neighbors_exist hd hxn hxnp1
  obtain ⟨out_nbrs, out_inj, out_adj, out_sphere⟩ := outer_neighbors_exist hd hxnp1;
  constructor;
  constructor;
  rotate_left;
  rotate_left;
  rotate_left;
  rotate_left;
  rotate_left;
  rotate_left;
  exact ⟨ List.ofFn fun i => zigzagPathSpec xn ( in_nbrs i ) ( in_adj i ) L, by
    simp +decide [ List.mem_ofFn, zigzagPathSpec_start ], by
    aesop, by
    simp +zetaDelta at *;
    intro i; exact Nat.floor_mono <| by nlinarith [ show ( d : ℝ ) ≥ 3 by norm_cast, show ( δ ^ 2 : ℝ ) * ( n + 1 ) ≥ 0 by positivity ] ;, by
    simp +decide [ List.mem_ofFn ];
    intro i; exact zigzagPathSpec_staysIn (in_adj i) L (by
    exact Set.mem_union_left _ hxn) (by
    exact Or.inr ( in_sphere i )), by
    rw [ List.pairwise_ofFn ];
    exact fun i j hij => zigzag_edgeDisjoint _ _ _ _ ( in_inj.ne hij.ne ) ⟩
  all_goals generalize_proofs at *;
  exact ⟨ List.ofFn fun i => zigzagPathSpec xnp1 ( out_nbrs i ) ( out_adj i ) L, by
    simp +decide [ List.mem_ofFn, zigzagPathSpec_start ], by
    aesop, by
    simp +zetaDelta at *;
    intro i; exact Nat.floor_mono <| by nlinarith [ show ( d : ℝ ) ≥ 3 by norm_cast, show ( δ ^ 2 : ℝ ) * ( n + 1 ) ≥ 0 by positivity ] ;, by
    simp +decide [ List.mem_ofFn, PathSpec.staysIn ];
    intro i; exact zigzagPathSpec_staysIn ( out_adj i ) L ( by
      exact Or.inr hxnp1 ) ( by
      exact Set.mem_union_left _ ( out_sphere i ) ) ;, by
    rw [ List.pairwise_ofFn ];
    exact fun i j hij => zigzag_edgeDisjoint _ _ _ _ ( out_inj.ne hij.ne ) ⟩
  all_goals generalize_proofs at *;
  all_goals norm_num [ List.length_ofFn ] at *;
  · intro i j; exact cross_zigzag_edgeDisjoint' (by
    exact sphere_ne hxn hxnp1 ( by linarith )) (by
    exact in_ne i) (in_adj i) (out_adj j) L L;
  · unfold PathSpec.EndpointFarFrom; norm_num [ endpointSeparationRadius ] ;
    intro i j hij; constructor <;> intro z hz <;> nlinarith [ show ( δ ^ 3 : ℝ ) * ( n + 1 ) ≤ 0 by exact mul_nonpos_of_nonpos_of_nonneg ( by nlinarith [ sq_pos_of_neg hδ_neg ] ) ( by positivity ), show ( dist ( zigzagPathSpec xn ( in_nbrs i ) ( in_adj i ) L ).finish z : ℝ ) ≥ 0 by positivity, show ( dist ( zigzagPathSpec xn ( in_nbrs j ) ( in_adj j ) L ).finish z : ℝ ) ≥ 0 by positivity ] ;
  · unfold PathSpec.EndpointFarFrom; norm_num [ endpointSeparationRadius ] ;
    intro i j hij; constructor <;> intros z hz <;> nlinarith [ show δ ^ 3 * ( n + 1 ) ≤ 0 by exact mul_nonpos_of_nonpos_of_nonneg ( by nlinarith [ sq_nonneg δ ] ) ( by positivity ), show 0 ≤ dist ( zigzagPathSpec xnp1 ( out_nbrs i ) ( out_adj i ) ⌊δ ^ 2 * ( n + 1 ) ⌋₊ ).finish z by positivity, show 0 ≤ dist ( zigzagPathSpec xnp1 ( out_nbrs j ) ( out_adj j ) ⌊δ ^ 2 * ( n + 1 ) ⌋₊ ).finish z by positivity ] ;
  · unfold PathSpec.EndpointFarFrom; norm_num [ endpointSeparationRadius ] ;
    intro i j; constructor <;> intro z hz <;> nlinarith [ show δ ^ 3 * ( n + 1 ) ≤ 0 by exact mul_nonpos_of_nonpos_of_nonneg ( by nlinarith [ sq_pos_of_neg hδ_neg ] ) ( by positivity ), show 0 ≤ dist ( zigzagPathSpec xn ( in_nbrs i ) ( in_adj i ) L ).finish z by positivity, show 0 ≤ dist ( zigzagPathSpec xnp1 ( out_nbrs j ) ( out_adj j ) L ).finish z by positivity ] ;

-- ============================================================
-- Section 6: Main assembly
-- ============================================================

/-
Main theorem matching Theorem `lem:2d-2` from `blueprint_disjoint.txt`,
with the blueprint's explicit large-`n` hypothesis packaged as
`SufficientlyLargeN n δ`.
-/

theorem main_theorem
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d}
    (hd : 3 ≤ d)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1 := by
  by_cases hδ_nonneg : 0 ≤ δ
  · by_cases horth : DifferentOrthants xn xnp1
    · exact exists_disjoint_paths_case1 hd hδ_nonneg hδ hlarge hxn hxnp1 horth
    · obtain ⟨s, hs, hs_xn, hs_xnp1⟩ := same_orthant_nonneg_signFlip horth
      exact hasDesiredDisjointPaths_signFlip hs
        (main_theorem_nonneg hd hδ_nonneg hδ hlarge
          (signFlip_mem_sphere hs hxn) (signFlip_mem_sphere hs hxnp1) hs_xn hs_xnp1)
  · exact main_theorem_neg_delta hd (lt_of_not_ge hδ_nonneg) hlarge hxn hxnp1
end DisjointPaths