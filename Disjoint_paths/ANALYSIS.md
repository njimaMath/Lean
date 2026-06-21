# Analysis of `disjoint.lean` Sorry'd Lemmas

## Summary

The file `disjoint.lean` contains 11 `sorry`'d lemmas (intermediate cases 1-6 for the main
theorem about disjoint lattice paths). After careful analysis:

- **9 out of 11 lemmas are provably false** as stated
- **2 out of 11 lemmas** (`exists_disjoint_paths_case1_small_coordinate` and
  `exists_disjoint_paths_case2_small_j_coordinate`) **appear to be true** but require
  constructing sophisticated "staircase" paths that don't exist in the current codebase
- Consequently, **`main_theorem` is false** as stated

## Build Error Fixed

Line 76 had a type mismatch: `loopless := adj_irrefl` was changed to `loopless := ⟨adj_irrefl⟩`
to match the `Std.Irrefl` structure type expected by `SimpleGraph`.

## The Core Issue

The `DisjointPathConfiguration` structure requires:
- Path lengths bounded by `⌊δ²(n+1)⌋ ≤ len ≤ ⌊2d·δ²(n+1)⌋`
- Pairwise endpoint separation: `dist(finish, z) ≥ δ³(n+1)` for all vertices z

**When `⌊2d·δ²(n+1)⌋ = 0`** (small n relative to `1/(dδ²)`), all paths are forced to have
length 0. Length-0 paths from the same starting point are identical (they're just a single vertex),
so pairwise endpoint separation requires `dist(x, x) ≥ δ³(n+1)`, i.e., `0 ≥ δ³(n+1)`, which
is impossible for δ > 0.

## Detailed Case Analysis

### FALSE Lemmas (9 of 11)

The following lemmas have no hypothesis preventing `δ²(n+1)` from being arbitrarily small
while still requiring 2+ paths (which forces endpoint separation to fail):

1. **`exists_disjoint_paths_case1_large_coordinate`** — `hr_large` does not ensure δ²(n+1) ≥ 1/(2d)
   - Counterexample: d=3, δ=0.001, n=999, xn=(999,0,0), xnp1=(-1,500,500), r=0
2. **`exists_disjoint_paths_case2_large_j_coordinate`** — `hj_large` allows δ²(n+1) < 1/(2d)
   - Counterexample: d=3, δ=0.001, n=2, xn=(1,1,0), xnp1=(3,0,0), j=0
3. **`exists_disjoint_paths_case3_core`** — No constraint on δ²(n+1)
4. **`exists_disjoint_paths_case3`** — No constraint on δ²(n+1)
5. **`exists_disjoint_paths_case4_distinct_axes`** — No constraint on δ²(n+1)
   - Counterexample: d=3, δ=1/24, n=0, xn=0, xnp1=e₁, i=0, j=1
6. **`exists_disjoint_paths_case4_same_axis`** — No constraint on δ²(n+1)
   - Counterexample: d=3, δ=1/24, n=0, xn=0, xnp1=e₀, i=j=0
7. **`exists_disjoint_paths_case5_positive_neighbor_coordinate`** — No constraint on δ²(n+1)
   - Counterexample: d=3, δ=0.001, n=2, xn=(1,1,0), xnp1=(2,1,0), j=0
8. **`exists_disjoint_paths_case5`** (sorry at line 1161) — Inherits the issue
9. **`exists_disjoint_paths_case6`** — No constraint on δ²(n+1)

### POSSIBLY TRUE Lemmas (2 of 11)

These lemmas have hypotheses that force δ²(n+1) > 1/3 or > 1, ensuring paths can have
positive length:

1. **`exists_disjoint_paths_case1_small_coordinate`** — `hr_small` gives `3δ²(n+1) > xn r ≥ 1`,
   so `δ²(n+1) > 1/3`. Path length ≥ 1 is guaranteed.
2. **`exists_disjoint_paths_case2_small_j_coordinate`** — `hj_small` gives `δ²(n+1) > xn j ≥ 1`,
   so `δ²(n+1) > 1`. Path length ≥ 1 is guaranteed.

However, proving these requires a "staircase path" construction (paths that walk in a specific
coordinate direction while alternating between two shells) to achieve sufficient endpoint
separation for large n. This infrastructure does not exist in the current codebase.

## Concrete Counterexample (Case 4, Same Axis)

For `d = 3`, `n = 0`, `δ = 1/24`:

- `xn = (0,0,0) ∈ sphere(0)`, `xnp1 = (1,0,0) ∈ sphere(1)`
- `axisPoint 0 0 = (0,0,0) = xn` ✓, `axisPoint 1 0 = (1,0,0) = xnp1` ✓
- `requiredInnerPathCount = 2·3 - 3 = 3`
- Path length upper bound: `⌊6 · (1/576) · 1⌋ = 0`
- 3 identical length-0 paths at origin: `finish = (0,0,0)`, `vertexSet = {(0,0,0)}`
- Pairwise endpoint separation requires: `(1/24)³ ≤ dist(0, 0) = 0` — **FALSE**

This counterexample was computationally verified in Lean (see the `example` declarations
confirming the floor computations and distance calculations).

## Suggested Fixes

### Option 1: Add hypothesis to main theorem
Add `(hn : 1 ≤ Nat.floor (δ ^ 2 * (↑n + 1)))` to `main_theorem` and propagate to case lemmas.
This ensures paths can have positive length.

### Option 2: Modify definitions
Change `endpointSeparationRadius` to be 0 when `⌊δ²(n+1)⌋ = 0`:
```lean
def endpointSeparationRadius (δ : ℝ) (n : Nat) : ℝ :=
  if Nat.floor (δ ^ 2 * (n + 1 : ℝ)) = 0 then 0
  else δ ^ 3 * (n + 1 : ℝ)
```

### Option 3: Adjust path counts
Reduce `requiredInnerPathCount` to `min (2*d - 3) 1` when paths are forced to have length 0.

## What Was Done

1. **Fixed build error**: `loopless` field type mismatch (line 76)
2. **Verified build** succeeds with existing sorries
3. **Identified** that 9/11 sorry'd lemmas are provably false
4. **Identified** that 2/11 sorry'd lemmas are likely true but require staircase infrastructure
5. **Provided** computational verification of counterexamples in Lean
6. **Documented** the analysis in this file
