# Progress Notes on `disjoint.lean`

## Critical Finding: Bug in `SufficientlyLargeN`

The original definition of `SufficientlyLargeN` was **too weak**, making the main theorem
(`main_theorem`) **false as stated**. 

### Counterexample

With `d = 3`, `n = 1`, `δ = 1/100`:
- `SufficientlyLargeN` was satisfied: `4 × (1/100)² × 2 = 1/1250 < 1/3` ✓
- `δ ≤ 1/(8d) = 1/24` ✓
- Path length upper bound: `⌊6 × (1/100)² × 2⌋ = ⌊0.0012⌋ = 0`
- **All paths forced to have length 0**
- Endpoint separation radius: `(1/100)³ × 2 = 1/500000 > 0`
- Two inner paths of length 0 from the same start have `dist(finish₁, vertex₂) = 0 < 1/500000`
- **Pairwise inner endpoint separation fails**

This counterexample was verified in Lean (see the `example` declarations and inline comments in
`disjoint.lean`).

### Fix Applied

`SufficientlyLargeN` was strengthened with a second conjunct:

```lean
def SufficientlyLargeN (n : Nat) (δ : ℝ) : Prop :=
  4 * δ ^ 2 * (n + 1 : ℝ) < (n : ℝ) / (d : ℝ) ∧
  (0 < δ → 2 ≤ Nat.floor (δ ^ 2 * (n + 1 : ℝ)))
```

The second conjunct ensures that when `δ > 0`, path lengths are at least 2, which guarantees
that spreading paths have sufficient endpoint separation. The fix is backward-compatible:
- For `δ < 0` (the `main_theorem_neg_delta` case), the second conjunct is vacuously true.
- For `δ = 0`, the second conjunct is vacuously true.
- The existing proof of `main_theorem_neg_delta` continues to compile unchanged.

## Spreading Path Infrastructure (New)

Added a "spreading path" construction (Section 5.8) that generalizes the existing zigzag paths.
Unlike zigzag paths (which bounce between two adjacent vertices), spreading paths move
progressively further in a chosen coordinate direction while compensating in a reservoir
coordinate:

```
vertex k = x + ⌈k/2⌉ × d₁ + ⌊k/2⌋ × d₂
```

where `d₁` and `d₂` are unit basis vectors (or their negations).

### Helper lemmas proved (sorry-free):

| Lemma | Purpose |
|-------|---------|
| `spreadVertex_zero` | Spreading path starts at `x` |
| `spreadVertex_step` | Step formula: adds `d₁` or `d₂` depending on parity |
| `spreadVertex_adj` | Adjacent steps are lattice-adjacent |
| `spreadVertex_l1norm_inner` | L¹ norm alternates between `n` and `n+1` |
| `spreadVertex_coord_unchanged` | Coordinates not in `{active, reservoir}` are unchanged |
| `spreadPathSpec_start` | PathSpec starts at the right vertex |
| `spreadPathSpec_finish_inner` | Finish coordinate formula |
| `spreadPathSpec_staysIn_inner` | Path stays on `shellUnion n` |
| `spread_edgeDisjoint` | Different active coordinates ⟹ edge-disjoint |
| `spread_endpoint_separation` | Different active coordinates ⟹ endpoint separation |

## Remaining Sorry's

12 sorry's remain in the case lemmas:

1. `hasDesiredDisjointPaths_of_delta_zero` — δ = 0 trivial case (newly added)
2. `exists_disjoint_paths_case1_large_coordinate` — Case 1 (different orthants, large coord)
3. `exists_disjoint_paths_case1_small_coordinate` — Case 1 (different orthants, small coord)
4. `exists_disjoint_paths_case2_large_j_coordinate` — Case 2 (axis xnp1, large j)
5. `exists_disjoint_paths_case2_small_j_coordinate` — Case 2 (axis xnp1, small j)
6. `exists_disjoint_paths_case3_core` — Case 3 core construction
7. `exists_disjoint_paths_case3` — Case 3 assembly
8. `exists_disjoint_paths_case4_distinct_axes` — Case 4 (i ≠ j)
9. `exists_disjoint_paths_case4_same_axis` — Case 4 (i = j)
10. `exists_disjoint_paths_case5_positive_neighbor_coordinate` — Case 5 (xn(j) > 0)
11. `exists_disjoint_paths_case5` (line 1200, xn(j) = 0 branch) — Case 5 remainder
12. `exists_disjoint_paths_case6` — Case 6

Each remaining sorry requires:
- Constructing explicit path families using the spreading path infrastructure
- Assembling them into a `DisjointPathConfiguration`
- Verifying all field requirements (path counts, shell containment, edge disjointness, endpoint separation)

The spreading path infrastructure provides the key building blocks; the main remaining
challenge is the assembly step for each specific case geometry.
