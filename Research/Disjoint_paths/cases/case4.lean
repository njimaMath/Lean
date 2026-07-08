import cases.common

namespace DisjointPaths

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

end DisjointPaths
