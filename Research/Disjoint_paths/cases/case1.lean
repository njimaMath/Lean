import cases.common

namespace DisjointPaths

axiom exists_disjoint_paths_case1_large_coordinate
    {n : Nat} {δ : ℝ} {xn xnp1 : Zd d} {r : Fin d}
    (hd : 3 ≤ d)
    (hδ_nonneg : 0 ≤ δ)
    (hδ : δ ≤ 1 / (((8 * d : Nat) : ℝ)))
    (hlarge : SufficientlyLargeN (d := d) n δ)
    (hxn : xn ∈ Zd.sphere n)
    (hxnp1 : xnp1 ∈ Zd.sphere (n + 1))
    (hr_neg : xnp1 r < 0)
    (hr_large : 3 * δ ^ 2 * (n + 1 : ℝ) ≤ (xn r : ℝ)) :
    HasDesiredDisjointPaths (d := d) n δ xn xnp1

axiom exists_disjoint_paths_case1_small_coordinate
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
    HasDesiredDisjointPaths (d := d) n δ xn xnp1

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

end DisjointPaths
