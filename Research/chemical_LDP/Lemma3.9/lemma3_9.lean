import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace ChemicalLDP
namespace Lemma39

open Classical

/-- A point of `ℤ^d`, represented as a function on `Fin d`. -/
abbrev Point (d : ℕ) := Fin d → ℤ

/--
The diameter term from the blueprint, interpreted as the metric diameter of the
finite subset `S ⊆ ℤ^d`.
-/
noncomputable def diam {d : ℕ} (S : Finset (Point d)) : ℝ :=
  Metric.diam (S : Set (Point d))

/--
The lower bound `m(d, S)` appearing in the blueprint.
-/
noncomputable def m {d : ℕ} (S : Finset (Point d)) : ℝ :=
  ((S.card : ℝ) / ((2 : ℝ) ^ (d - 1) * (diam S + 1))) ^ (1 / (d - 1 : ℝ))

/--
`CoordinateSeparated S i j` says that distinct points of `S` have distinct
`i`-coordinates and distinct `j`-coordinates.
-/
def CoordinateSeparated {d : ℕ} (S : Finset (Point d)) (i j : Fin d) : Prop :=
  ∀ ⦃z z' : Point d⦄, z ∈ S → z' ∈ S → z ≠ z' → z i ≠ z' i ∧ z j ≠ z' j

/-- Drop coordinate `k` from a point in `ℤ^(d+1)` to get a point in `ℤ^d`. -/
def dropCoord {d : ℕ} (k : Fin (d + 1)) (z : Point (d + 1)) : Point d :=
  z ∘ k.succAbove

-- ============================================================
-- Section 1: Basic properties of CoordinateSeparated
-- ============================================================

lemma coordSep_mono {d : ℕ} {S T : Finset (Point d)} {i j : Fin d}
    (hST : S ⊆ T) (hT : CoordinateSeparated T i j) : CoordinateSeparated S i j :=
  fun _ _ ha hb hab => hT (hST ha) (hST hb) hab

lemma coordSep_insert {d : ℕ} {S : Finset (Point d)} {i j : Fin d} {z : Point d}
    (hS : CoordinateSeparated S i j) (_hz : z ∉ S)
    (hi : ∀ t ∈ S, z i ≠ t i) (hj : ∀ t ∈ S, z j ≠ t j) :
    CoordinateSeparated (insert z S) i j := by
  intro a b ha hb hab;
  cases eq_or_ne a z <;> cases eq_or_ne b z <;> simp_all +decide [ CoordinateSeparated ];
  exact ⟨ Ne.symm ( hi a ha ), Ne.symm ( hj a ha ) ⟩

/-
============================================================
Section 2: Maximal coordinate-separated subset with covering
============================================================

For any nonempty `S` and distinct coordinates `i ≠ j`, there exists a
coordinate-separated subset `T ⊆ S` that is maximal in the sense that every
point of `S` shares its `i`-coordinate or `j`-coordinate with some point of `T`.
-/
lemma exists_maximal_coordSep {d : ℕ} (S : Finset (Point d)) (i j : Fin d)
    (_hij : i ≠ j) (hS : S.Nonempty) :
    ∃ T : Finset (Point d), T ⊆ S ∧ T.Nonempty ∧ CoordinateSeparated T i j ∧
      ∀ z ∈ S, (∃ t ∈ T, z i = t i) ∨ (∃ t ∈ T, z j = t j) := by
  -- Consider the set of all coordinate-separated subsets of S (w.r.t. i, j).
  set C := S.powerset.filter (fun T => CoordinateSeparated T i j) with hC_def;
  -- Since $C$ is nonempty, we can choose a maximal element $T$ from $C$.
  obtain ⟨T, hT_mem, hT_max⟩ : ∃ T ∈ C, ∀ U ∈ C, U.card ≤ T.card := by
    apply_rules [ Finset.exists_max_image ];
    exact ⟨ { hS.choose }, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.singleton_subset_iff.mpr hS.choose_spec, fun z z' hz hz' hne => False.elim <| hne <| by aesop ⟩ ⟩;
  refine' ⟨ T, Finset.mem_powerset.mp ( Finset.mem_filter.mp hT_mem |>.1 ), Finset.nonempty_of_ne_empty _, Finset.mem_filter.mp hT_mem |>.2, fun z hz => _ ⟩;
  · contrapose! hT_max;
    exact ⟨ { hS.choose }, by exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.subset_iff.mpr <| Finset.singleton_subset_iff.mpr hS.choose_spec, by simp +decide [ CoordinateSeparated ] ⟩, by simp +decide [ hT_max ] ⟩;
  · contrapose! hT_max;
    refine' ⟨ Insert.insert z T, _, _ ⟩ <;> simp_all +decide [ Finset.mem_powerset, Finset.subset_iff ];
    · exact coordSep_insert hT_mem.2 ( by aesop ) ( by aesop ) ( by aesop );
    · rw [ Finset.card_insert_of_notMem ] <;> aesop

-- ============================================================
-- Section 3: Diameter and fiber bounds
-- ============================================================

lemma diam_nonneg' {d : ℕ} (S : Finset (Point d)) : 0 ≤ diam S :=
  Metric.diam_nonneg

lemma diam_add_one_pos {d : ℕ} (S : Finset (Point d)) : (0 : ℝ) < diam S + 1 := by
  linarith [diam_nonneg' S]

/-
For `d = 2`, fixing one coordinate of points in `S` leaves at most `⌊diam S⌋ + 1 ≤ diam S + 1`
points (since the other coordinate ranges over an interval of length at most `diam S`).
-/
lemma fiber_card_le_diam_add_one (S : Finset (Point 2)) (k : Fin 2) (v : ℤ) :
    ((S.filter (fun z => z k = v)).card : ℝ) ≤ diam S + 1 := by
  let F : Finset (Point 2) := S.filter (fun z => z k = v)
  let G : Finset ℤ := F.image (fun z : Point 2 => z (k + 1))
  have hG_card : F.card = G.card := by
    dsimp [G]
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    fin_cases k
    · have hx0 : x 0 = v := (Finset.mem_filter.mp hx).2
      have hy0 : y 0 = v := (Finset.mem_filter.mp hy).2
      ext i
      fin_cases i
      · simp [hx0, hy0]
      · simpa using hxy
    · have hx1 : x 1 = v := (Finset.mem_filter.mp hx).2
      have hy1 : y 1 = v := (Finset.mem_filter.mp hy).2
      ext i
      fin_cases i
      · simpa using hxy
      · simp [hx1, hy1]
  by_cases hF : F.Nonempty
  · have h_dist :
        ∀ z z' : Point 2, z ∈ S → z' ∈ S → z k = v → z' k = v →
          abs (z (k + 1) - z' (k + 1)) ≤ diam S := by
      intro z z' hz hz' hv hv'
      refine le_trans ?_
        (Metric.dist_le_diam_of_mem
          (Set.Finite.isBounded <| Finset.finite_toSet S)
          (Finset.mem_coe.mpr hz) (Finset.mem_coe.mpr hz'))
      · simp +decide [dist_eq_norm, Pi.norm_def]
        simp +decide [Fin.univ_succ]
        fin_cases k <;> simp +decide [Norm.norm]
    have hG_nonempty : G.Nonempty := by
      obtain ⟨z, hz⟩ := hF
      exact ⟨z (k + 1), Finset.mem_image_of_mem _ hz⟩
    obtain ⟨z₀, hz₀mem, hz₀min⟩ : ∃ z₀ ∈ G, ∀ z ∈ G, z₀ ≤ z := by
      exact ⟨G.min' hG_nonempty, Finset.min'_mem _ _, fun z hz => Finset.min'_le _ _ hz⟩
    obtain ⟨z₁, hz₁mem, hz₁max⟩ : ∃ z₁ ∈ G, ∀ z ∈ G, z ≤ z₁ := by
      exact ⟨G.max' hG_nonempty, Finset.max'_mem _ _, fun z hz => Finset.le_max' _ _ hz⟩
    have h_interval : G.card ≤ (Finset.Icc z₀ z₁).card := by
      exact Finset.card_le_card fun x hx => Finset.mem_Icc.mpr ⟨hz₀min x hx, hz₁max x hx⟩
    have hz₀_le_z₁ : z₀ ≤ z₁ := hz₀min z₁ hz₁mem
    have h_interval_length : (z₁ : ℝ) - z₀ ≤ diam S := by
      obtain ⟨a, haF, ha_eq⟩ := Finset.mem_image.mp hz₀mem
      obtain ⟨b, hbF, hb_eq⟩ := Finset.mem_image.mp hz₁mem
      have h_dist_ab :
          |(z₀ : ℝ) - z₁| ≤ diam S := by
        simpa [G, ha_eq, hb_eq] using
          h_dist a b (Finset.mem_filter.mp haF).1 (Finset.mem_filter.mp hbF).1
            (Finset.mem_filter.mp haF).2 (Finset.mem_filter.mp hbF).2
      have hz₀_le_z₁' : (z₀ : ℝ) ≤ z₁ := by exact_mod_cast hz₀_le_z₁
      have habs :
          |(z₀ : ℝ) - z₁| = (z₁ : ℝ) - z₀ := by
        rw [abs_of_nonpos (sub_nonpos.mpr hz₀_le_z₁')]
        ring
      rw [habs] at h_dist_ab
      exact h_dist_ab
    have h_interval_card : ((Finset.Icc z₀ z₁).card : ℝ) ≤ diam S + 1 := by
      have hz₀_le_z₁_succ : z₀ ≤ z₁ + 1 := by linarith
      have hcard_int : ((Finset.Icc z₀ z₁).card : ℤ) = z₁ + 1 - z₀ := by
        simpa using Int.card_Icc_of_le (a := z₀) (b := z₁) hz₀_le_z₁_succ
      have hcard_real : ((Finset.Icc z₀ z₁).card : ℝ) = (z₁ : ℝ) + 1 - z₀ := by
        exact_mod_cast hcard_int
      linarith
    have hG_bound : ((G.card : ℕ) : ℝ) ≤ diam S + 1 := by
      exact le_trans (Nat.cast_le.mpr h_interval) h_interval_card
    rw [← hG_card] at hG_bound
    simpa [F] using hG_bound
  · have hF_eq : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [F, hF_eq]
    linarith [diam_nonneg' S]

/-
============================================================
Section 4: Projection (dropCoord) properties
============================================================

`dropCoord` is injective on points sharing the same `k`-th coordinate.
-/
lemma dropCoord_injective_of_eq {d : ℕ} (k : Fin (d + 1)) {z z' : Point (d + 1)}
    (hk : z k = z' k) (h : dropCoord k z = dropCoord k z') : z = z' := by
  ext i; exact (by
  by_cases hi : i = k <;> simp_all +decide [funext_iff];
  obtain ⟨ j, hj ⟩ := Fin.exists_succAbove_eq hi; aesop;);

/-
The diameter does not increase under `dropCoord`.
-/
lemma diam_image_dropCoord_le {d : ℕ} (k : Fin (d + 1))
    (S : Finset (Point (d + 1))) :
    diam (S.image (dropCoord k)) ≤ diam S := by
  refine' Metric.diam_le_of_forall_dist_le _ _;
  · exact diam_nonneg' S;
  · -- Let $x, y \in \text{image}(S, \text{dropCoord } k)$. Then there exist $z, z' \in S$ such that $x = \text{dropCoord } k z$ and $y = \text{dropCoord } k z'$.
    intro x hx y hy
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z', hz'S, rfl⟩ := Finset.mem_image.mp hy;
    refine' le_trans _
      (Metric.dist_le_diam_of_mem
        (Set.Finite.isBounded <| Finset.finite_toSet S) hzS hz'S);
    · simp +decide [ dist_eq_norm, Pi.norm_def ];
      exact fun i => Finset.le_sup ( f := fun b => ‖z b - z' b‖₊ ) ( Finset.mem_univ ( Fin.succAbove k i ) );

/-
Coordinate separation lifts from the projected image back to the original set,
    provided all points share the same `k`-th coordinate.
-/
lemma coordSep_lift_dropCoord {d : ℕ} (k : Fin (d + 1))
    {S : Finset (Point (d + 1))} {i j : Fin d}
    (hv : ∀ z ∈ S, ∀ z' ∈ S, z k = z' k)
    (hcs : CoordinateSeparated (S.image (dropCoord k)) i j) :
    CoordinateSeparated S (k.succAbove i) (k.succAbove j) := by
  intro z hz z' hz' ne; have := hcs; simp_all +decide [ CoordinateSeparated ] ;
  specialize this _ z' rfl _ hz' rfl ( show ( dropCoord k z ) ≠ ( dropCoord k hz ) from by contrapose! ne; exact dropCoord_injective_of_eq _ ( hv _ z' _ hz' ) ne ) ; aesop;

/-
============================================================
Section 5: Algebraic bound for the inductive step
============================================================

Key algebraic bound: if `u = m(d+1, S) > 0`, `|T| ≥ |S|/(2u)`, and `diam T ≤ diam S`,
then `m(d, T) ≥ u`, where dimensions are `d+1` and `d` respectively (with `d ≥ 2`).
-/
lemma m_step_bound {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Point (n + 1))) (hS : S.Nonempty)
    (T : Finset (Point n)) (hTne : T.Nonempty)
    (hcard : (S.card : ℝ) / (2 * m S) ≤ T.card)
    (hdiam : diam T ≤ diam S) :
    m S ≤ m T := by
  -- From hcard: T.card ≥ S.card / (2 * m S).
  have hcard_ge : (T.card : ℝ) ≥ (S.card : ℝ) / (2 * m S) := by
    exact hcard;
  -- From hcard_ge: T.card ≥ S.card / (2 * m S).
  have hcard_ge_simplified : (T.card : ℝ) / (2 ^ (n - 1) * (diam T + 1)) ≥ (m S) ^ (n - 1) := by
    -- From hcard_ge: T.card ≥ S.card / (2 * m S), we can rewrite it as T.card * (2 * m S) ≥ S.card.
    have hcard_ge_rewrite : (T.card : ℝ) * (2 * m S) ≥ (S.card : ℝ) := by
      rwa [ ge_iff_le, div_le_iff₀ ] at hcard_ge;
      exact mul_pos zero_lt_two ( Real.rpow_pos_of_pos ( div_pos ( Nat.cast_pos.mpr hS.card_pos ) ( mul_pos ( pow_pos zero_lt_two _ ) ( add_pos_of_nonneg_of_pos ( diam_nonneg' _ ) zero_lt_one ) ) ) _ );
    -- From hcard_ge_rewrite: T.card * (2 * m S) ≥ S.card, we can rewrite it as T.card * (2 * m S) ≥ (m S)^n * (2^n * (diam S + 1)).
    have hcard_ge_rewrite_simplified : (T.card : ℝ) * (2 * m S) ≥ (m S) ^ n * (2 ^ n * (diam S + 1)) := by
      have hcard_ge_rewrite_simplified : (m S) ^ n = (S.card : ℝ) / (2 ^ n * (diam S + 1)) := by
        unfold m;
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by exact div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( pow_nonneg zero_le_two _ ) ( add_nonneg ( diam_nonneg' _ ) zero_le_one ) ) ), Nat.cast_succ, add_sub_cancel_right, div_mul_cancel₀ _ ( by positivity ), Real.rpow_one ] ; norm_num;
      rw [ hcard_ge_rewrite_simplified, div_mul_cancel₀ _ ( by exact ne_of_gt ( mul_pos ( by positivity ) ( add_pos_of_nonneg_of_pos ( diam_nonneg' _ ) zero_lt_one ) ) ) ] ; linarith;
    -- From hcard_ge_rewrite_simplified: T.card * (2 * m S) ≥ (m S)^n * (2^n * (diam S + 1)), we can divide both sides by (2 * m S) to get T.card ≥ (m S)^(n-1) * (2^(n-1) * (diam S + 1)).
    have hcard_ge_div : (T.card : ℝ) ≥ (m S) ^ (n - 1) * (2 ^ (n - 1) * (diam S + 1)) := by
      rcases n <;> simp_all +decide [ pow_succ' ];
      nlinarith [ show 0 < m S from Real.rpow_pos_of_pos ( div_pos ( Nat.cast_pos.mpr hS.card_pos ) ( mul_pos ( pow_pos ( by norm_num ) _ ) ( add_pos_of_nonneg_of_pos ( diam_nonneg' S ) zero_lt_one ) ) ) _ ];
    rw [ ge_iff_le, le_div_iff₀ ];
    · exact le_trans ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( by linarith ) ( by positivity ) ) ( by exact pow_nonneg ( by exact Real.rpow_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( add_nonneg ( Metric.diam_nonneg ) zero_le_one ) ) ) _ ) _ ) ) hcard_ge_div;
    · exact mul_pos ( pow_pos ( by norm_num ) _ ) ( add_pos_of_nonneg_of_pos ( diam_nonneg' _ ) zero_lt_one );
  -- From hcard_ge_simplified: T.card / (2^(n-1) * (diam T + 1)) ≥ (m S)^(n-1).
  have hcard_ge_simplified_root : (T.card : ℝ) / (2 ^ (n - 1) * (diam T + 1)) ≥ (m S) ^ (n - 1) → (m T) ≥ (m S) := by
    intro h;
    refine' le_trans _ ( Real.rpow_le_rpow _ h _ );
    · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by exact Real.rpow_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( pow_nonneg zero_le_two _ ) ( add_nonneg ( diam_nonneg' _ ) zero_le_one ) ) ) _ ), Nat.cast_sub ( by linarith ), Nat.cast_one, mul_one_div_cancel ( sub_ne_zero_of_ne ( by norm_cast; linarith ) ), Real.rpow_one ];
    · exact pow_nonneg ( Real.rpow_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( pow_nonneg zero_le_two _ ) ( add_nonneg ( diam_nonneg' _ ) zero_le_one ) ) ) _ ) _;
    · exact div_nonneg zero_le_one ( by norm_num; linarith );
  exact hcard_ge_simplified_root hcard_ge_simplified

/-
============================================================
Section 6: Base case (d = 2) and inductive step
============================================================

Base case: Lemma 3.9 for `d = 2`.
-/
lemma lemma_3_9_base (S : Finset (Point 2)) (hS : S.Nonempty) :
    ∃ i j : Fin 2, i ≠ j ∧ ∃ S' : Finset (Point 2),
      S' ⊆ S ∧ m S ≤ (S'.card : ℝ) ∧ CoordinateSeparated S' i j := by
  refine ⟨ 0, 1, ?_, ?_ ⟩;
  · decide;
  · obtain ⟨ T, hT₁, hT₂, hT₃, hT₄ ⟩ := exists_maximal_coordSep S 0 1 ( by decide ) hS;
    refine' ⟨ T, hT₁, _, hT₃ ⟩;
    -- Apply the fiber cardinality bound to each of the two sets in the union.
    have h_card_union : (S.card : ℝ) ≤ (∑ t ∈ T, (S.filter (fun z => z 0 = t 0)).card) + (∑ t ∈ T, (S.filter (fun z => z 1 = t 1)).card) := by
      have h_card_union : S.card ≤ Finset.card (Finset.biUnion T (fun t => S.filter (fun z => z 0 = t 0))) + Finset.card (Finset.biUnion T (fun t => S.filter (fun z => z 1 = t 1))) := by
        exact le_trans ( Finset.card_le_card fun x hx => by specialize hT₄ x hx; aesop ) ( Finset.card_union_le _ _ );
      exact_mod_cast h_card_union.trans ( add_le_add ( Finset.card_biUnion_le ) ( Finset.card_biUnion_le ) );
    -- Apply the fiber cardinality bound to each of the two sets in the union to get the desired inequality.
    have h_card_bound : (S.card : ℝ) ≤ 2 * T.card * (diam S + 1) := by
      have h_card_bound : ∀ t ∈ T, (S.filter (fun z => z 0 = t 0)).card ≤ diam S + 1 ∧ (S.filter (fun z => z 1 = t 1)).card ≤ diam S + 1 := by
        exact fun t ht => ⟨ fiber_card_le_diam_add_one S 0 _, fiber_card_le_diam_add_one S 1 _ ⟩;
      norm_num +zetaDelta at *;
      exact h_card_union.trans ( by rw [ two_mul ] ; exact le_trans ( add_le_add ( Finset.sum_le_sum fun x hx => h_card_bound x hx |>.1 ) ( Finset.sum_le_sum fun x hx => h_card_bound x hx |>.2 ) ) ( by norm_num; linarith ) );
    unfold m;
    norm_num;
    rw [ div_le_iff₀ ] <;> nlinarith [ show 0 < diam S + 1 from diam_add_one_pos S ]

/-
Inductive step: assuming Lemma 3.9 for dimension `n ≥ 2`, derive it for `n + 1`.
-/
lemma lemma_3_9_step (n : ℕ) (hn : 2 ≤ n)
    (ih : ∀ (S : Finset (Point n)), S.Nonempty →
      ∃ i j : Fin n, i ≠ j ∧ ∃ S' : Finset (Point n),
        S' ⊆ S ∧ m S ≤ (S'.card : ℝ) ∧ CoordinateSeparated S' i j)
    (S : Finset (Point (n + 1))) (hS : S.Nonempty) :
    ∃ i j : Fin (n + 1), i ≠ j ∧ ∃ S' : Finset (Point (n + 1)),
      S' ⊆ S ∧ m S ≤ (S'.card : ℝ) ∧ CoordinateSeparated S' i j := by
  -- Define i₀ and j₀ as the last two coordinates in Fin (n + 1).
  set i₀ : Fin (n + 1) := ⟨n - 1, by
    omega⟩
  set j₀ : Fin (n + 1) := ⟨n, by
    linarith⟩
  generalize_proofs at *;
  obtain ⟨T, hT⟩ : ∃ T : Finset (Point (n + 1)), T ⊆ S ∧ T.Nonempty ∧ CoordinateSeparated T i₀ j₀ ∧ ∀ z ∈ S, (∃ t ∈ T, z i₀ = t i₀) ∨ (∃ t ∈ T, z j₀ = t j₀) := by
    apply exists_maximal_coordSep S i₀ j₀;
    · grind;
    · assumption;
  by_cases h_case : m S ≤ T.card;
  · exact ⟨ i₀, j₀, ne_of_lt ( Nat.pred_lt ( ne_bot_of_gt hn ) ), T, hT.1, h_case, hT.2.2.1 ⟩;
  · -- By the pigeonhole principle, there exists a coordinate $k \in \{i₀, j₀\}$ and a value $v$ such that the fiber $S.filter (fun z => z k = v)$ has size at least $S.card / (2 * T.card)$.
    obtain ⟨k, _hk_mem, v, hv⟩ :
        ∃ k ∈ [i₀, j₀], ∃ v : ℤ, (S.filter (fun z => z k = v)).card ≥ S.card / (2 * T.card : ℝ) := by
      have h_cover :
          (S.card : ℝ) ≤
            (∑ t ∈ T, ((S.filter (fun z => z i₀ = t i₀)).card : ℝ)) +
            (∑ t ∈ T, ((S.filter (fun z => z j₀ = t j₀)).card : ℝ)) := by
        have h_subset :
            S ⊆
              Finset.biUnion T (fun t => S.filter (fun z => z i₀ = t i₀)) ∪
              Finset.biUnion T (fun t => S.filter (fun z => z j₀ = t j₀)) := by
          intro z hz
          rcases hT.2.2.2 z hz with ⟨t, ht, hzt⟩ | ⟨t, ht, hzt⟩
          · refine Finset.mem_union.mpr <| Or.inl <| Finset.mem_biUnion.mpr ?_
            exact ⟨t, ht, by simp [hz, hzt]⟩
          · refine Finset.mem_union.mpr <| Or.inr <| Finset.mem_biUnion.mpr ?_
            exact ⟨t, ht, by simp [hz, hzt]⟩
        have h_cover_nat :
            S.card ≤
              Finset.card (Finset.biUnion T (fun t => S.filter (fun z => z i₀ = t i₀))) +
              Finset.card (Finset.biUnion T (fun t => S.filter (fun z => z j₀ = t j₀))) := by
          exact le_trans (Finset.card_le_card h_subset) (Finset.card_union_le _ _)
        have h_cover_nat' :
            S.card ≤
              (∑ t ∈ T, (S.filter (fun z => z i₀ = t i₀)).card) +
              (∑ t ∈ T, (S.filter (fun z => z j₀ = t j₀)).card) := by
          exact le_trans h_cover_nat (add_le_add Finset.card_biUnion_le Finset.card_biUnion_le)
        exact_mod_cast h_cover_nat'
      have h_half :
          (S.card : ℝ) / 2 ≤ ∑ t ∈ T, ((S.filter (fun z => z i₀ = t i₀)).card : ℝ) ∨
            (S.card : ℝ) / 2 ≤ ∑ t ∈ T, ((S.filter (fun z => z j₀ = t j₀)).card : ℝ) := by
        by_cases hleft :
            (S.card : ℝ) / 2 ≤ ∑ t ∈ T, ((S.filter (fun z => z i₀ = t i₀)).card : ℝ)
        · exact Or.inl hleft
        · have hright :
              (S.card : ℝ) / 2 ≤ ∑ t ∈ T, ((S.filter (fun z => z j₀ = t j₀)).card : ℝ) := by
            linarith
          exact Or.inr hright
      have hTcard_ne : (T.card : ℝ) ≠ 0 := by
        exact_mod_cast hT.2.1.card_ne_zero
      cases h_half with
      | inl hleft =>
          have hleft_avg :
              ∑ t ∈ T, ((S.card : ℝ) / (2 * T.card : ℝ)) ≤
                ∑ t ∈ T, ((S.filter (fun z => z i₀ = t i₀)).card : ℝ) := by
            calc
              ∑ t ∈ T, ((S.card : ℝ) / (2 * T.card : ℝ))
                  = (T.card : ℝ) * ((S.card : ℝ) / (2 * T.card : ℝ)) := by simp
              _ = (S.card : ℝ) / 2 := by
                field_simp [hTcard_ne]
              _ ≤ ∑ t ∈ T, ((S.filter (fun z => z i₀ = t i₀)).card : ℝ) := hleft
          obtain ⟨t, htT, ht⟩ := Finset.exists_le_of_sum_le hT.2.1 hleft_avg
          refine ⟨i₀, by simp, t i₀, ?_⟩
          simpa using ht
      | inr hright =>
          have hright_avg :
              ∑ t ∈ T, ((S.card : ℝ) / (2 * T.card : ℝ)) ≤
                ∑ t ∈ T, ((S.filter (fun z => z j₀ = t j₀)).card : ℝ) := by
            calc
              ∑ t ∈ T, ((S.card : ℝ) / (2 * T.card : ℝ))
                  = (T.card : ℝ) * ((S.card : ℝ) / (2 * T.card : ℝ)) := by simp
              _ = (S.card : ℝ) / 2 := by
                field_simp [hTcard_ne]
              _ ≤ ∑ t ∈ T, ((S.filter (fun z => z j₀ = t j₀)).card : ℝ) := hright
          obtain ⟨t, htT, ht⟩ := Finset.exists_le_of_sum_le hT.2.1 hright_avg
          refine ⟨j₀, by simp, t j₀, ?_⟩
          simpa using ht
    -- Let $S₁ = S.filter (fun z => z k = v)$.
    set S₁ := S.filter (fun z => z k = v);
    have hS₁ : S₁.Nonempty := by
      exact Finset.card_pos.mp ( Nat.cast_pos.mp ( lt_of_lt_of_le ( div_pos ( Nat.cast_pos.mpr hS.card_pos ) ( mul_pos zero_lt_two ( Nat.cast_pos.mpr hT.2.1.card_pos ) ) ) hv ) );
    have hS₁_card : S₁.card ≥ S.card / (2 * m S : ℝ) := by
      exact le_trans ( div_le_div_of_nonneg_left ( Nat.cast_nonneg _ ) ( by norm_cast; linarith [ Finset.card_pos.mpr hT.2.1 ] ) ( by linarith ) ) hv;
    have hS₁_diam : diam S₁ ≤ diam S := by
      apply_rules [ Metric.diam_mono ] ; aesop_cat;
      exact Set.Finite.isBounded <| Finset.finite_toSet S;
    have hS₁_image : (S₁.image (dropCoord k)).Nonempty := by
      exact ⟨ _, Finset.mem_image_of_mem _ hS₁.choose_spec ⟩;
    have hS₁_image_card : (S₁.image (dropCoord k)).card = S₁.card := by
      rw [ Finset.card_image_of_injOn ];
      intro z hz z' hz' h_eq; exact dropCoord_injective_of_eq k ( by aesop ) h_eq;;
    have hS₁_image_diam : diam (S₁.image (dropCoord k)) ≤ diam S₁ := by
      apply diam_image_dropCoord_le;
    obtain ⟨i', j', hij', S₂, hS₂⟩ := ih (S₁.image (dropCoord k)) hS₁_image;
    use k.succAbove i', k.succAbove j', by
      simp +decide [hij'], S₁.filter (fun z => dropCoord k z ∈ S₂);
    generalize_proofs at *;
    refine' ⟨ _, _, _ ⟩;
    · exact fun x hx => Finset.mem_filter.mp hx |>.1 |> Finset.mem_filter.mp |>.1;
    · have hS₂_card : m S ≤ m (S₁.image (dropCoord k)) := by
        apply m_step_bound hn S hS (S₁.image (dropCoord k)) hS₁_image;
        · aesop;
        · exact le_trans hS₁_image_diam hS₁_diam;
      refine' le_trans hS₂_card ( le_trans hS₂.2.1 _ );
      rw [ show ( Finset.filter ( fun z => dropCoord k z ∈ S₂ ) S₁ ).card = S₂.card from ?_ ];
      refine' Finset.card_bij ( fun x hx => dropCoord k x ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
      · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; exact dropCoord_injective_of_eq k ( by aesop ) h;
      · exact fun x hx => by obtain ⟨ a, ha₁, ha₂ ⟩ := hS₂.1 hx; exact ⟨ a, ⟨ ha₁, by simpa [ ha₂ ] using hx ⟩, ha₂ ⟩ ;
    · apply coordSep_lift_dropCoord;
      · grind;
      · convert hS₂.2.2 using 1;
        grind

/-
============================================================
Section 7: Main theorem
============================================================

Blueprint Lemma 3.9 (labelled Lemma 4.2 in the source text).

For a nonempty finite set `S ⊆ ℤ^d` with `d ≥ 2`, there are two distinct
coordinates `i ≠ j` and a subset `S' ⊆ S` of size at least `m(d, S)` such that
the projections of `S'` on coordinates `i` and `j` are both injective.
-/
theorem lemma_3_9
    {d : ℕ} (hd : 2 ≤ d) (S : Finset (Point d)) (hS : S.Nonempty) :
    ∃ i j : Fin d, i ≠ j ∧ ∃ S' : Finset (Point d),
      S' ⊆ S ∧ m S ≤ (S'.card : ℝ) ∧ CoordinateSeparated S' i j := by
  -- By induction on $d$.
  induction' d, Nat.succ_le_iff.mpr hd using Nat.le_induction with d hd2 ih;
  · exact lemma_3_9_base S hS
  · exact lemma_3_9_step d hd2 (ih hd2) S hS

end Lemma39
end ChemicalLDP
