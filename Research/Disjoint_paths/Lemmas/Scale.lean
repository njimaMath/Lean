import Disjoint_paths.Lemmas.Definitions
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The large-radius scale

All paths use the scale `δ² (n + 1)`.  This file collects the consequences of
`d ≥ 3` and `δ ≤ (8d)⁻¹` which are independent of the geometric cases.
-/

namespace DisjointPaths

noncomputable def pathScale (δ : ℝ) (n : ℕ) : ℕ :=
  ⌊δ ^ 2 * (n + 1 : ℝ)⌋₊

lemma delta_le_one_div_twenty_four {d : ℕ} (hd : 3 ≤ d)
    {δ : ℝ} (hδ : δ ≤ 1 / (8 * d : ℝ)) :
    δ ≤ 1 / 24 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hdenom : (24 : ℝ) ≤ 8 * d := by nlinarith
  have hinv : (1 : ℝ) / (8 * d) ≤ 1 / 24 := by
    exact one_div_le_one_div_of_le (by norm_num) hdenom
  exact hδ.trans hinv

lemma delta_sq_pos {δ : ℝ} (hδpos : 0 < δ) : 0 < δ ^ 2 := by
  positivity

lemma exists_large_scale_threshold (δ : ℝ) (hδpos : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      12 ≤ δ ^ 2 * (n + 1 : ℝ) := by
  have hsquare : 0 < δ ^ 2 := delta_sq_pos hδpos
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (12 / δ ^ 2)
  refine ⟨n₀, ?_⟩
  intro n hn
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hquot : 12 / δ ^ 2 ≤ (n : ℝ) := hn₀.trans hnR
  have hn_succ : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
  have := hquot.trans hn_succ
  apply (div_le_iff₀ hsquare).mp at this
  simpa [mul_comm] using this

lemma separation_radius_le_scale_div_twenty_four {d : ℕ}
    (hd : 3 ≤ d) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / (8 * d : ℝ)) (n : ℕ) :
    δ ^ 3 * (n + 1 : ℝ) ≤ (δ ^ 2 * (n + 1 : ℝ)) / 24 := by
  have hsmall := delta_le_one_div_twenty_four hd hδ
  have hsquare : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hn : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
  calc
    δ ^ 3 * (n + 1 : ℝ) =
        δ * (δ ^ 2 * (n + 1 : ℝ)) := by ring
    _ ≤ (1 / 24) * (δ ^ 2 * (n + 1 : ℝ)) := by
      gcongr
    _ = (δ ^ 2 * (n + 1 : ℝ)) / 24 := by ring

lemma separation_radius_le_floor_scale_div_three_sub_three {d : ℕ}
    (hd : 3 ≤ d) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / (8 * d : ℝ)) (n : ℕ)
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ)) :
    δ ^ 3 * (n + 1 : ℝ) ≤
      (((⌊δ ^ 2 * (n + 1 : ℝ)⌋ : ℤ) : ℝ) / 3 - 3) := by
  have hradius := separation_radius_le_scale_div_twenty_four hd hδpos hδ n
  have hfloor := (Int.sub_one_lt_floor (δ ^ 2 * (n + 1 : ℝ))).le
  nlinarith

lemma reservoir_scale_bound {d n : ℕ} (hd : 3 ≤ d) (hn : 1 ≤ n)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ)) :
    16 * (d : ℝ) ^ 2 * δ ^ 2 * (n + 1 : ℝ) ≤ n := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hdR
  have hδnonneg : 0 ≤ δ := hδpos.le
  have hmul : 8 * (d : ℝ) * δ ≤ 1 := by
    have hdenom : 0 < 8 * (d : ℝ) := by positivity
    have := (le_div_iff₀ hdenom).mp hδ
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hsquare : 64 * (d : ℝ) ^ 2 * δ ^ 2 ≤ 1 := by
    have hbase : 0 ≤ 8 * (d : ℝ) * δ := by positivity
    have hs := (sq_le_sq₀ hbase (by norm_num)).mpr hmul
    ring_nf at hs ⊢
    exact hs
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsquare_nonneg : 0 ≤ 16 * (d : ℝ) ^ 2 * δ ^ 2 := by positivity
  have hquarter : 16 * (d : ℝ) ^ 2 * δ ^ 2 ≤ 1 / 4 := by nlinarith
  calc
    16 * (d : ℝ) ^ 2 * δ ^ 2 * (n + 1 : ℝ)
        ≤ (1 / 4) * (n + 1 : ℝ) := by gcongr
    _ ≤ n := by nlinarith

lemma pathScale_cast_le {δ : ℝ} (n : ℕ) :
    (pathScale δ n : ℝ) ≤ δ ^ 2 * (n + 1 : ℝ) := by
  apply Nat.floor_le
  positivity

lemma separation_radius_le_pathScale {d : ℕ}
    (hd : 3 ≤ d) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / (8 * d : ℝ)) (n : ℕ)
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ)) :
    δ ^ 3 * (n + 1 : ℝ) ≤ (pathScale δ n : ℝ) := by
  have hradius := separation_radius_le_scale_div_twenty_four hd hδpos hδ n
  have hfloor := (Nat.lt_floor_add_one (δ ^ 2 * (n + 1 : ℝ))).le
  change δ ^ 2 * (n + 1 : ℝ) ≤ (pathScale δ n : ℝ) + 1 at hfloor
  nlinarith

lemma separation_radius_le_pathScale_div_six {d : ℕ}
    (hd : 3 ≤ d) {δ : ℝ} (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / (8 * d : ℝ)) (n : ℕ)
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ)) :
    δ ^ 3 * (n + 1 : ℝ) ≤ (((pathScale δ n) / 6 : ℕ) : ℝ) := by
  let m := pathScale δ n
  have hm : 12 ≤ m := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    exact hscale
  have hradius := separation_radius_le_scale_div_twenty_four hd hδpos hδ n
  have hfloor := (Nat.lt_floor_add_one (δ ^ 2 * (n + 1 : ℝ))).le
  change δ ^ 2 * (n + 1 : ℝ) ≤ (m : ℝ) + 1 at hfloor
  have hnat : m + 1 ≤ 24 * (m / 6) := by omega
  have hcast : (m : ℝ) + 1 ≤ 24 * ((m / 6 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  nlinarith

lemma pathScale_reservoir_bound {d n : ℕ} (hd : 3 ≤ d) (hn : 1 ≤ n)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ)) :
    d * pathScale δ n ≤ n := by
  have hmain := reservoir_scale_bound hd hn hδpos hδ
  have hfloor := pathScale_cast_le (δ := δ) n
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 0 ≤ δ ^ 2 * (n + 1 : ℝ) := by positivity
  have hcast : ((d * pathScale δ n : ℕ) : ℝ) ≤ n := by
    push_cast
    calc
      (d : ℝ) * pathScale δ n ≤ d * (δ ^ 2 * (n + 1 : ℝ)) := by gcongr
      _ ≤ 16 * (d : ℝ) ^ 2 * δ ^ 2 * (n + 1 : ℝ) := by
        have hcoeff : (d : ℝ) ≤ 16 * d ^ 2 := by nlinarith
        calc
          (d : ℝ) * (δ ^ 2 * (n + 1 : ℝ)) ≤
              (16 * d ^ 2) * (δ ^ 2 * (n + 1 : ℝ)) :=
            mul_le_mul_of_nonneg_right hcoeff hx
          _ = 16 * d ^ 2 * δ ^ 2 * (n + 1 : ℝ) := by ring
      _ ≤ n := hmain
  exact_mod_cast hcast

lemma pathScale_strong_reservoir_bound {d n : ℕ} (hd : 3 ≤ d) (hn : 1 ≤ n)
    {δ : ℝ} (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ)) :
    16 * d ^ 2 * pathScale δ n ≤ n := by
  have hmain := reservoir_scale_bound hd hn hδpos hδ
  have hfloor := pathScale_cast_le (δ := δ) n
  have hcast : ((16 * d ^ 2 * pathScale δ n : ℕ) : ℝ) ≤ n := by
    push_cast
    calc
      16 * (d : ℝ) ^ 2 * (pathScale δ n : ℝ) ≤
          16 * (d : ℝ) ^ 2 * (δ ^ 2 * (n + 1 : ℝ)) := by
            gcongr
      _ ≤ (n : ℝ) := by
        simpa [mul_assoc] using hmain
  exact_mod_cast hcast

lemma exists_construction_threshold {d : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      1 ≤ n ∧ 12 ≤ δ ^ 2 * (n + 1 : ℝ) ∧ d * pathScale δ n ≤ n := by
  obtain ⟨n₀, hn₀⟩ := exists_large_scale_threshold δ hδpos
  refine ⟨max 1 n₀, ?_⟩
  intro n hn
  have hnone : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ) :=
    hn₀ n (le_trans (le_max_right _ _) hn)
  exact ⟨hnone, hscale, pathScale_reservoir_bound hd hnone hδpos hδ⟩

lemma pathScale_length_lower {δ : ℝ} (n : ℕ) :
    ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((2 * pathScale δ n : ℕ) : ℤ) := by
  have hx : 0 ≤ δ ^ 2 * (n + 1 : ℝ) := by positivity
  rw [← Int.natCast_floor_eq_floor hx]
  change ((pathScale δ n : ℕ) : ℤ) ≤ ((2 * pathScale δ n : ℕ) : ℤ)
  exact_mod_cast (show pathScale δ n ≤ 2 * pathScale δ n by omega)

lemma pathScale_length_upper {d : ℕ} (hd : 1 ≤ d)
    (δ : ℝ) (n : ℕ) :
    ((2 * pathScale δ n : ℕ) : ℤ) ≤
      ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋ := by
  apply Int.le_floor.mpr
  have hfloor := pathScale_cast_le (δ := δ) n
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  push_cast
  calc
    (2 : ℝ) * pathScale δ n ≤ 2 * (δ ^ 2 * (n + 1 : ℝ)) := by
      gcongr
    _ ≤ 2 * d * δ ^ 2 * (n + 1 : ℝ) := by
      have hx : 0 ≤ δ ^ 2 * (n + 1 : ℝ) := by positivity
      nlinarith

lemma four_pathScale_length_upper {d : ℕ} (hd : 2 ≤ d)
    (δ : ℝ) (n : ℕ) :
    ((4 * pathScale δ n : ℕ) : ℤ) ≤
      ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋ := by
  apply Int.le_floor.mpr
  have hfloor := pathScale_cast_le (δ := δ) n
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  push_cast
  calc
    (4 : ℝ) * pathScale δ n ≤
        4 * (δ ^ 2 * (n + 1 : ℝ)) := by gcongr
    _ ≤ 2 * d * δ ^ 2 * (n + 1 : ℝ) := by
      have hx : 0 ≤ δ ^ 2 * (n + 1 : ℝ) := by positivity
      nlinarith

lemma six_pathScale_length_upper {d : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (n : ℕ) :
    ((6 * pathScale δ n : ℕ) : ℤ) ≤
      ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋ := by
  apply Int.le_floor.mpr
  have hfloor := pathScale_cast_le (δ := δ) n
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  push_cast
  calc
    (6 : ℝ) * pathScale δ n ≤
        6 * (δ ^ 2 * (n + 1 : ℝ)) := by gcongr
    _ ≤ 2 * d * δ ^ 2 * (n + 1 : ℝ) := by
      have hx : 0 ≤ δ ^ 2 * (n + 1 : ℝ) := by positivity
      nlinarith

end DisjointPaths
