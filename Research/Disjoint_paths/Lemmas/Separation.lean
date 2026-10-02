import Disjoint_paths.Lemmas.Basic
import Mathlib.Tactic.Linarith

/-!
# Separation by one coordinate

The geometric constructions distinguish paths by a coordinate interval.  The
lemmas here convert that interval information into the exact `l1Dist` and
edge-disjointness conclusions used by the main theorem.
-/

namespace DisjointPaths

lemma edgeDisjoint_of_vertices_disjoint {d : ℕ} (p q : LatticePath d)
    (hvertices : Disjoint {x | x ∈ p.vertices} {x | x ∈ q.vertices}) :
    Disjoint p.edgeSet q.edgeSet := by
  rw [Set.disjoint_left]
  intro e hep heq
  have hp := p.edgeSet_endpoints_mem hep
  have hq := q.edgeSet_endpoints_mem heq
  exact Set.disjoint_left.mp hvertices hp.1 hq.1

lemma vertices_disjoint_of_coordinate_gap {d : ℕ} (p q : LatticePath d)
    (i : Fin d) (a b : ℤ)
    (hp : ∀ x ∈ p.vertices, a ≤ x i)
    (hq : ∀ x ∈ q.vertices, x i ≤ b)
    (hgap : b < a) :
    Disjoint {x | x ∈ p.vertices} {x | x ∈ q.vertices} := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  exact (not_lt_of_ge (le_trans (hp x hxp) (hq x hxq))) hgap

lemma edgeDisjoint_of_coordinate_gap {d : ℕ} (p q : LatticePath d)
    (i : Fin d) (a b : ℤ)
    (hp : ∀ x ∈ p.vertices, a ≤ x i)
    (hq : ∀ x ∈ q.vertices, x i ≤ b)
    (hgap : b < a) :
    Disjoint p.edgeSet q.edgeSet := by
  exact edgeDisjoint_of_vertices_disjoint p q
    (vertices_disjoint_of_coordinate_gap p q i a b hp hq hgap)

lemma intCast_le_l1Dist_of_coordinate_gap {d : ℕ}
    (x y : LatticePoint d) (i : Fin d) (k : ℤ)
    (hk : 0 ≤ k) (hgap : k ≤ x i - y i) :
    (k : ℝ) ≤ (l1Dist x y : ℝ) := by
  have habs : k ≤ |x i - y i| := by
    rw [abs_of_nonneg (le_trans hk hgap)]
    exact hgap
  have hnat : Int.toNat k ≤ Int.natAbs (x i - y i) := by
    simpa [Int.natAbs_of_nonneg hk] using habs
  have hdist := le_trans hnat (natAbs_coord_le_l1Dist x y i)
  have hk' : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  rw [← hk']
  exact_mod_cast hdist

lemma endpoint_far_from_vertices_of_coordinate_gap {d : ℕ}
    (p q : LatticePath d) (i : Fin d) (r : ℝ) (a b k : ℤ)
    (hrk : r ≤ (k : ℝ)) (hk : 0 ≤ k)
    (hfinish : a ≤ p.finish i)
    (hvertices : ∀ x ∈ q.vertices, x i ≤ b)
    (hgap : k ≤ a - b) :
    ∀ x ∈ q.vertices, r ≤ (l1Dist p.finish x : ℝ) := by
  intro x hx
  apply le_trans hrk
  apply intCast_le_l1Dist_of_coordinate_gap p.finish x i k hk
  linarith [hfinish, hvertices x hx, hgap]

lemma endpoint_far_from_vertices_of_reverse_coordinate_gap {d : ℕ}
    (p q : LatticePath d) (i : Fin d) (r : ℝ) (a b k : ℤ)
    (hrk : r ≤ (k : ℝ)) (hk : 0 ≤ k)
    (hfinish : p.finish i ≤ a)
    (hvertices : ∀ x ∈ q.vertices, b ≤ x i)
    (hgap : k ≤ b - a) :
    ∀ x ∈ q.vertices, r ≤ (l1Dist p.finish x : ℝ) := by
  intro x hx
  have hforward : (k : ℝ) ≤ (l1Dist x p.finish : ℝ) := by
    apply intCast_le_l1Dist_of_coordinate_gap x p.finish i k hk
    linarith [hfinish, hvertices x hx, hgap]
  have hsymm : l1Dist x p.finish = l1Dist p.finish x := by
    unfold l1Dist l1Norm
    apply Finset.sum_congr rfl
    intro j _
    change Int.natAbs (x j - p.finish j) =
      Int.natAbs (p.finish j - x j)
    rw [show x j - p.finish j = -(p.finish j - x j) by ring,
      Int.natAbs_neg]
  simpa [hsymm] using le_trans hrk hforward

lemma endpoint_far_from_vertices_of_signed_coordinate_gap {d : ℕ}
    (p q : LatticePath d) (i : Fin d) (s : ℤ)
    (hs : Int.natAbs s = 1) (r : ℝ) (a k : ℤ)
    (hrk : r ≤ (k : ℝ)) (hk : 0 ≤ k)
    (hfinish : a + k ≤ s * p.finish i)
    (hvertices : ∀ x ∈ q.vertices, s * x i ≤ a) :
    ∀ x ∈ q.vertices, r ≤ (l1Dist p.finish x : ℝ) := by
  rcases Int.natAbs_eq_iff.mp hs with hsign | hsign
  · apply endpoint_far_from_vertices_of_coordinate_gap
      p q i r (a + k) a k hrk hk
    · simpa [hsign] using hfinish
    · intro x hx
      simpa [hsign] using hvertices x hx
    · omega
  · apply endpoint_far_from_vertices_of_reverse_coordinate_gap
      p q i r (-(a + k)) (-a) k hrk hk
    · have := hfinish
      rw [hsign] at this
      norm_num at this
      omega
    · intro x hx
      have := hvertices x hx
      rw [hsign] at this
      norm_num at this
      omega
    · omega

end DisjointPaths
