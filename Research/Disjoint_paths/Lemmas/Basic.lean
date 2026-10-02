import Disjoint_paths.Lemmas.Definitions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# Elementary facts for the disjoint-path construction

This file only develops consequences of the definitions fixed in
`Main_Disjoint.lean`. In particular, all distance comparisons below use the
same `l1Dist` that occurs in the final theorem.
-/

namespace DisjointPaths

namespace LatticePath

private lemma mem_zip_self_tail_endpoints {α : Type*} {l : List α}
    {a b : α} (h : (a, b) ∈ l.zip l.tail) : a ∈ l ∧ b ∈ l := by
  induction l with
  | nil => simp at h
  | cons x tail ih =>
      cases tail with
      | nil => simp at h
      | cons y rest =>
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
          rcases h with h | h
          · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
            simp
          · rcases ih h with ⟨ha, hb⟩
            exact ⟨List.mem_cons_of_mem x ha, List.mem_cons_of_mem x hb⟩

private lemma mem_zip_self_tail_ne {α : Type*} {l : List α}
    (hnodup : l.Nodup) {a b : α} (h : (a, b) ∈ l.zip l.tail) : a ≠ b := by
  induction l with
  | nil => simp at h
  | cons x tail ih =>
      cases tail with
      | nil => simp at h
      | cons y rest =>
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
          rcases h with h | h
          · have hxy : x ≠ y := by
              intro hxy
              subst y
              exact (List.nodup_cons.mp hnodup).1 (by simp)
            have ha : a = x := congrArg Prod.fst h
            have hb : b = y := congrArg Prod.snd h
            intro hab
            exact hxy (ha.symm.trans (hab.trans hb))
          · exact ih (List.Nodup.tail hnodup) h

lemma orientedEdge_endpoints_mem {d : ℕ} (p : LatticePath d)
    {a b : LatticePoint d} (h : (a, b) ∈ p.orientedEdges) :
    a ∈ p.vertices ∧ b ∈ p.vertices := by
  exact mem_zip_self_tail_endpoints h

lemma orientedEdge_ne {d : ℕ} (p : LatticePath d)
    {a b : LatticePoint d} (h : (a, b) ∈ p.orientedEdges) : a ≠ b := by
  exact mem_zip_self_tail_ne p.nodup h

lemma edgeSet_endpoints_mem {d : ℕ} (p : LatticePath d)
    {e : LatticePoint d × LatticePoint d} (h : e ∈ p.edgeSet) :
    e.1 ∈ p.vertices ∧ e.2 ∈ p.vertices := by
  rcases h with h | h
  · exact orientedEdge_endpoints_mem p h
  · exact (orientedEdge_endpoints_mem p h).symm

lemma edgeSet_endpoints_ne {d : ℕ} (p : LatticePath d)
    {e : LatticePoint d × LatticePoint d} (h : e ∈ p.edgeSet) : e.1 ≠ e.2 := by
  rcases h with h | h
  · exact orientedEdge_ne p h
  · exact Ne.symm (orientedEdge_ne p h)

lemma edgeDisjoint_of_common_vertices_subsingleton {d : ℕ}
    (p q : LatticePath d) (z : LatticePoint d)
    (hcommon : ∀ x, x ∈ p.vertices → x ∈ q.vertices → x = z) :
    Disjoint p.edgeSet q.edgeSet := by
  rw [Set.disjoint_left]
  intro e hep heq
  have hp := edgeSet_endpoints_mem p hep
  have hq := edgeSet_endpoints_mem q heq
  have hfirst : e.1 = z := hcommon e.1 hp.1 hq.1
  have hsecond : e.2 = z := hcommon e.2 hp.2 hq.2
  exact edgeSet_endpoints_ne p hep (hfirst.trans hsecond.symm)

lemma start_mem_vertices {d : ℕ} (p : LatticePath d) :
    p.start ∈ p.vertices := by
  exact List.head_mem p.nonempty

lemma finish_mem_vertices {d : ℕ} (p : LatticePath d) :
    p.finish ∈ p.vertices := by
  exact List.getLast_mem p.nonempty

lemma finish_eq_start_of_edgeLength_eq_zero {d : ℕ} (p : LatticePath d)
    (h : p.edgeLength = 0) : p.finish = p.start := by
  cases hvertices : p.vertices with
  | nil => exact False.elim (p.nonempty hvertices)
  | cons a tail =>
      cases tail with
      | nil => simp [finish, start, hvertices]
      | cons b tail =>
          simp [edgeLength, hvertices] at h

lemma one_le_edgeLength_of_finish_ne_start {d : ℕ} (p : LatticePath d)
    (h : p.finish ≠ p.start) : 1 ≤ p.edgeLength := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hzero
  exact h (finish_eq_start_of_edgeLength_eq_zero p hzero)

end LatticePath

@[simp] lemma l1Dist_self {d : ℕ} (x : LatticePoint d) : l1Dist x x = 0 := by
  simp [l1Dist, l1Norm]

lemma natAbs_coord_le_l1Dist {d : ℕ} (x y : LatticePoint d) (i : Fin d) :
    Int.natAbs (x i - y i) ≤ l1Dist x y := by
  unfold l1Dist l1Norm
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (Int.natAbs (x j - y j)))
    (Finset.mem_univ i)

lemma coordinate_sub_le_of_natAbs_sub_le {d : ℕ}
    (x z : LatticePoint d) (r : Fin d) (m : ℕ)
    (h : Int.natAbs (x r - z r) ≤ m) :
    z r - m ≤ x r := by
  by_cases hnonneg : 0 ≤ x r - z r
  · omega
  · have hnonpos : x r - z r ≤ 0 := le_of_not_ge hnonneg
    have hcast : (Int.natAbs (x r - z r) : ℤ) ≤ m := by exact_mod_cast h
    rw [Int.ofNat_natAbs_of_nonpos hnonpos] at hcast
    omega

lemma coordinate_le_add_of_natAbs_sub_le {d : ℕ}
    (x z : LatticePoint d) (r : Fin d) (m : ℕ)
    (h : Int.natAbs (x r - z r) ≤ m) :
    x r ≤ z r + m := by
  by_cases hnonneg : 0 ≤ x r - z r
  · have hcast : (Int.natAbs (x r - z r) : ℤ) ≤ m := by exact_mod_cast h
    rw [Int.ofNat_natAbs_of_nonneg hnonneg] at hcast
    omega
  · omega

lemma coord_eq_of_l1Dist_eq_zero {d : ℕ} {x y : LatticePoint d}
    (h : l1Dist x y = 0) : x = y := by
  funext i
  have hi := natAbs_coord_le_l1Dist x y i
  rw [h] at hi
  have : x i - y i = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hi)
  exact sub_eq_zero.mp this

lemma l1Dist_eq_zero_iff {d : ℕ} {x y : LatticePoint d} :
    l1Dist x y = 0 ↔ x = y := by
  constructor
  · exact coord_eq_of_l1Dist_eq_zero
  · rintro rfl
    exact l1Dist_self x

lemma l1Dist_pos_of_ne {d : ℕ} {x y : LatticePoint d} (h : x ≠ y) :
    0 < l1Dist x y := by
  exact Nat.pos_of_ne_zero (fun hzero => h (coord_eq_of_l1Dist_eq_zero hzero))

lemma supportCard_eq_one_of_isAxisPoint {d n : ℕ} (hn : 0 < n)
    {x : LatticePoint d} (haxis : IsAxisPoint n x) :
    supportCard x = 1 := by
  classical
  rcases haxis with ⟨i, rfl | rfl⟩
  · simp [supportCard, hn.ne']
    convert Finset.card_singleton i
    ext j
    simp
  · simp [supportCard, hn.ne']
    convert Finset.card_singleton i
    ext j
    simp

lemma exists_other_nonzero_of_not_axis {d n : ℕ} (hn : 0 < n)
    (z : LatticePoint d) (hz : z ∈ sphere d n)
    (hnotAxis : ¬ IsAxisPoint n z) (p : Fin d) (hp : z p ≠ 0) :
    ∃ h : Fin d, h ≠ p ∧ z h ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hnorm : Int.natAbs (z p) = n := by
    change (∑ i, Int.natAbs (z i)) = n at hz
    rw [Finset.sum_eq_single p] at hz
    · exact hz
    · intro i _ hip
      rw [hnone i hip]
      simp
    · simp
  apply hnotAxis
  rcases Int.natAbs_eq_iff.mp hnorm with hpos | hneg
  · refine ⟨p, Or.inl ?_⟩
    funext i
    by_cases hip : i = p
    · subst i
      simp [hpos]
    · simp [hip, hnone i hip]
  · refine ⟨p, Or.inr ?_⟩
    funext i
    by_cases hip : i = p
    · subst i
      simp [hneg]
    · simp [hip, hnone i hip]

end DisjointPaths
