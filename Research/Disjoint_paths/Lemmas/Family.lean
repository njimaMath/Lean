import Disjoint_paths.Lemmas.Reflection

/-!
# Properties of a complete path family

This module packages the conclusion shared by all geometric cases.  Keeping
the two index types abstract makes it possible to normalize lattice points by
reflection before identifying the resulting finite index types with the path
counts in the main theorem.
-/

namespace DisjointPaths

noncomputable section

def FamilyProperties {d n : ℕ} (δ : ℝ)
    (xInner xOuter : LatticePoint d) {α β : Type*}
    (paths : α ⊕ β → LatticePath d) : Prop :=
  (∀ i : α, (paths (Sum.inl i)).start = xInner) ∧
  (∀ i : β, (paths (Sum.inr i)).start = xOuter) ∧
  (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
  (∀ i, ∀ x ∈ (paths i).vertices,
    x ∈ sphere d n ∪ sphere d (n + 1)) ∧
  (∀ i,
    ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
    ((paths i).edgeLength : ℤ) ≤
      ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
  (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
    δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ))

theorem familyProperties_reflect {d n : ℕ} (δ : ℝ)
    (s : Fin d → ℤ) (hs : ∀ i, Int.natAbs (s i) = 1)
    (xInner xOuter : LatticePoint d) {α β : Type*}
    (paths : α ⊕ β → LatticePath d)
    (hpaths : FamilyProperties (n := n) δ xInner xOuter paths) :
    FamilyProperties (n := n) δ (reflect s xInner) (reflect s xOuter)
      (fun i ↦ (paths i).reflect hs) := by
  rcases hpaths with
    ⟨hstartInner, hstartOuter, hedges, hspheres, hlength, hseparation⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [hstartInner i]
  · intro i
    simp [hstartOuter i]
  · intro i j hij
    exact (LatticePath.edgeDisjoint_reflect_iff hs (paths i) (paths j)).mpr
      (hedges i j hij)
  · intro i x hx
    have hx' : reflect s x ∈ (paths i).vertices :=
      (LatticePath.mem_vertices_reflect_iff hs (paths i) x).mp hx
    rcases hspheres i (reflect s x) hx' with hxInner | hxOuter
    · exact Or.inl ((reflect_mem_sphere_iff hs).mp hxInner)
    · exact Or.inr ((reflect_mem_sphere_iff hs).mp hxOuter)
  · intro i
    simpa using hlength i
  · intro i j hij x hx
    have hx' : reflect s x ∈ (paths j).vertices :=
      (LatticePath.mem_vertices_reflect_iff hs (paths j) x).mp hx
    have hfar := hseparation i j hij (reflect s x) hx'
    have hdist :
        l1Dist (reflect s (paths i).finish) x =
          l1Dist (paths i).finish (reflect s x) := by
      calc
        l1Dist (reflect s (paths i).finish) x =
            l1Dist (reflect s (paths i).finish) (reflect s (reflect s x)) := by
              rw [reflect_reflect hs]
        _ = l1Dist (paths i).finish (reflect s x) :=
          l1Dist_reflect hs (paths i).finish (reflect s x)
    simpa only [LatticePath.finish_reflect, hdist] using hfar

end

end DisjointPaths
