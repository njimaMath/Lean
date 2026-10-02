import Disjoint_paths.Lemmas.Separation

/-!
# Combining two separated path families

The geometric cases construct the paths based at the inner and outer points
separately.  This lemma records the final, purely formal, assembly when one
coordinate separates the two families.
-/

namespace DisjointPaths

noncomputable section

theorem combine_path_families_of_coordinate_gap
    {d n a b : ℕ} (xInner xOuter : LatticePoint d)
    (innerPaths : Fin a → LatticePath d)
    (outerPaths : Fin b → LatticePath d)
    (hinnerStart : ∀ i, (innerPaths i).start = xInner)
    (houterStart : ∀ j, (outerPaths j).start = xOuter)
    (hinnerEdges : ∀ i j, i ≠ j →
      Disjoint (innerPaths i).edgeSet (innerPaths j).edgeSet)
    (houterEdges : ∀ i j, i ≠ j →
      Disjoint (outerPaths i).edgeSet (outerPaths j).edgeSet)
    (hinnerSphere : ∀ i, ∀ z ∈ (innerPaths i).vertices,
      z ∈ sphere d n ∪ sphere d (n + 1))
    (houterSphere : ∀ j, ∀ z ∈ (outerPaths j).vertices,
      z ∈ sphere d n ∪ sphere d (n + 1))
    (lo hi : ℤ)
    (hinnerLength : ∀ i, lo ≤ ((innerPaths i).edgeLength : ℤ) ∧
      ((innerPaths i).edgeLength : ℤ) ≤ hi)
    (houterLength : ∀ j, lo ≤ ((outerPaths j).edgeLength : ℤ) ∧
      ((outerPaths j).edgeLength : ℤ) ≤ hi)
    (rsep : ℝ)
    (hinnerFar : ∀ i j, i ≠ j → ∀ z ∈ (innerPaths j).vertices,
      rsep ≤ (l1Dist (innerPaths i).finish z : ℝ))
    (houterFar : ∀ i j, i ≠ j → ∀ z ∈ (outerPaths j).vertices,
      rsep ≤ (l1Dist (outerPaths i).finish z : ℝ))
    (r : Fin d) (α β k : ℤ)
    (hrk : rsep ≤ (k : ℝ)) (hk : 0 ≤ k) (hstrict : β < α)
    (hgap : k ≤ α - β)
    (hinnerCoord : ∀ i, ∀ z ∈ (innerPaths i).vertices, α ≤ z r)
    (houterCoord : ∀ j, ∀ z ∈ (outerPaths j).vertices, z r ≤ β) :
    ∃ paths : Fin a ⊕ Fin b → LatticePath d,
      (∀ i, (paths (Sum.inl i)).start = xInner) ∧
      (∀ j, (paths (Sum.inr j)).start = xOuter) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ z ∈ (paths i).vertices,
        z ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i, lo ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤ hi) ∧
      (∀ i j, i ≠ j → ∀ z ∈ (paths j).vertices,
      rsep ≤ (l1Dist (paths i).finish z : ℝ)) := by
  let paths : Fin a ⊕ Fin b → LatticePath d := Sum.elim innerPaths outerPaths
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hinnerStart i
  · intro j
    exact houterStart j
  · intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · apply hinnerEdges i j
      intro h
      apply hij
      cases h
      rfl
    · exact edgeDisjoint_of_coordinate_gap (innerPaths i) (outerPaths j) r α β
        (hinnerCoord i) (houterCoord j) hstrict
    · exact (edgeDisjoint_of_coordinate_gap (innerPaths j) (outerPaths i) r α β
        (hinnerCoord j) (houterCoord i) hstrict).symm
    · apply houterEdges i j
      intro h
      apply hij
      cases h
      rfl
  · intro i z hz
    rcases i with i | i
    · exact hinnerSphere i z hz
    · exact houterSphere i z hz
  · intro i
    rcases i with i | i
    · exact hinnerLength i
    · exact houterLength i
  · intro i j hij z hz
    rcases i with i | i <;> rcases j with j | j
    · exact hinnerFar i j (by
        intro h
        apply hij
        cases h
        rfl) z hz
    · exact endpoint_far_from_vertices_of_coordinate_gap
        (innerPaths i) (outerPaths j) r rsep α β k hrk hk
        (hinnerCoord i (innerPaths i).finish (LatticePath.finish_mem_vertices _))
        (houterCoord j) hgap z hz
    · exact endpoint_far_from_vertices_of_reverse_coordinate_gap
        (outerPaths i) (innerPaths j) r rsep β α k hrk hk
        (houterCoord i (outerPaths i).finish (LatticePath.finish_mem_vertices _))
        (hinnerCoord j) hgap z hz
    · exact houterFar i j (by
        intro h
        apply hij
        cases h
        rfl) z hz

theorem combine_path_families_of_reverse_coordinate_gap
    {d n a b : ℕ} (xInner xOuter : LatticePoint d)
    (innerPaths : Fin a → LatticePath d) (outerPaths : Fin b → LatticePath d)
    (hinnerStart : ∀ i, (innerPaths i).start = xInner)
    (houterStart : ∀ j, (outerPaths j).start = xOuter)
    (hinnerEdges : ∀ i j, i ≠ j → Disjoint (innerPaths i).edgeSet (innerPaths j).edgeSet)
    (houterEdges : ∀ i j, i ≠ j → Disjoint (outerPaths i).edgeSet (outerPaths j).edgeSet)
    (hinnerSphere : ∀ i, ∀ z ∈ (innerPaths i).vertices, z ∈ sphere d n ∪ sphere d (n + 1))
    (houterSphere : ∀ j, ∀ z ∈ (outerPaths j).vertices, z ∈ sphere d n ∪ sphere d (n + 1))
    (lo hi : ℤ)
    (hinnerLength : ∀ i, lo ≤ ((innerPaths i).edgeLength : ℤ) ∧ ((innerPaths i).edgeLength : ℤ) ≤ hi)
    (houterLength : ∀ j, lo ≤ ((outerPaths j).edgeLength : ℤ) ∧ ((outerPaths j).edgeLength : ℤ) ≤ hi)
    (rsep : ℝ)
    (hinnerFar : ∀ i j, i ≠ j → ∀ z ∈ (innerPaths j).vertices, rsep ≤ (l1Dist (innerPaths i).finish z : ℝ))
    (houterFar : ∀ i j, i ≠ j → ∀ z ∈ (outerPaths j).vertices, rsep ≤ (l1Dist (outerPaths i).finish z : ℝ))
    (r : Fin d) (α β k : ℤ)
    (hrk : rsep ≤ (k : ℝ)) (hk : 0 ≤ k) (hstrict : α < β) (hgap : k ≤ β - α)
    (hinnerCoord : ∀ i, ∀ z ∈ (innerPaths i).vertices, z r ≤ α)
    (houterCoord : ∀ j, ∀ z ∈ (outerPaths j).vertices, β ≤ z r) :
    ∃ paths : Fin a ⊕ Fin b → LatticePath d,
      (∀ i, (paths (Sum.inl i)).start = xInner) ∧
      (∀ j, (paths (Sum.inr j)).start = xOuter) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ z ∈ (paths i).vertices, z ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i, lo ≤ ((paths i).edgeLength : ℤ) ∧ ((paths i).edgeLength : ℤ) ≤ hi) ∧
      (∀ i j, i ≠ j → ∀ z ∈ (paths j).vertices,
        rsep ≤ (l1Dist (paths i).finish z : ℝ)) := by
  let paths : Fin a ⊕ Fin b → LatticePath d := Sum.elim innerPaths outerPaths
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact hinnerStart i
  · intro j; exact houterStart j
  · intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · apply hinnerEdges i j; intro h; apply hij; cases h; rfl
    · exact (edgeDisjoint_of_coordinate_gap (outerPaths j) (innerPaths i) r β α
        (houterCoord j) (hinnerCoord i) hstrict).symm
    · exact edgeDisjoint_of_coordinate_gap (outerPaths i) (innerPaths j) r β α
        (houterCoord i) (hinnerCoord j) hstrict
    · apply houterEdges i j; intro h; apply hij; cases h; rfl
  · intro i z hz
    rcases i with i | i
    · exact hinnerSphere i z hz
    · exact houterSphere i z hz
  · intro i; rcases i with i | i
    · exact hinnerLength i
    · exact houterLength i
  · intro i j hij z hz
    rcases i with i | i <;> rcases j with j | j
    · exact hinnerFar i j (by intro h; apply hij; cases h; rfl) z hz
    · exact endpoint_far_from_vertices_of_reverse_coordinate_gap
        (innerPaths i) (outerPaths j) r rsep α β k hrk hk
        (hinnerCoord i (innerPaths i).finish (LatticePath.finish_mem_vertices _))
        (houterCoord j) hgap z hz
    · exact endpoint_far_from_vertices_of_coordinate_gap
        (outerPaths i) (innerPaths j) r rsep β α k hrk hk
        (houterCoord i (outerPaths i).finish (LatticePath.finish_mem_vertices _))
        (hinnerCoord j) hgap z hz
    · exact houterFar i j (by intro h; apply hij; cases h; rfl) z hz

theorem combine_path_families_of_opposed_endpoint_growth
    {d n a b : ℕ} (xInner xOuter : LatticePoint d)
    (innerPaths : Fin a → LatticePath d) (outerPaths : Fin b → LatticePath d)
    (hinnerStart : ∀ i, (innerPaths i).start = xInner)
    (houterStart : ∀ j, (outerPaths j).start = xOuter)
    (hinnerEdges : ∀ i j, i ≠ j → Disjoint (innerPaths i).edgeSet (innerPaths j).edgeSet)
    (houterEdges : ∀ i j, i ≠ j → Disjoint (outerPaths i).edgeSet (outerPaths j).edgeSet)
    (hinnerSphere : ∀ i, ∀ z ∈ (innerPaths i).vertices, z ∈ sphere d n ∪ sphere d (n + 1))
    (houterSphere : ∀ j, ∀ z ∈ (outerPaths j).vertices, z ∈ sphere d n ∪ sphere d (n + 1))
    (lo hi : ℤ)
    (hinnerLength : ∀ i, lo ≤ ((innerPaths i).edgeLength : ℤ) ∧ ((innerPaths i).edgeLength : ℤ) ≤ hi)
    (houterLength : ∀ j, lo ≤ ((outerPaths j).edgeLength : ℤ) ∧ ((outerPaths j).edgeLength : ℤ) ≤ hi)
    (rsep : ℝ)
    (hinnerFar : ∀ i j, i ≠ j → ∀ z ∈ (innerPaths j).vertices, rsep ≤ (l1Dist (innerPaths i).finish z : ℝ))
    (houterFar : ∀ i j, i ≠ j → ∀ z ∈ (outerPaths j).vertices, rsep ≤ (l1Dist (outerPaths i).finish z : ℝ))
    (r : Fin d) (α β k : ℤ) (hrk : rsep ≤ (k : ℝ)) (hk : 0 ≤ k)
    (hstrict : β < α)
    (hinnerCoord : ∀ i, ∀ z ∈ (innerPaths i).vertices, α ≤ z r)
    (houterCoord : ∀ j, ∀ z ∈ (outerPaths j).vertices, z r ≤ β)
    (hinnerFinish : ∀ i, α + k ≤ (innerPaths i).finish r)
    (houterFinish : ∀ j, (outerPaths j).finish r ≤ β - k) :
    ∃ paths : Fin a ⊕ Fin b → LatticePath d,
      (∀ i, (paths (Sum.inl i)).start = xInner) ∧
      (∀ j, (paths (Sum.inr j)).start = xOuter) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ z ∈ (paths i).vertices, z ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i, lo ≤ ((paths i).edgeLength : ℤ) ∧ ((paths i).edgeLength : ℤ) ≤ hi) ∧
      (∀ i j, i ≠ j → ∀ z ∈ (paths j).vertices,
        rsep ≤ (l1Dist (paths i).finish z : ℝ)) := by
  let paths : Fin a ⊕ Fin b → LatticePath d := Sum.elim innerPaths outerPaths
  refine ⟨paths, hinnerStart, houterStart, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact hinnerEdges i j (by intro h; apply hij; cases h; rfl)
    · exact edgeDisjoint_of_coordinate_gap (innerPaths i) (outerPaths j) r α β
        (hinnerCoord i) (houterCoord j) hstrict
    · exact (edgeDisjoint_of_coordinate_gap (innerPaths j) (outerPaths i) r α β
        (hinnerCoord j) (houterCoord i) hstrict).symm
    · exact houterEdges i j (by intro h; apply hij; cases h; rfl)
  · intro i z hz
    rcases i with i | i
    · exact hinnerSphere i z hz
    · exact houterSphere i z hz
  · intro i
    rcases i with i | i
    · exact hinnerLength i
    · exact houterLength i
  · intro i j hij z hz
    rcases i with i | i <;> rcases j with j | j
    · exact hinnerFar i j (by intro h; apply hij; cases h; rfl) z hz
    · exact endpoint_far_from_vertices_of_coordinate_gap
        (innerPaths i) (outerPaths j) r rsep (α + k) β k hrk hk
        (hinnerFinish i) (houterCoord j) (by omega) z hz
    · exact endpoint_far_from_vertices_of_reverse_coordinate_gap
        (outerPaths i) (innerPaths j) r rsep (β - k) α k hrk hk
        (houterFinish i) (hinnerCoord j) (by omega) z hz
    · exact houterFar i j (by intro h; apply hij; cases h; rfl) z hz

end

end DisjointPaths
