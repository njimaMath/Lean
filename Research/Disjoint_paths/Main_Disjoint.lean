import Disjoint_paths.Lemmas.Definitions
import Disjoint_paths.Lemmas.Main_Proof

/-!
# Edge-disjoint paths on two consecutive lattice spheres

The implementation objects are provided by `Lemmas.Definitions`. This file
also declares a theorem-facing copy of that API under distinct names:

* `MainLatticePoint`, `mainL1Norm`, `mainL1Dist`, and `mainSphere`;
* `MainNearestNeighbor` and `MainLatticePath`, together with its endpoint,
  length, and edge-set definitions;
* `mainSupportCard`, `MainIsAxisPoint`, `mainPathCountAtInner`,
  `mainPathCountAtOuter`, and `MainPathIndex`.

Each new declaration reduces to its implementation counterpart. The proof is
provided by `Lemmas.Main_Proof` and transported across these definitions.
-/

namespace DisjointPaths

noncomputable section

/-- A lattice point as named in the public theorem interface. -/
abbrev MainLatticePoint (d : ℕ) := LatticePoint d

/-- The `ℓ¹` norm used in the public theorem interface. -/
def mainL1Norm {d : ℕ} (x : MainLatticePoint d) : ℕ :=
  l1Norm x

/-- The `ℓ¹` distance used in the public theorem interface. -/
def mainL1Dist {d : ℕ} (x y : MainLatticePoint d) : ℕ :=
  l1Dist x y

/-- The sphere of radius `n` in the public theorem interface. -/
def mainSphere (d n : ℕ) : Set (MainLatticePoint d) :=
  sphere d n

/-- The nearest-neighbor relation in the public theorem interface. -/
def MainNearestNeighbor {d : ℕ}
    (x y : MainLatticePoint d) : Prop :=
  NearestNeighbor x y

/-- Paths used by the public theorem interface. -/
abbrev MainLatticePath (d : ℕ) := LatticePath d

namespace MainLatticePath

/-- The first vertex of a path. -/
def start {d : ℕ} (p : MainLatticePath d) : MainLatticePoint d :=
  LatticePath.start p

/-- The last vertex of a path. -/
def finish {d : ℕ} (p : MainLatticePath d) : MainLatticePoint d :=
  LatticePath.finish p

/-- The number of edges in a path. -/
def edgeLength {d : ℕ} (p : MainLatticePath d) : ℕ :=
  LatticePath.edgeLength p

/-- The oriented edges traversed by a path. -/
def orientedEdges {d : ℕ} (p : MainLatticePath d) :
    Set (MainLatticePoint d × MainLatticePoint d) :=
  LatticePath.orientedEdges p

/-- The unoriented edge set of a path. -/
def edgeSet {d : ℕ} (p : MainLatticePath d) :
    Set (MainLatticePoint d × MainLatticePoint d) :=
  LatticePath.edgeSet p

end MainLatticePath

/-- The number of nonzero coordinates of a lattice point. -/
def mainSupportCard {d : ℕ} (x : MainLatticePoint d) : ℕ :=
  supportCard x

/-- The signed coordinate-axis points on the sphere of radius `n`. -/
def MainIsAxisPoint {d : ℕ} (n : ℕ) (x : MainLatticePoint d) : Prop :=
  IsAxisPoint n x

/-- The number of paths requested from the inner sphere point. -/
def mainPathCountAtInner {d : ℕ} (n : ℕ) (x : MainLatticePoint d) : ℕ :=
  pathCountAtInner n x

/-- The number of paths requested from the outer sphere point. -/
def mainPathCountAtOuter {d : ℕ} (n : ℕ) (x : MainLatticePoint d) : ℕ :=
  pathCountAtOuter n x

/-- The combined index type for paths from the inner and outer points. -/
abbrev MainPathIndex {d : ℕ} (n : ℕ)
    (xInner xOuter : MainLatticePoint d) :=
  Fin (mainPathCountAtInner n xInner) ⊕ Fin (mainPathCountAtOuter n xOuter)

/--
Existence of the prescribed edge-disjoint paths on two consecutive `ℓ¹`
lattice spheres.
-/
theorem exists_edgeDisjoint_paths_on_consecutive_spheres
    {d : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (xInner xOuter : MainLatticePoint d),
      xInner ∈ mainSphere d n →
      xOuter ∈ mainSphere d (n + 1) →
      ∃ paths : MainPathIndex n xInner xOuter → MainLatticePath d,
        (∀ i : Fin (mainPathCountAtInner n xInner),
          MainLatticePath.start (paths (Sum.inl i)) = xInner) ∧
        (∀ i : Fin (mainPathCountAtOuter n xOuter),
          MainLatticePath.start (paths (Sum.inr i)) = xOuter) ∧
        (∀ i j, i ≠ j →
          Disjoint (MainLatticePath.edgeSet (paths i))
            (MainLatticePath.edgeSet (paths j))) ∧
        (∀ i, ∀ x ∈ (paths i).vertices,
          x ∈ mainSphere d n ∪ mainSphere d (n + 1)) ∧
        (∀ i,
          ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤
              (MainLatticePath.edgeLength (paths i) : ℤ) ∧
          (MainLatticePath.edgeLength (paths i) : ℤ) ≤
            ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
        (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
          δ ^ 3 * (n + 1 : ℝ) ≤
            (mainL1Dist (MainLatticePath.finish (paths i)) x : ℝ)) := by
  change ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (xInner xOuter : LatticePoint d),
    xInner ∈ sphere d n →
    xOuter ∈ sphere d (n + 1) →
    ∃ paths : PathIndex n xInner xOuter → LatticePath d,
      (∀ i : Fin (pathCountAtInner n xInner),
        (paths (Sum.inl i)).start = xInner) ∧
      (∀ i : Fin (pathCountAtOuter n xOuter),
        (paths (Sum.inr i)).start = xOuter) ∧
      (∀ i j, i ≠ j →
        Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤
          (l1Dist (paths i).finish x : ℝ))
  exact exists_edgeDisjoint_paths_on_consecutive_spheres_proof hd δ hδpos hδ

end

end DisjointPaths
