import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Definitions for paths on consecutive lattice spheres

This module contains the objects occurring in the final theorem.  It is kept
separate from the theorem proof so that geometric helper modules do not create
an import cycle through `Main_Disjoint`.
-/

namespace DisjointPaths

noncomputable section

local instance classicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev LatticePoint (d : ℕ) := Fin d → ℤ

def l1Norm {d : ℕ} (x : LatticePoint d) : ℕ :=
  ∑ i, Int.natAbs (x i)

def l1Dist {d : ℕ} (x y : LatticePoint d) : ℕ :=
  l1Norm (fun i ↦ x i - y i)

def sphere (d n : ℕ) : Set (LatticePoint d) :=
  {x | l1Norm x = n}

def NearestNeighbor {d : ℕ} (x y : LatticePoint d) : Prop :=
  l1Dist x y = 1

structure LatticePath (d : ℕ) where
  vertices : List (LatticePoint d)
  nonempty : vertices ≠ []
  adjacent : vertices.IsChain NearestNeighbor
  nodup : vertices.Nodup

namespace LatticePath

def start {d : ℕ} (p : LatticePath d) : LatticePoint d :=
  p.vertices.head p.nonempty

def finish {d : ℕ} (p : LatticePath d) : LatticePoint d :=
  p.vertices.getLast p.nonempty

def edgeLength {d : ℕ} (p : LatticePath d) : ℕ :=
  p.vertices.length - 1

def orientedEdges {d : ℕ} (p : LatticePath d) : Set (LatticePoint d × LatticePoint d) :=
  {e | e ∈ p.vertices.zip p.vertices.tail}

def edgeSet {d : ℕ} (p : LatticePath d) : Set (LatticePoint d × LatticePoint d) :=
  {e | e ∈ p.orientedEdges ∨ e.swap ∈ p.orientedEdges}

end LatticePath

def supportCard {d : ℕ} (x : LatticePoint d) : ℕ :=
  (Finset.univ.filter fun i ↦ x i ≠ 0).card

def IsAxisPoint {d : ℕ} (n : ℕ) (x : LatticePoint d) : Prop :=
  ∃ i : Fin d,
    x = (fun j ↦ if j = i then (n : ℤ) else 0) ∨
      x = (fun j ↦ if j = i then -(n : ℤ) else 0)

def pathCountAtInner {d : ℕ} (n : ℕ) (x : LatticePoint d) : ℕ :=
  if IsAxisPoint n x then 2 * d - 3 else 2 * d - supportCard x - 1

def pathCountAtOuter {d : ℕ} (n : ℕ) (x : LatticePoint d) : ℕ :=
  if IsAxisPoint (n + 1) x then 1 else supportCard x - 1

abbrev PathIndex {d : ℕ} (n : ℕ) (xInner xOuter : LatticePoint d) :=
  Fin (pathCountAtInner n xInner) ⊕ Fin (pathCountAtOuter n xOuter)

end

end DisjointPaths
