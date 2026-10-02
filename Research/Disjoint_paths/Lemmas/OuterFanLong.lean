import Disjoint_paths.Lemmas.InwardAlternating
import Disjoint_paths.Lemmas.Fan

/-!
# Outer fan when all private coordinates are long

This is the direct outer analogue of the ordinary inner fan.  Every private
coordinate is decreased while a common coordinate is used for outward moves.
-/

namespace DisjointPaths

def LongOuterIndex {d : ℕ} (y : LatticePoint d) (p : Fin d) (m : ℕ) :=
  {i : Fin d // i ≠ p ∧ (m : ℤ) ≤ coordinateSign (y i) * y i}

def longOuterFanPath {d : ℕ} (y : LatticePoint d)
    (p : Fin d) (sp : ℤ) (hsp : Int.natAbs sp = 1)
    (m : ℕ) (q : LongOuterIndex y p m) : LatticePath d :=
  inwardAlternatingPath y q.1 (coordinateSign (y q.1)) p sp q.2.1
    (natAbs_coordinateSign (y q.1)) hsp m

@[simp] lemma longOuterFanPath_start {d : ℕ} (y : LatticePoint d)
    (p : Fin d) (sp : ℤ) (hsp : Int.natAbs sp = 1)
    (m : ℕ) (q : LongOuterIndex y p m) :
    (longOuterFanPath y p sp hsp m q).start = y := by
  simp [longOuterFanPath]

@[simp] lemma longOuterFanPath_edgeLength {d : ℕ} (y : LatticePoint d)
    (p : Fin d) (sp : ℤ) (hsp : Int.natAbs sp = 1)
    (m : ℕ) (q : LongOuterIndex y p m) :
    (longOuterFanPath y p sp hsp m q).edgeLength = 2 * m := by
  simp [longOuterFanPath]

lemma longOuterFanPath_vertices_on_two_spheres {d n : ℕ}
    (y : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    (hy : y ∈ sphere d (n + 1)) (houtward : 0 ≤ sp * y p)
    (q : LongOuterIndex y p m) :
    ∀ x ∈ (longOuterFanPath y p sp hsp m q).vertices,
      x ∈ sphere d n ∪ sphere d (n + 1) := by
  exact LatticePath.inwardAlternatingPath_vertices_on_two_spheres
    y q.1 (coordinateSign (y q.1)) p sp q.2.1
    (natAbs_coordinateSign (y q.1)) hsp m hy q.2.2 houtward

lemma longOuterFanPath_coordinate_lower_bound {d : ℕ}
    (y : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ) (q : LongOuterIndex y p m)
    (x : LatticePoint d) (hx : x ∈ (longOuterFanPath y p sp hsp m q).vertices)
    (r : Fin d) :
    y r - m ≤ x r := by
  apply coordinate_sub_le_of_natAbs_sub_le x y r m
  exact LatticePath.inwardAlternatingPath_coordinate_displacement_le
    y q.1 (coordinateSign (y q.1)) p sp q.2.1
    (natAbs_coordinateSign _) hsp m x hx r

lemma longOuterFanPath_coordinate_upper_bound {d : ℕ}
    (y : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ) (q : LongOuterIndex y p m)
    (x : LatticePoint d) (hx : x ∈ (longOuterFanPath y p sp hsp m q).vertices)
    (r : Fin d) :
    x r ≤ y r + m := by
  apply coordinate_le_add_of_natAbs_sub_le x y r m
  exact LatticePath.inwardAlternatingPath_coordinate_displacement_le
    y q.1 (coordinateSign (y q.1)) p sp q.2.1
    (natAbs_coordinateSign _) hsp m x hx r

private lemma longOuterDirections_distinct {d : ℕ} {y : LatticePoint d}
    {p : Fin d} {m : ℕ} {q r : LongOuterIndex y p m} (hqr : q ≠ r) :
    q.1 ≠ r.1 ∨
      -coordinateSign (y q.1) ≠ -coordinateSign (y r.1) := by
  left
  intro h
  apply hqr
  exact Subtype.ext h

lemma longOuterFanPath_edgeDisjoint {d : ℕ}
    (y : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ)
    {q r : LongOuterIndex y p m} (hqr : q ≠ r) :
    Disjoint (longOuterFanPath y p sp hsp m q).edgeSet
      (longOuterFanPath y p sp hsp m r).edgeSet := by
  unfold longOuterFanPath inwardAlternatingPath
  exact alternatingPaths_edgeDisjoint_of_distinct y p (-sp)
    q.1 r.1 (-coordinateSign (y q.1)) (-coordinateSign (y r.1))
    q.2.1 r.2.1 (by simp) (by simp) (by simpa using hsp)
    (longOuterDirections_distinct hqr) m

lemma longOuterFanPath_endpoint_far {d : ℕ}
    (y : LatticePoint d) (p : Fin d) (sp : ℤ)
    (hsp : Int.natAbs sp = 1) (m : ℕ) (rsep : ℝ)
    (hrsep : rsep ≤ (m : ℝ))
    {q r : LongOuterIndex y p m} (hqr : q ≠ r) :
    ∀ x ∈ (longOuterFanPath y p sp hsp m r).vertices,
      rsep ≤ (l1Dist (longOuterFanPath y p sp hsp m q).finish x : ℝ) := by
  unfold longOuterFanPath inwardAlternatingPath
  exact alternatingPath_endpoint_far_of_distinct y p (-sp)
    q.1 r.1 (-coordinateSign (y q.1)) (-coordinateSign (y r.1))
    q.2.1 r.2.1 (by simp) (by simp) (by simpa using hsp)
    (longOuterDirections_distinct hqr) m rsep hrsep

end DisjointPaths
