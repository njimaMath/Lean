import Disjoint_paths.Lemmas.Case1.Basic
import Disjoint_paths.Lemmas.InnerFan
import Disjoint_paths.Lemmas.OuterPrivateFamily

/-!
# Complete families separated by a starting-coordinate gap

The inner fan and the continued outer family each remain within one path
scale of their starting points.  A gap of three scales therefore leaves one
full scale between the two families.
-/

namespace DisjointPaths

noncomputable section

theorem exists_nonAxis_paths_of_inner_coordinate_gap
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (houterNonAxis : ¬ IsAxisPoint (n + 1) xOuter)
    (r : Fin d)
    (hcoordinate : 3 * (pathScale δ n : ℤ) ≤ xInner r - xOuter r) :
    ∃ paths : PathIndex n xInner xOuter → LatticePath d,
      (∀ i : Fin (pathCountAtInner n xInner),
        (paths (Sum.inl i)).start = xInner) ∧
      (∀ i : Fin (pathCountAtOuter n xOuter),
        (paths (Sum.inr i)).start = xOuter) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤
          (l1Dist (paths i).finish x : ℝ)) := by
  let m := pathScale δ n
  obtain ⟨innerPaths, hinnerStart, hinnerEdges, hinnerSphere, hinnerLength,
    hinnerFar, hinnerBounds⟩ :=
    exists_innerFan hd δ hδpos hδ hn hscale xInner hinner
  obtain ⟨outerPaths, houterStart, houterEdges, houterSphere, houterLength,
    houterFar, houterBounds⟩ :=
    exists_nonAxis_outerPrivateFamily hd δ hδpos hδ hn hscale
      xOuter houter houterNonAxis
  apply combine_path_families_of_coordinate_gap xInner xOuter
    innerPaths outerPaths hinnerStart houterStart hinnerEdges houterEdges
    hinnerSphere houterSphere
    ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋
    hinnerLength houterLength (δ ^ 3 * (n + 1 : ℝ))
    hinnerFar houterFar r (xInner r - (m : ℤ))
    (xOuter r + (m : ℤ)) m
  · exact separation_radius_le_pathScale hd hδpos hδ n hscale
  · positivity
  · change xOuter r + (m : ℤ) < xInner r - m
    have hm : 0 < m := by
      have : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
      omega
    omega
  · change (m : ℤ) ≤
      (xInner r - m) - (xOuter r + m)
    omega
  · intro i x hx
    exact (hinnerBounds i x hx r).1
  · intro i x hx
    exact (houterBounds i x hx r).2

theorem exists_nonAxis_paths_of_outer_coordinate_gap
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (houterNonAxis : ¬ IsAxisPoint (n + 1) xOuter)
    (r : Fin d)
    (hcoordinate : 3 * (pathScale δ n : ℤ) ≤ xOuter r - xInner r) :
    ∃ paths : PathIndex n xInner xOuter → LatticePath d,
      (∀ i : Fin (pathCountAtInner n xInner),
        (paths (Sum.inl i)).start = xInner) ∧
      (∀ i : Fin (pathCountAtOuter n xOuter),
        (paths (Sum.inr i)).start = xOuter) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤
          (l1Dist (paths i).finish x : ℝ)) := by
  let m := pathScale δ n
  obtain ⟨innerPaths, hinnerStart, hinnerEdges, hinnerSphere, hinnerLength,
    hinnerFar, hinnerBounds⟩ :=
    exists_innerFan hd δ hδpos hδ hn hscale xInner hinner
  obtain ⟨outerPaths, houterStart, houterEdges, houterSphere, houterLength,
    houterFar, houterBounds⟩ :=
    exists_nonAxis_outerPrivateFamily hd δ hδpos hδ hn hscale
      xOuter houter houterNonAxis
  apply combine_path_families_of_reverse_coordinate_gap xInner xOuter
    innerPaths outerPaths hinnerStart houterStart hinnerEdges houterEdges
    hinnerSphere houterSphere
    ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋
    hinnerLength houterLength (δ ^ 3 * (n + 1 : ℝ))
    hinnerFar houterFar r (xInner r + (m : ℤ))
    (xOuter r - (m : ℤ)) m
  · exact separation_radius_le_pathScale hd hδpos hδ n hscale
  · positivity
  · change xInner r + (m : ℤ) < xOuter r - m
    have hm : 0 < m := by
      have : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
      omega
    omega
  · change (m : ℤ) ≤
      (xOuter r - m) - (xInner r + m)
    omega
  · intro i x hx
    exact (hinnerBounds i x hx r).2
  · intro i x hx
    exact (houterBounds i x hx r).1

end

end DisjointPaths
