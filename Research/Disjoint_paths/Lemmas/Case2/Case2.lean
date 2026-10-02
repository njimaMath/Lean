import Disjoint_paths.Lemmas.Case1.Basic
import Disjoint_paths.Lemmas.InnerFan
import Disjoint_paths.Lemmas.OuterFan

/-!
# Case 2: an outer axis point separated from the inner fan
-/

namespace DisjointPaths

noncomputable section

theorem case2_of_separated_axis_outer_fan
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (haxis : IsAxisPoint (n + 1) xOuter)
    (r : Fin d) (k : ℤ)
    (hrk : δ ^ 3 * (n + 1 : ℝ) ≤ (k : ℝ)) (hk : 0 ≤ k)
    (hstrict : xOuter r + (pathScale δ n : ℤ) <
      xInner r - (pathScale δ n : ℤ))
    (hgap : k ≤ (xInner r - (pathScale δ n : ℤ)) -
      (xOuter r + (pathScale δ n : ℤ))) :
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
        ((paths i).edgeLength : ℤ) ≤ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) := by
  obtain ⟨innerPaths, hinnerStart, hinnerEdges, hinnerSphere, hinnerLength,
    hinnerFar, hinnerBounds⟩ :=
    exists_innerFan hd δ hδpos hδ hn hscale xInner hinner
  obtain ⟨outerPaths, houterStart, houterEdges, houterSphere, houterLength,
    houterFar, houterBounds⟩ :=
    exists_axis_outerFan hd δ hδpos hδ hn hscale xOuter houter haxis
  exact combine_path_families_of_coordinate_gap xInner xOuter innerPaths outerPaths
    hinnerStart houterStart hinnerEdges houterEdges hinnerSphere houterSphere
    ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋ hinnerLength houterLength
    (δ ^ 3 * (n + 1 : ℝ)) hinnerFar houterFar r
    (xInner r - (pathScale δ n : ℤ)) (xOuter r + (pathScale δ n : ℤ)) k
    hrk hk hstrict hgap
    (fun i x hx => (hinnerBounds i x hx r).1)
    (fun i x hx => (houterBounds i x hx r).2)

theorem case2_axis_outer_large_gap
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (haxis : IsAxisPoint (n + 1) xOuter) (r : Fin d)
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
        ((paths i).edgeLength : ℤ) ≤ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) := by
  let m := pathScale δ n
  have hm : 12 ≤ m :=
    (Nat.le_floor_iff (by positivity)).mpr hscale
  apply case2_of_separated_axis_outer_fan hd δ hδpos hδ hn hscale
    xInner xOuter hinner houter haxis r m
  · exact separation_radius_le_pathScale hd hδpos hδ n hscale
  · exact_mod_cast (Nat.zero_le m)
  · change xOuter r + (m : ℤ) < xInner r - m
    omega
  · change (m : ℤ) ≤ (xInner r - m) - (xOuter r + m)
    omega

theorem case2_axis_outer_reverse_large_gap
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (haxis : IsAxisPoint (n + 1) xOuter) (r : Fin d)
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
        ((paths i).edgeLength : ℤ) ≤ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) := by
  let m := pathScale δ n
  obtain ⟨innerPaths, hinnerStart, hinnerEdges, hinnerSphere, hinnerLength,
    hinnerFar, hinnerBounds⟩ :=
    exists_innerFan hd δ hδpos hδ hn hscale xInner hinner
  obtain ⟨outerPaths, houterStart, houterEdges, houterSphere, houterLength,
    houterFar, houterBounds⟩ :=
    exists_axis_outerFan hd δ hδpos hδ hn hscale xOuter houter haxis
  apply combine_path_families_of_reverse_coordinate_gap xInner xOuter
    innerPaths outerPaths hinnerStart houterStart hinnerEdges houterEdges
    hinnerSphere houterSphere
    ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋
    hinnerLength houterLength (δ ^ 3 * (n + 1 : ℝ))
    hinnerFar houterFar r (xInner r + (m : ℤ))
    (xOuter r - (m : ℤ)) m
  · exact separation_radius_le_pathScale hd hδpos hδ n hscale
  · positivity
  · have hm : 0 < m := by
      have : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
      omega
    omega
  · omega
  · intro i x hx
    exact (hinnerBounds i x hx r).2
  · intro i x hx
    exact (houterBounds i x hx r).1

end

end DisjointPaths
