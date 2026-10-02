import Disjoint_paths.Lemmas.Case1.Basic
import Disjoint_paths.Lemmas.InnerFan
import Disjoint_paths.Lemmas.OuterFan
import Disjoint_paths.Lemmas.ExtendedInnerFan
import Disjoint_paths.Lemmas.SeparatedOuterFamily
import Disjoint_paths.Lemmas.SeparatedPrivateFamilies
import Disjoint_paths.Lemmas.Family

/-!
# Case 1: a long-coordinate different-orthant subcase

When the two ordinary fan intervals are separated in one coordinate, their
union is an admissible family with the required combined index type.
-/

namespace DisjointPaths

noncomputable section

theorem case1_of_separated_long_fans
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (p : Fin d) (hp : xOuter p ≠ 0)
    (hall : ∀ i, i ≠ p → xOuter i ≠ 0 →
      (pathScale δ n : ℤ) ≤ coordinateSign (xOuter i) * xOuter i)
    (houterNonAxis : ¬ IsAxisPoint (n + 1) xOuter)
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
    exists_long_nonAxis_outerFan hd δ hδpos hδ hscale xOuter houter p hp hall
      houterNonAxis
  exact combine_path_families_of_coordinate_gap xInner xOuter innerPaths outerPaths
    hinnerStart houterStart hinnerEdges houterEdges hinnerSphere houterSphere
    ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋ hinnerLength houterLength
    (δ ^ 3 * (n + 1 : ℝ)) hinnerFar houterFar r
    (xInner r - (pathScale δ n : ℤ)) (xOuter r + (pathScale δ n : ℤ)) k
    hrk hk hstrict hgap
    (fun i x hx => (hinnerBounds i x hx r).1)
    (fun i x hx => (houterBounds i x hx r).2)

theorem case1_different_orthants_large_gap
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (p : Fin d) (hp : xOuter p ≠ 0)
    (hall : ∀ i, i ≠ p → xOuter i ≠ 0 →
      (pathScale δ n : ℤ) ≤ coordinateSign (xOuter i) * xOuter i)
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
        ((paths i).edgeLength : ℤ) ≤ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) := by
  let m := pathScale δ n
  have hm : 12 ≤ m :=
    (Nat.le_floor_iff (by positivity)).mpr hscale
  apply case1_of_separated_long_fans hd δ hδpos hδ hn hscale
    xInner xOuter hinner houter p hp hall houterNonAxis r m
  · exact separation_radius_le_pathScale hd hδpos hδ n hscale
  · exact_mod_cast (Nat.zero_le m)
  · change xOuter r + (m : ℤ) < xInner r - m
    omega
  · change (m : ℤ) ≤ (xInner r - m) - (xOuter r + m)
    omega

theorem case1_different_orthants_small_gap_oriented
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (houterNonAxis : ¬ IsAxisPoint (n + 1) xOuter)
    (r : Fin d) (hinnerR : 0 < xInner r) (houterR : xOuter r < 0)
    (hclose : xInner r - xOuter r < 3 * (pathScale δ n : ℤ)) :
    ∃ paths : PathIndex n xInner xOuter → LatticePath d,
      (∀ i : Fin (pathCountAtInner n xInner), (paths (Sum.inl i)).start = xInner) ∧
      (∀ i : Fin (pathCountAtOuter n xOuter), (paths (Sum.inr i)).start = xOuter) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices, x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i, ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) := by
  let m := pathScale δ n
  have hm : 0 < m := by
    have : 12 ≤ m := (Nat.le_floor_iff (by positivity)).mpr hscale
    omega
  have hstrong : 16 * d ^ 2 * m ≤ n :=
    pathScale_strong_reservoir_bound hd hn hδpos hδ
  have hd3 : d * (3 * m) ≤ n := by
    have hcoeff : d * (3 * m) ≤ 16 * d ^ 2 * m := by
      calc
        d * (3 * m) = 3 * d * m := by ring
        _ ≤ (16 * d) * d * m := by
          gcongr
          omega
        _ = 16 * d ^ 2 * m := by ring
    exact hcoeff.trans hstrong
  obtain ⟨p, hp3⟩ := exists_reservoir_coordinate
    (show 1 ≤ d by omega) xInner hinner hd3
  obtain ⟨q, hq3⟩ := exists_reservoir_coordinate
    (show 1 ≤ d by omega) xOuter houter (by omega : d * (3 * m) ≤ n + 1)
  have hpr : p ≠ r := by
    intro h
    subst p
    have hsign : coordinateSign (xInner r) = 1 := by
      simp [coordinateSign, hinnerR.le]
    rw [hsign] at hp3
    omega
  have hqr : q ≠ r := by
    intro h
    subst q
    have hsign : coordinateSign (xOuter r) = -1 := by
      simp [coordinateSign, not_le.mpr houterR]
    rw [hsign] at hq3
    omega
  have hp2 : ((2 * m : ℕ) : ℤ) ≤
      coordinateSign (xInner p) * xInner p := by
    have hcast : ((2 * m : ℕ) : ℤ) ≤ ((3 * m : ℕ) : ℤ) := by
      exact_mod_cast (show 2 * m ≤ 3 * m by omega)
    exact hcast.trans hp3
  have hqNonzero : xOuter q ≠ 0 := by
    intro h
    rw [h, coordinateSign_mul_self] at hq3
    norm_num at hq3
    omega
  obtain ⟨innerPaths, hinnerStart, hinnerEdges, hinnerSphere, hinnerLength,
      hinnerFar, hinnerHalf, hinnerFinish, _hinnerBounds⟩ :=
    exists_extended_innerFan hd δ hδpos hδ hscale xInner hinner p
      (coordinateSign (xInner p)) (natAbs_coordinateSign _) hp2 r (Ne.symm hpr)
      (ne_of_gt hinnerR)
  obtain ⟨outerPaths, houterStart, houterEdges, houterSphere, houterLength,
      houterFar, houterHalf, houterFinish⟩ :=
    exists_separated_outerFamily hd δ hδpos hδ hscale xOuter houter
      houterNonAxis q r hqr hqNonzero (ne_of_lt houterR) (by simpa [m] using hq3)
  have hinnerSign : coordinateSign (xInner r) = 1 := by
    simp [coordinateSign, hinnerR.le]
  have houterSign : coordinateSign (xOuter r) = -1 := by
    simp [coordinateSign, not_le.mpr houterR]
  apply combine_path_families_of_opposed_endpoint_growth
    xInner xOuter innerPaths outerPaths hinnerStart houterStart
    hinnerEdges houterEdges hinnerSphere houterSphere
    ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋
    hinnerLength houterLength (δ ^ 3 * (n + 1 : ℝ))
    hinnerFar houterFar r (xInner r) (xOuter r) m
  · exact separation_radius_le_pathScale hd hδpos hδ n hscale
  · positivity
  · omega
  · intro i x hx
    have := hinnerHalf i x hx
    rw [hinnerSign] at this
    simpa using this
  · intro i x hx
    have := houterHalf i x hx
    rw [houterSign] at this
    norm_num at this
    omega
  · intro i
    have := hinnerFinish i
    rw [hinnerSign] at this
    simpa using this
  · intro i
    have := houterFinish i
    rw [houterSign] at this
    norm_num at this
    omega

theorem case1_different_orthants_small_gap_reverse_oriented
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (houterNonAxis : ¬ IsAxisPoint (n + 1) xOuter)
    (r : Fin d) (hinnerR : xInner r < 0) (houterR : 0 < xOuter r)
    (hclose : xOuter r - xInner r < 3 * (pathScale δ n : ℤ)) :
    ∃ paths : PathIndex n xInner xOuter → LatticePath d,
      FamilyProperties (n := n) δ xInner xOuter paths := by
  let s : Fin d → ℤ := fun _ ↦ -1
  have hs : ∀ i, Int.natAbs (s i) = 1 := by
    intro i
    simp [s]
  have hinner' : reflect s xInner ∈ sphere d n :=
    (reflect_mem_sphere_iff hs).2 hinner
  have houter' : reflect s xOuter ∈ sphere d (n + 1) :=
    (reflect_mem_sphere_iff hs).2 houter
  have houterNonAxis' : ¬ IsAxisPoint (n + 1) (reflect s xOuter) := by
    simpa only [isAxisPoint_reflect_iff hs] using houterNonAxis
  have hinnerR' : 0 < reflect s xInner r := by
    simp only [reflect_apply, s]
    omega
  have houterR' : reflect s xOuter r < 0 := by
    simp only [reflect_apply, s]
    omega
  have hclose' :
      reflect s xInner r - reflect s xOuter r < 3 * (pathScale δ n : ℤ) := by
    simp only [reflect_apply, s]
    omega
  obtain ⟨basePaths, hstartInner, hstartOuter, hedges, hspheres,
      hlength, hfar⟩ :=
    case1_different_orthants_small_gap_oriented hd δ hδpos hδ hn hscale
      (reflect s xInner) (reflect s xOuter) hinner' houter'
      houterNonAxis' r hinnerR' houterR' hclose'
  have hbase : FamilyProperties (n := n) δ
      (reflect s xInner) (reflect s xOuter) basePaths :=
    ⟨hstartInner, hstartOuter, hedges, hspheres, hlength, hfar⟩
  have hreflected := familyProperties_reflect δ s hs
    (reflect s xInner) (reflect s xOuter) basePaths hbase
  rcases hreflected with
    ⟨hrefStartInner, hrefStartOuter, hrefEdges, hrefSpheres,
      hrefLength, hrefFar⟩
  let innerEquiv : Fin (pathCountAtInner n xInner) ≃
      Fin (pathCountAtInner n (reflect s xInner)) :=
    Equiv.cast (by simp only [pathCountAtInner_reflect hs])
  let outerEquiv : Fin (pathCountAtOuter n xOuter) ≃
      Fin (pathCountAtOuter n (reflect s xOuter)) :=
    Equiv.cast (by simp only [pathCountAtOuter_reflect hs])
  let indexEquiv : PathIndex n xInner xOuter ≃
      PathIndex n (reflect s xInner) (reflect s xOuter) :=
    Equiv.sumCongr innerEquiv outerEquiv
  let paths : PathIndex n xInner xOuter → LatticePath d :=
    fun i ↦ (basePaths (indexEquiv i)).reflect hs
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [paths, indexEquiv, Equiv.sumCongr_apply, Sum.map_inl,
      reflect_reflect hs] using hrefStartInner (innerEquiv i)
  · intro i
    simpa only [paths, indexEquiv, Equiv.sumCongr_apply, Sum.map_inr,
      reflect_reflect hs] using hrefStartOuter (outerEquiv i)
  · intro i j hij
    exact hrefEdges (indexEquiv i) (indexEquiv j)
      (indexEquiv.injective.ne hij)
  · intro i z hz
    exact hrefSpheres (indexEquiv i) z hz
  · intro i
    exact hrefLength (indexEquiv i)
  · intro i j hij z hz
    exact hrefFar (indexEquiv i) (indexEquiv j)
      (indexEquiv.injective.ne hij) z hz

theorem case1_different_orthants
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hn : 1 ≤ n) (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (xInner xOuter : LatticePoint d)
    (hinner : xInner ∈ sphere d n) (houter : xOuter ∈ sphere d (n + 1))
    (houterNonAxis : ¬ IsAxisPoint (n + 1) xOuter)
    (r : Fin d) (hopposite : xInner r * xOuter r < 0) :
    ∃ paths : PathIndex n xInner xOuter → LatticePath d,
      FamilyProperties (n := n) δ xInner xOuter paths := by
  rcases Int.mul_neg_iff.mp hopposite with horiented | hreverse
  · by_cases hgap :
        3 * (pathScale δ n : ℤ) ≤ xInner r - xOuter r
    · simpa only [FamilyProperties] using
        exists_nonAxis_paths_of_inner_coordinate_gap hd δ hδpos hδ hn hscale
          xInner xOuter hinner houter houterNonAxis r hgap
    · have hclose :
          xInner r - xOuter r < 3 * (pathScale δ n : ℤ) := by omega
      simpa only [FamilyProperties] using
        case1_different_orthants_small_gap_oriented hd δ hδpos hδ hn hscale
          xInner xOuter hinner houter houterNonAxis r
          horiented.1 horiented.2 hclose
  · by_cases hgap :
        3 * (pathScale δ n : ℤ) ≤ xOuter r - xInner r
    · simpa only [FamilyProperties] using
        exists_nonAxis_paths_of_outer_coordinate_gap hd δ hδpos hδ hn hscale
          xInner xOuter hinner houter houterNonAxis r hgap
    · have hclose :
          xOuter r - xInner r < 3 * (pathScale δ n : ℤ) := by omega
      exact case1_different_orthants_small_gap_reverse_oriented
        hd δ hδpos hδ hn hscale xInner xOuter hinner houter houterNonAxis r
        hreverse.1 hreverse.2 hclose

end

end DisjointPaths
