import Disjoint_paths.Lemmas.DownwardInnerPath
import Disjoint_paths.Lemmas.FanCount
import Disjoint_paths.Lemmas.Reservoir
import Disjoint_paths.Lemmas.Scale

/-!
# A complete inner family crossing a short nonzero coordinate

All ordinary fan directions except the reservoir direction use
`shortDownwardInnerPath`.  The unique outward reservoir direction is replaced
by `exceptionalShortDownwardInnerPath`, preserving the exact non-axis count.
-/

namespace DisjointPaths

noncomputable section

open LatticePath

theorem exists_shortDownwardInnerFamily_nonAxis
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (hδpos : 0 < δ) (hδ : δ ≤ 1 / (8 * d : ℝ))
    (hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (z : LatticePoint d) (hz : z ∈ sphere d n)
    (hnotAxis : ¬ IsAxisPoint n z)
    (r p : Fin d) (hrp : r ≠ p) (hzr : z r ≠ 0)
    (hshort : Int.natAbs (z r) < pathScale δ n)
    (hreservoir : ((3 * pathScale δ n : ℕ) : ℤ) ≤
      coordinateSign (z p) * z p) :
    ∃ paths : Fin (pathCountAtInner n z) → LatticePath d,
      (∀ i, (paths i).start = z) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤
          ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) ∧
      (∀ i x, x ∈ (paths i).vertices →
        coordinateSign (z r) * x r ≤ coordinateSign (z r) * z r) ∧
      (∀ i, coordinateSign (z r) * (paths i).finish r ≤
        coordinateSign (z r) * z r - (pathScale δ n : ℤ)) := by
  classical
  let m := pathScale δ n
  let s := Int.natAbs (z r)
  let t := m - s
  let sr := coordinateSign (z r)
  let sp := coordinateSign (z p)
  let h := thirdCoordinate hd p r (Ne.symm hrp)
  let sh := coordinateSign (z h)
  have hsr : Int.natAbs sr = 1 := natAbs_coordinateSign _
  have hsp : Int.natAbs sp = 1 := natAbs_coordinateSign _
  have hsh : Int.natAbs sh = 1 := natAbs_coordinateSign _
  have hs : 0 < s := Int.natAbs_pos.mpr hzr
  have hsm : s < m := hshort
  have ht : 0 < t := by dsimp [t]; omega
  have hst : s + t = m := by dsimp [t]; omega
  have hstScale : s + t = pathScale δ n := by simpa [m] using hst
  have hseparator : sr * z r = s := by
    dsimp [sr, s]
    rw [coordinateSign_mul_self]
  have hpNonzero : z p ≠ 0 := by
    intro hpzero
    rw [hpzero] at hreservoir
    norm_num at hreservoir
    have hm : 12 ≤ m := by
      apply (Nat.le_floor_iff (by positivity)).mpr
      exact hscale
    omega
  have hph : p ≠ h := by
    exact Ne.symm (thirdCoordinate_ne_left hd p r (Ne.symm hrp))
  have hrh : r ≠ h := by
    exact Ne.symm (thirdCoordinate_ne_right hd p r (Ne.symm hrp))
  have hcard : Fintype.card (InnerFanIndex z r) = pathCountAtInner n z := by
    rw [card_innerFanIndex z r hzr]
    simp [pathCountAtInner, hnotAxis]
  let indexEquiv : Fin (pathCountAtInner n z) ≃ InnerFanIndex z r :=
    (Fintype.equivFinOfCardEq hcard).symm
  have hreservoir' : ((3 * t : ℕ) : ℤ) ≤ sp * z p + s := by
    dsimp [sp, m] at hreservoir ⊢
    push_cast at hreservoir ⊢
    omega
  have hordinaryReservoir : ((2 * t : ℕ) : ℤ) ≤ sp * z p := by
    dsimp [sp, m] at hreservoir ⊢
    push_cast at hreservoir ⊢
    omega
  have houtP : 0 ≤ sp * z p := by
    dsimp [sp]
    rw [coordinateSign_mul_self]
    positivity
  have houtH : 0 ≤ sh * z h := by
    dsimp [sh]
    rw [coordinateSign_mul_self]
    positivity
  let rawPath (q : InnerFanIndex z r) : LatticePath d :=
    if hqp : q.1.1 = p then
      exceptionalShortDownwardInnerPath z p r h sp sr sh
        (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator
    else
      shortDownwardInnerPath z q.1.1 r p (boolSign q.1.2) sr sp
        q.2.2 hqp hrp (natAbs_boolSign _) hsr hsp s t
  let paths : Fin (pathCountAtInner n z) → LatticePath d := fun i =>
    rawPath (indexEquiv i)
  have hreservoirSign : ∀ q : InnerFanIndex z r, q.1.1 = p →
      boolSign q.1.2 = sp := by
    intro q hqp
    dsimp [sp]
    apply boolSign_eq_coordinateSign_of_outward z p q.1.2 hpNonzero
    simpa [IsOutwardDirection, hqp] using q.2.1
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    let q := indexEquiv i
    by_cases hqp : q.1.1 = p
    · simp [paths, rawPath, q, hqp]
    · simp [paths, rawPath, q, hqp]
  · intro i j hij
    let q := indexEquiv i
    let v := indexEquiv j
    have hqv : q ≠ v := indexEquiv.injective.ne hij
    by_cases hqp : q.1.1 = p
    · by_cases hvp : v.1.1 = p
      · exfalso
        apply hqv
        apply Subtype.ext
        apply Prod.ext
        · exact hqp.trans hvp.symm
        apply boolSign_injective
        rw [hreservoirSign q hqp, hreservoirSign v hvp]
      · symm
        simpa [paths, rawPath, q, v, hqp, hvp] using
          shortDownwardInnerPath_edgeDisjoint_exceptional
            z r p h sr sp sh hrp hph hrh hsr hsp hsh s t hs ht
            hseparator v hvp
    · by_cases hvp : v.1.1 = p
      · simpa [paths, rawPath, q, v, hqp, hvp] using
          shortDownwardInnerPath_edgeDisjoint_exceptional
            z r p h sr sp sh hrp hph hrh hsr hsp hsh s t hs ht
            hseparator q hqp
      · simpa [paths, rawPath, q, v, hqp, hvp] using
          shortDownwardInnerPaths_edgeDisjoint z r p sr sp hrp hsr hsp
            s t hs hqp hvp hqv
  · intro i x hx
    let q := indexEquiv i
    by_cases hqp : q.1.1 = p
    · apply exceptionalShortDownwardInnerPath_vertices_on_two_spheres
        z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh s t hz
        houtP houtH hseparator hreservoir' x
      simpa [paths, rawPath, q, hqp] using hx
    · apply shortDownwardInnerPath_vertices_on_two_spheres
        z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
        (natAbs_boolSign _) hsr hsp s t hz
        (by simpa [IsOutwardDirection] using q.2.1) hseparator
        hordinaryReservoir x
      simpa [paths, rawPath, q, hqp] using hx
  · intro i
    let q := indexEquiv i
    by_cases hqp : q.1.1 = p
    · constructor
      · rw [show (paths i).edgeLength = 2 * s + 6 * t by
          simp [paths, rawPath, q, hqp]]
        have hlower := pathScale_length_lower (δ := δ) n
        push_cast at hlower ⊢
        omega
      · rw [show (paths i).edgeLength = 2 * s + 6 * t by
          simp [paths, rawPath, q, hqp]]
        have hupper := six_pathScale_length_upper hd δ n
        push_cast at hupper ⊢
        omega
    · constructor
      · rw [show (paths i).edgeLength = 2 * s + 4 * t by
          simp [paths, rawPath, q, hqp]]
        have hlower := pathScale_length_lower (δ := δ) n
        push_cast at hlower ⊢
        omega
      · rw [show (paths i).edgeLength = 2 * s + 4 * t by
          simp [paths, rawPath, q, hqp]]
        have hupper := six_pathScale_length_upper hd δ n
        push_cast at hupper ⊢
        omega
  · intro i j hij x hx
    let q := indexEquiv i
    let v := indexEquiv j
    have hqv : q ≠ v := indexEquiv.injective.ne hij
    have hradius : δ ^ 3 * (n + 1 : ℝ) ≤ (((s + t) / 6 : ℕ) : ℝ) := by
      rw [hst]
      exact separation_radius_le_pathScale_div_six hd hδpos hδ n hscale
    by_cases hqp : q.1.1 = p
    · by_cases hvp : v.1.1 = p
      · exfalso
        apply hqv
        apply Subtype.ext
        apply Prod.ext
        · exact hqp.trans hvp.symm
        apply boolSign_injective
        rw [hreservoirSign q hqp, hreservoirSign v hvp]
      · have hxv : x ∈
            (shortDownwardInnerPath z v.1.1 r p (boolSign v.1.2) sr sp
              v.2.2 hvp hrp (natAbs_boolSign _) hsr hsp s t).vertices := by
          simpa [paths, rawPath, v, hvp] using hx
        have hfar := exceptionalShortDownwardInnerPath_endpoint_far_ordinary
          z r p h sr sp sh hrp hph hrh hsr hsp hsh s t hseparator
          v hvp (δ ^ 3 * (n + 1 : ℝ)) hradius x hxv
        simpa [paths, rawPath, q, hqp] using hfar
    · by_cases hvp : v.1.1 = p
      · have hxv : x ∈
            (exceptionalShortDownwardInnerPath z p r h sp sr sh
              (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator).vertices := by
          simpa [paths, rawPath, v, hvp] using hx
        have hfar := shortDownwardInnerPath_endpoint_far_exceptional
          z r p h sr sp sh hrp hph hrh hsr hsp hsh s t hseparator
          q hqp (δ ^ 3 * (n + 1 : ℝ)) hradius x hxv
        simpa [paths, rawPath, q, hqp] using hfar
      · have hxv : x ∈
            (shortDownwardInnerPath z v.1.1 r p (boolSign v.1.2) sr sp
              v.2.2 hvp hrp (natAbs_boolSign _) hsr hsp s t).vertices := by
          simpa [paths, rawPath, v, hvp] using hx
        have hfar := shortDownwardInnerPath_endpoint_far_of_distinct
          z r p sr sp hrp hsr hsp s t
          (δ ^ 3 * (n + 1 : ℝ)) (by
            rw [hstScale]
            exact separation_radius_le_pathScale hd hδpos hδ n hscale)
          hqp hvp hqv x hxv
        simpa [paths, rawPath, q, hqp] using hfar
  · intro i x hx
    let q := indexEquiv i
    by_cases hqp : q.1.1 = p
    · apply exceptionalShortDownwardInnerPath_separator_coordinate_le_start
        z p r h sp sr sh (Ne.symm hrp) hph hrh hsp hsr hsh
        s t hseparator x
      simpa [paths, rawPath, q, hqp] using hx
    · apply shortDownwardInnerPath_separator_coordinate_le_start
        z q.1.1 r p (boolSign q.1.2) sr sp q.2.2 hqp hrp
        (natAbs_boolSign _) hsr hsp s t x
      simpa [paths, rawPath, q, hqp] using hx
  · intro i
    let q := indexEquiv i
    by_cases hqp : q.1.1 = p
    · rw [show paths i = exceptionalShortDownwardInnerPath z p r h sp sr sh
          (Ne.symm hrp) hph hrh hsp hsr hsh s t hseparator by
          simp [paths, rawPath, q, hqp]]
      rw [exceptionalShortDownwardInnerPath_finish_separator_coordinate]
      push_cast
      omega
    · rw [show paths i = shortDownwardInnerPath z q.1.1 r p
          (boolSign q.1.2) sr sp q.2.2 hqp hrp (natAbs_boolSign _)
          hsr hsp s t by simp [paths, rawPath, q, hqp]]
      rw [shortDownwardInnerPath_finish_separator_coordinate]
      push_cast
      omega

end

end DisjointPaths
