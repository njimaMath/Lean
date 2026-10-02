import Disjoint_paths.Lemmas.OuterContinuation
import Disjoint_paths.Lemmas.Scale

/-!
# A one-path outer family

This packages a private-coordinate outer path when the prescribed outer path
count is one.  Unlike the axis-only construction, the private coordinate may
be short and hence use the corrected continuation.
-/

namespace DisjointPaths

noncomputable section

theorem exists_single_outerPrivatePath
    {d n : ℕ} (hd : 3 ≤ d)
    (δ : ℝ) (_hδpos : 0 < δ) (_hδ : δ ≤ 1 / (8 * d : ℝ))
    (_hscale : 12 ≤ δ ^ 2 * (n + 1 : ℝ))
    (y : LatticePoint d) (hy : y ∈ sphere d (n + 1))
    (i h p : Fin d) (hyi : y i ≠ 0)
    (hih : i ≠ h) (hip : i ≠ p) (hhp : h ≠ p)
    (hreservoir : (pathScale δ n : ℤ) ≤ coordinateSign (y p) * y p)
    (hcount : pathCountAtOuter n y = 1) :
    ∃ paths : Fin (pathCountAtOuter n y) → LatticePath d,
      (∀ i, (paths i).start = y) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere d n ∪ sphere d (n + 1)) ∧
      (∀ i,
        ⌊δ ^ 2 * (n + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
        ((paths i).edgeLength : ℤ) ≤ ⌊2 * d * δ ^ 2 * (n + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        δ ^ 3 * (n + 1 : ℝ) ≤ (l1Dist (paths i).finish x : ℝ)) ∧
      (∀ i x, x ∈ (paths i).vertices → ∀ r,
        y r - (pathScale δ n : ℤ) ≤ x r ∧
          x r ≤ y r + (pathScale δ n : ℤ)) := by
  let m := pathScale δ n
  let path := outerPrivatePath y i h p m hyi hih hip hhp
  let paths : Fin (pathCountAtOuter n y) → LatticePath d := fun _ => path
  refine ⟨paths, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simp [paths, path]
  · intro j k hjk
    exfalso
    apply hjk
    apply Fin.ext
    have hj := j.isLt
    have hk := k.isLt
    omega
  · intro j x hx
    apply outerPrivatePath_vertices_on_two_spheres y i h p m hyi hih hip hhp hy
      (by simpa [m] using hreservoir) x
    simpa [paths, path] using hx
  · intro j
    constructor
    · simpa [paths, path, m] using pathScale_length_lower (δ := δ) n
    · simpa [paths, path, m] using
        pathScale_length_upper (show 1 ≤ d by omega) δ n
  · intro j k hjk
    exfalso
    apply hjk
    apply Fin.ext
    have hj := j.isLt
    have hk := k.isLt
    omega
  · intro j x hx r
    simpa [paths, path, m] using
      outerPrivatePath_coordinate_bounds y i h p m hyi hih hip hhp x
        (by simpa [paths, path] using hx) r

end

end DisjointPaths
