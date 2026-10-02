import Disjoint_paths.Lemmas.OuterContinuation
import Disjoint_paths.Lemmas.Separation

/-!
# Pairwise properties of continued outer paths

Distinct paths have distinct private coordinates and share one reservoir.
Each path moves inward in its own private coordinate, while every other path
is nondecreasing in that signed coordinate.  This proves both edge
disjointness and endpoint-to-whole-path separation.
-/

namespace DisjointPaths

noncomputable section

theorem outerPrivatePaths_edgeDisjoint_of_distinct {d : ℕ}
    (y : LatticePoint d) (p : Fin d)
    (i hi j hj : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hyj : y j ≠ 0)
    (hihi : i ≠ hi) (hihp : hi ≠ p) (hip : i ≠ p)
    (hjhj : j ≠ hj) (hjhp : hj ≠ p) (hjp : j ≠ p)
    (hij : i ≠ j) :
    Disjoint
      (outerPrivatePath y i hi p m hyi hihi hip hihp).edgeSet
      (outerPrivatePath y j hj p m hyj hjhj hjp hjhp).edgeSet := by
  apply LatticePath.edgeDisjoint_of_common_vertices_subsingleton _ _ y
  intro x hxi hxj
  have hle := outerPrivatePath_private_coordinate_le_start
    y i hi p m hyi hihi hip hihp x hxi
  have hge := outerPrivatePath_other_coordinate_ge_start
    y j hj p m hyj hjhj hjp hjhp x hxj i hij hip
  apply outerPrivatePath_eq_start_of_private_coordinate_eq
    y i hi p m hyi hihi hip hihp x hxi
  exact le_antisymm hle hge

theorem outerPrivatePath_endpoint_far_of_distinct {d : ℕ}
    (y : LatticePoint d) (p : Fin d)
    (i hi j hj : Fin d) (m : ℕ)
    (hyi : y i ≠ 0) (hyj : y j ≠ 0)
    (hihi : i ≠ hi) (hihp : hi ≠ p) (hip : i ≠ p)
    (hjhj : j ≠ hj) (hjhp : hj ≠ p) (hjp : j ≠ p)
    (hij : i ≠ j) (r : ℝ) (hr : r ≤ (m : ℝ)) :
    ∀ x ∈ (outerPrivatePath y j hj p m hyj hjhj hjp hjhp).vertices,
      r ≤ (l1Dist
        (outerPrivatePath y i hi p m hyi hihi hip hihp).finish x : ℝ) := by
  let pathI := outerPrivatePath y i hi p m hyi hihi hip hihp
  let pathJ := outerPrivatePath y j hj p m hyj hjhj hjp hjhp
  have hfinish := outerPrivatePath_finish_private_coordinate
    y i hi p m hyi hihi hip hihp
  have hvertices : ∀ x ∈ pathJ.vertices,
      coordinateSign (y i) * y i ≤ coordinateSign (y i) * x i := by
    intro x hx
    exact outerPrivatePath_other_coordinate_ge_start
      y j hj p m hyj hjhj hjp hjhp x hx i hij hip
  rcases Int.natAbs_eq_iff.mp (natAbs_coordinateSign (y i)) with hsign | hsign
  · apply endpoint_far_from_vertices_of_reverse_coordinate_gap
      pathI pathJ i r (pathI.finish i) (y i) m hr (by positivity) le_rfl
    · intro x hx
      have hx' := hvertices x hx
      rw [hsign] at hx'
      simpa using hx'
    · have hyabs := coordinateSign_mul_self (y i)
      rw [hsign] at hfinish hyabs
      norm_num at hfinish hyabs
      change (m : ℤ) ≤ y i -
        (outerPrivatePath y i hi p m hyi hihi hip hihp).finish i
      omega
  · apply endpoint_far_from_vertices_of_coordinate_gap
      pathI pathJ i r (pathI.finish i) (y i) m hr (by positivity) le_rfl
    · intro x hx
      have hx' := hvertices x hx
      rw [hsign] at hx'
      simpa using hx'
    · have hyabs := coordinateSign_mul_self (y i)
      rw [hsign] at hfinish hyabs
      norm_num at hfinish hyabs
      change (m : ℤ) ≤
        (outerPrivatePath y i hi p m hyi hihi hip hihp).finish i - y i
      omega

end

end DisjointPaths
