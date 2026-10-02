import Disjoint_paths.Lemmas.Basic
import Mathlib.Tactic.NormNum

/-!
# The obstruction at `n = 0`

The statement in `Main_Disjoint.lean` has no large-radius hypothesis. This
file proves that its conclusion is false for `d = 3`, `n = 0`,
`xInner = 0`, `xOuter = e₀`, and `δ = 1 / 24`.
-/

namespace DisjointPaths

noncomputable section

private def zeroPoint : LatticePoint 3 := fun _ ↦ 0

private def firstUnitPoint : LatticePoint 3 := fun i ↦ if i = 0 then 1 else 0

lemma zeroPoint_mem_sphere_zero : zeroPoint ∈ sphere 3 0 := by
  simp [sphere, l1Norm, zeroPoint]

lemma firstUnitPoint_mem_sphere_one : firstUnitPoint ∈ sphere 3 1 := by
  change l1Norm firstUnitPoint = 1
  decide

lemma zeroPoint_isAxisPoint : IsAxisPoint 0 zeroPoint := by
  refine ⟨0, Or.inl ?_⟩
  funext j
  simp [zeroPoint]

lemma pathCountAtInner_zeroPoint : pathCountAtInner 0 zeroPoint = 3 := by
  simp [pathCountAtInner, zeroPoint_isAxisPoint]

lemma counterexample_hypotheses :
    3 ≤ (3 : ℕ) ∧
      zeroPoint ∈ sphere 3 0 ∧
      firstUnitPoint ∈ sphere 3 1 ∧
      0 < (1 / 24 : ℝ) ∧
      (1 / 24 : ℝ) ≤ 1 / (8 * 3 : ℝ) := by
  exact ⟨by norm_num, zeroPoint_mem_sphere_zero,
    firstUnitPoint_mem_sphere_one, by norm_num, by norm_num⟩

/-- The full existential conclusion of the claimed theorem, specialized to
the small-radius data, is false. This is a sanity check for the necessity of
the threshold in the theorem, not a counterexample to the quantified theorem.
-/
theorem no_path_family_at_n_zero :
    ¬ ∃ paths : PathIndex 0 zeroPoint firstUnitPoint → LatticePath 3,
      (∀ i : Fin (pathCountAtInner 0 zeroPoint),
        (paths (Sum.inl i)).start = zeroPoint) ∧
      (∀ i : Fin (pathCountAtOuter 0 firstUnitPoint),
        (paths (Sum.inr i)).start = firstUnitPoint) ∧
      (∀ i j, i ≠ j → Disjoint (paths i).edgeSet (paths j).edgeSet) ∧
      (∀ i, ∀ x ∈ (paths i).vertices,
        x ∈ sphere 3 0 ∪ sphere 3 1) ∧
      (∀ i,
        ⌊(1 / 24 : ℝ) ^ 2 * (0 + 1 : ℝ)⌋ ≤ ((paths i).edgeLength : ℤ) ∧
          ((paths i).edgeLength : ℤ) ≤
            ⌊2 * 3 * (1 / 24 : ℝ) ^ 2 * (0 + 1 : ℝ)⌋) ∧
      (∀ i j, i ≠ j → ∀ x ∈ (paths j).vertices,
        (1 / 24 : ℝ) ^ 3 * (0 + 1 : ℝ) ≤
          (l1Dist (paths i).finish x : ℝ)) := by
  rintro ⟨paths, hstartInner, -, -, -, hlength, hseparation⟩
  let i₀ : Fin (pathCountAtInner 0 zeroPoint) :=
    ⟨0, by rw [pathCountAtInner_zeroPoint]; omega⟩
  let i₁ : Fin (pathCountAtInner 0 zeroPoint) :=
    ⟨1, by rw [pathCountAtInner_zeroPoint]; omega⟩
  let index₀ : PathIndex 0 zeroPoint firstUnitPoint := Sum.inl i₀
  let index₁ : PathIndex 0 zeroPoint firstUnitPoint := Sum.inl i₁
  have hne : index₀ ≠ index₁ := by
    simp [index₀, index₁, i₀, i₁]
  have hupper := (hlength index₀).2
  have hedgeLength : (paths index₀).edgeLength = 0 := by
    norm_num [index₀] at hupper
    omega
  have hfinish : (paths index₀).finish = zeroPoint := by
    rw [LatticePath.finish_eq_start_of_edgeLength_eq_zero _ hedgeLength]
    exact hstartInner i₀
  have hzero_mem : zeroPoint ∈ (paths index₁).vertices := by
    rw [← hstartInner i₁]
    exact List.head_mem (paths index₁).nonempty
  have hpositive_le_zero :=
    hseparation index₀ index₁ hne zeroPoint hzero_mem
  rw [hfinish] at hpositive_le_zero
  norm_num [l1Dist, l1Norm, zeroPoint] at hpositive_le_zero

end

end DisjointPaths
