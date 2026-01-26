import Mathlib
open scoped BigOperators
open MeasureTheory
open Filter
namespace Test
abbrev γ : Measure ℝ := ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
variable (κ : ℝ)

-- mimic the definitions
let bound : ℝ → ℝ := fun z => 4 * (κ ^ 2 + z ^ 2) + 10

example : Integrable (fun z : ℝ => 4 * (κ ^ 2 + z ^ 2) + 10) (γ := γ) := by
  -- try the same proof
  have hz2_int : Integrable (fun z : ℝ => z ^ 2) γ := by
    simpa [γ] using
      (MeasureTheory.MemLp.integrable_sq
        (ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))))
  have hκ2_int : Integrable (fun _ : ℝ => κ ^ 2) γ := by
    simpa using (MeasureTheory.integrable_const (μ := γ) (κ ^ 2))
  have hsum : Integrable (fun z : ℝ => κ ^ 2 + z ^ 2) γ := hκ2_int.add hz2_int
  have hmul : Integrable (fun z : ℝ => (4 : ℝ) * (κ ^ 2 + z ^ 2)) γ := hsum.const_mul 4
  have hconst : Integrable (fun _ : ℝ => (10 : ℝ)) γ := by
    simpa using (MeasureTheory.integrable_const (μ := γ) (10 : ℝ))
  have : Integrable (fun z : ℝ => (4 : ℝ) * (κ ^ 2 + z ^ 2) + (10 : ℝ)) γ := hmul.add hconst
  -- now simp
  simpa [mul_add, add_assoc, add_left_comm, add_comm] using this
end Test
