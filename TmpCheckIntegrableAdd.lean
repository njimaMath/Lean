import Mathlib
open MeasureTheory
open scoped BigOperators
variable {μ : Measure ℝ}
variable (κ : ℝ)
example : Integrable (fun z : ℝ => (4 : ℝ) * (κ ^ 2 + z ^ 2) + (10 : ℝ)) μ := by
  have hz2_int : Integrable (fun z : ℝ => z ^ 2) μ := by
    -- dummy
    simpa using (integrable_const (μ := μ) (0 : ℝ))
  have hκ2_int : Integrable (fun _ : ℝ => κ ^ 2) μ := by
    simpa using (integrable_const (μ := μ) (κ ^ 2))
  have hsum : Integrable (fun z : ℝ => κ ^ 2 + z ^ 2) μ := hκ2_int.add hz2_int
  have hmul : Integrable (fun z : ℝ => (4 : ℝ) * (κ ^ 2 + z ^ 2)) μ := hsum.const_mul 4
  have hconst : Integrable (fun _ : ℝ => (10 : ℝ)) μ := by
    simpa using (integrable_const (μ := μ) (10 : ℝ))
  have : Integrable (fun z : ℝ => (4 : ℝ) * (κ ^ 2 + z ^ 2) + (10 : ℝ)) μ := hmul.add hconst
  -- simp only? 
  simpa [add_comm, add_left_comm, add_assoc] using this
