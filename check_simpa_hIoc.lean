import Mathlib
open MeasureTheory
open scoped ENNReal Interval
noncomputable section
abbrev f : ℝ → ℝ := ProbabilityTheory.gaussianPDFReal (0:ℝ) (1:ℝ≥0)
example (κ : ℝ) : True := by
  have hab : (κ - 1 : ℝ) < κ - (1/2:ℝ) := by linarith
  have hIoc :
      (∫ x in Set.Ioc (κ - 1) (κ - (1/2:ℝ)), f x) =
        ∫ x : ℝ in (κ - 1)..(κ - (1/2:ℝ)), f x := by
    simpa using (intervalIntegral.integral_of_le (μ:= (volume:Measure ℝ)) (f := f) (a := (κ - 1)) (b := (κ - (1/2:ℝ))) hab.le).symm
  have hpos_interval : 0 < ∫ x : ℝ in (κ - 1)..(κ - (1/2:ℝ)), f x := by
    -- fake
    have : 0 < (1:ℝ) := by norm_num
    simpa using this
  have : 0 < ∫ x in Set.Ioc (κ - 1) (κ - (1/2:ℝ)), f x := by
    -- try the same simpa
    --
    simpa [hIoc] using hpos_interval
  trivial
