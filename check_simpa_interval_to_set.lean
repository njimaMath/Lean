import Mathlib
open MeasureTheory
open scoped ENNReal
namespace Test
noncomputable section
variable (κ : ℝ)
variable (f : ℝ → ℝ)
variable (hab : (κ - 1 : ℝ) < κ - (1/2:ℝ))
-- assume something
variable (hpos_interval : 0 < ∫ x : ℝ in (κ - 1)..(κ - (1/2:ℝ)), f x)
-- relation
variable (hIoc : (∫ x : ℝ in (κ - 1)..(κ - (1/2:ℝ)), f x) = ∫ x in Set.Ioc (κ - 1) (κ - (1/2:ℝ)), f x)
example : 0 < ∫ x in Set.Ioc (κ - 1) (κ - (1/2:ℝ)), f x := by
  -- try rewriting
  --
  have : 0 < (∫ x : ℝ in (κ - 1)..(κ - (1/2:ℝ)), f x) := hpos_interval
  --
  -- method
  --
  -- exact?
  --
  -- Maybe use `by simpa [hIoc] using hpos_interval`:
  simpa [hIoc] using hpos_interval
end
end Test
