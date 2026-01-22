import Mathlib
open MeasureTheory
open scoped ENNReal
namespace Test
noncomputable section
variable (κ : ℝ)
variable (f : ℝ → ℝ)
variable (hpos_interval : 0 < ∫ x : ℝ in (κ - 1)..(κ - (1/2:ℝ)), f x)
variable (hIoc : (∫ x : ℝ in (κ - 1)..(κ - (1/2:ℝ)), f x) = ∫ x in Set.Ioc (κ - 1) (κ - (1/2:ℝ)), f x)
example : 0 < ∫ x in Set.Ioc (κ - 1) (κ - (1/2:ℝ)), f x := by
  -- use rewriting without simp
  have : 0 < (∫ x : ℝ in (κ - 1)..(κ - (1/2:ℝ)), f x) := hpos_interval
  -- rewrite
  --
  -- `rw` should work
  --
  simpa using this
end
end Test
