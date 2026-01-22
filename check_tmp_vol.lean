import Mathlib
open MeasureTheory
open scoped NNReal
#check (by
  have : (0:ℝ≥0∞) < (volume : Measure ℝ) ({0}ᶜ : Set ℝ) := by
    --
    simpa using (show (0:ℝ≥0∞) < (⊤:ℝ≥0∞) from ENNReal.bot_lt_top)
  exact this)
