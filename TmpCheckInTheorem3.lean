import Mathlib
import perceptronFixed.Theorem1.Theorem

open scoped BigOperators Topology NNReal Real ENNReal Interval
open MeasureTheory Filter

namespace Scratch2

noncomputable section

namespace Theorem3

abbrev γ : Measure ℝ := Theorem1.γ
abbrev Expect (f : ℝ → ℝ) : ℝ := Theorem1.Expect f
abbrev sech : ℝ → ℝ := Theorem1.sech

lemma test (x : ℝ) : (1 / (Real.cosh x) ^ 2) = (sech x) ^ 2 := by
  simp [sech, Theorem1.sech]

end Theorem3

end

end Scratch2
