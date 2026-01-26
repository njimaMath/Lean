import Mathlib
import perceptronFixed.Prop_A_P.Prop_A_P
import perceptronFixed.Theorem1.Theorem

open scoped BigOperators Topology NNReal Real ENNReal Interval
open MeasureTheory Filter

namespace Theorem3

noncomputable section

abbrev sech : ℝ → ℝ := Theorem1.sech

lemma test (x : ℝ) : (1 / (Real.cosh x) ^ 2) = (sech x) ^ 2 := by
  simp [sech, Theorem1.sech]

end

end Theorem3
