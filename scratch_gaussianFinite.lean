import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

open MeasureTheory

namespace Scratch

noncomputable section

example : IsFiniteMeasure (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) := by
  infer_instance

end

end Scratch
