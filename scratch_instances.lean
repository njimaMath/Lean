import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

open scoped BigOperators
open MeasureTheory

namespace Scratch

noncomputable section

abbrev gaussianStd (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))

example (n : ℕ) : SFinite (gaussianStd n) := by
  dsimp [gaussianStd]
  infer_instance

example (n : ℕ) : SigmaFinite (gaussianStd n) := by
  dsimp [gaussianStd]
  infer_instance

example (n : ℕ) : IsProbabilityMeasure (gaussianStd n) := by
  dsimp [gaussianStd]
  infer_instance

example (n : ℕ) : IsFiniteMeasure (gaussianStd n) := by
  dsimp [gaussianStd]
  infer_instance

end

end Scratch
