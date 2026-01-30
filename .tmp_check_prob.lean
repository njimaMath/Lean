import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace Tmp

open MeasureTheory

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i, MeasurableSpace (A i)]

variable (μ : (i : I) → Measure (A i)) [∀ i, IsProbabilityMeasure (μ i)]

#check (Measure.pi μ)
#synth IsProbabilityMeasure (Measure.pi μ)

end Tmp
