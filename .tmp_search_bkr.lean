import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open scoped BigOperators ENNReal

namespace Tmp

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable (μ : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
variable (A B : Set ((i : ι) → α i))

-- Check if a BKR lemma already exists in Mathlib under some name
#check Measure.pi
#check Measure.pi_mul

end Tmp
