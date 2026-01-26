import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Real
open MeasureTheory
namespace ProbabilityTheory

noncomputable section

lemma test (mu : R) {v : NNReal} (hv : v ? 0) (x : R) :
    HasDerivAt (gaussianPDFReal mu v)
      (-(x - mu) / (v : R) * gaussianPDFReal mu v x) x := by
  
  sorry

end

end ProbabilityTheory
