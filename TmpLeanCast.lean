import Mathlib.Probability.Distributions.Gaussian.Real

open scoped Real
namespace ProbabilityTheory

example (mu : Real) {v : NNReal} (hv : v ? 0) : ((v:Real) ? 0) := by
  exact_mod_cast hv

end ProbabilityTheory
