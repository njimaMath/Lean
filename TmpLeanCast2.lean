import Mathlib.Probability.Distributions.Gaussian.Real

namespace ProbabilityTheory

example (mu : Real) {v : NNReal} (hv : v != 0) : ((v:Real) != 0) := by
  -- try exact_mod_cast?
  exact_mod_cast hv

end ProbabilityTheory
