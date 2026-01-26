import Mathlib.Probability.Distributions.Gaussian.Real

namespace ProbabilityTheory

example {v : NNReal} (hv : v = 0 -> False) : ((v:Real) = 0 -> False) := by
  intro h
  apply hv
  -- how to get v = 0 from coe = 0?
  exact NNReal.coe_eq_zero.mp h

end ProbabilityTheory
