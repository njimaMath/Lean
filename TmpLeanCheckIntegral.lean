import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

#check (ProbabilityTheory.gaussianReal (mu := (0:Real)) (v := (1:NNReal)))
#check (ProbabilityTheory.gaussianReal (mu := (0:Real)) (v := (1:NNReal))).prod
#check MeasureTheory.integral_prod_symm
#check MeasureTheory.integral_prod
