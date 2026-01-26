import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

#check (hasDerivAt_id (0:Real))
#check (hasDerivAt_id (0:Real)).sub_const (1:Real)
#check (hasDerivAt_id (0:Real)).sub_const (1:Real) |>.pow 2
#check (hasDerivAt_id (0:Real)).sub_const (1:Real) |>.pow 2 |>.neg
#check (hasDerivAt_id (0:Real)).sub_const (1:Real) |>.pow 2 |>.neg |>.div_const (2:Real)
#check Real.hasDerivAt_exp
