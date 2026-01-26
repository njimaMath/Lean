import Mathlib.Analysis.Calculus.Deriv.Pow

#check hasDerivAt_id
#check (hasDerivAt_id : HasDerivAt (fun x : Real => x) 1 0)
#check (hasDerivAt_id (0:Real))
