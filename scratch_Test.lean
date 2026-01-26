import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators

namespace Scratch

noncomputable section

abbrev E (n : ℕ) := Fin n → ℝ

abbrev e (n : ℕ) (i : Fin n) : E n := Pi.single i 1

def partialDeriv (n : ℕ) (i : Fin n) (f : E n → ℝ) (x : E n) : ℝ :=
  (fderiv ℝ f x) (e n i)

example {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) (f : E (n+1) → ℝ)
    (hf : Differentiable ℝ f) :
    deriv (fun t : ℝ => f (i.insertNth t y)) 0 = partialDeriv (n+1) i f (i.insertNth 0 y) := by
  admit

end

end Scratch
