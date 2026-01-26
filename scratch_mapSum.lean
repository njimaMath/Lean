import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.FDeriv.Basic

open scoped BigOperators

namespace Scratch

noncomputable section

variable {n : ℕ}

example (D : (Fin n → ℝ) →L[ℝ] ℝ) (a : Fin n → ℝ) (v : Fin n → Fin n → ℝ) :
    D (∑ j : Fin n, a j • v j) = ∑ j : Fin n, a j • D (v j) := by
  simp

end

end Scratch
