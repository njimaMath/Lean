import Lemmas.Cavity.Stability

open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace SpinGlass.AT

example (β h s : ℝ) :
    let ell : Fin 3 → ℝ := ![1, -2, 1]
    Matrix.vecMul ell (stabilityOperator β (rsQ β h) (rsR β h) s) =
      (1 - s * atParameter β h) • ell := by
  dsimp [stabilityOperator, cavityMatrix, atParameter, rsA]
  funext j
  fin_cases j <;> simp [Matrix.vecMul_eq_sum, Fin.sum_univ_succ] <;> ring

end SpinGlass.AT
