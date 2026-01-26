import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace Scratch

noncomputable section

example {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) (t : ℝ) :
    Function.update (i.insertNth (α := fun _ : Fin (n+1) => ℝ) (0:ℝ) y) i t
      = i.insertNth (α := fun _ : Fin (n+1) => ℝ) t y := by
  simp

end

end Scratch
