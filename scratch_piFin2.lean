import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic

open MeasureTheory

namespace Scratch

noncomputable section

example {n : ℕ} (i : Fin (n+1)) (p : ℝ × (Fin n → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm p
      = i.insertNth (α := fun _ : Fin (n+1) => ℝ) p.1 p.2 := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

end

end Scratch
