import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace Scratch

noncomputable section

abbrev E (n : ℕ) := Fin n → ℝ

example {n : ℕ} (i : Fin (n+1)) :
    Topology.IsClosedEmbedding (fun p : ℝ × (Fin n → ℝ) =>
      i.insertNth (α := fun _ : Fin (n+1) => ℝ) p.1 p.2) := by
  admit

end

end Scratch
