import Mathlib
example {α : Type} (R : α → α → Prop) (l : List α) : l.Chain' R ↔ List.IsChain R l := by
  rfl
