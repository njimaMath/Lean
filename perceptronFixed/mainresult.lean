import Mathlib

import perceptronFixed.Theorem1.Theorem


open scoped Topology
open MeasureTheory Filter

namespace MainResult

noncomputable section

abbrev γ : Measure ℝ := Theorem1.γ
abbrev Expect (f : ℝ → ℝ) : ℝ := Theorem1.Expect f

abbrev φ : ℝ → ℝ := Theorem1.φ
abbrev Φbar : ℝ → ℝ := Theorem1.Φbar
def Φ (u : ℝ) : ℝ := 1 - Φbar u
abbrev E : ℝ → ℝ := Theorem1.E

abbrev F (κ q x : ℝ) : ℝ := Theorem1.F κ q x
abbrev P (r : ℝ) : ℝ := Theorem1.P r
abbrev R (κ q α : ℝ) : ℝ := Theorem1.R κ q α
abbrev B (κ q : ℝ) : ℝ := Theorem1.B κ q

abbrev Cκ (κ : ℝ) : ℝ := Theorem1.Cκ κ
abbrev αc (κ : ℝ) : ℝ := Theorem1.αc κ

abbrev IsSolution (κ α q r : ℝ) : Prop := Theorem1.IsSolution κ α q r

abbrev qSol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  Theorem1.qSol κ α hκ hα0 hα

abbrev rSol (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  Theorem1.rSol κ α hκ hα0 hα

abbrev RSFunctional (κ α q r : ℝ) : ℝ := Theorem3.RSFunctional κ α q r
abbrev RSStar (κ α : ℝ) (hκ : 0 ≤ κ) (hα0 : 0 < α) (hα : α < αc κ) : ℝ :=
  Theorem3.RSStar κ α hκ hα0 hα

theorem main
    (κ α : ℝ)
    (hκ : 0 ≤ κ) :
    (0 < α ∧ α < αc κ → ∃! qr : ℝ × ℝ, IsSolution κ α qr.1 qr.2) ∧
    (αc κ ≤ α → ¬ ∃ q r : ℝ, IsSolution κ α q r) := by
  constructor
  · intro hα
    exact Theorem1.theorem_main (κ := κ) (α := α) hκ hα.1 hα.2
  · intro hα
    exact Theorem1.theorem_main_no_solution (κ := κ) (α := α) hκ hα

theorem second_main
    (κ : ℝ) (hκ : 0 ≤ κ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 < α n ∧ α n < αc κ)
    (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    (Tendsto (fun n => rSol κ (α n) hκ (hα n).1 (hα n).2) atTop atTop) ∧
      Tendsto (fun n => qSol κ (α n) hκ (hα n).1 (hα n).2) atTop (𝓝 (1 : ℝ)) := by
  simpa using
    (Theorem1.theorem_second_main_seq (κ := κ) hκ (α := α) (hα := hα) hlim)

theorem third_main
    (κ : ℝ) (hκ : 0 ≤ κ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 < α n ∧ α n < αc κ)
    (hlim : Tendsto α atTop (𝓝 (αc κ))) :
    Tendsto (fun n => RSStar κ (α n) hκ (hα n).1 (hα n).2) atTop atBot := by
  simpa using
    (Theorem3.theorem_three_seq (κ := κ) (hκ := hκ) (α := α) (hα := hα) hlim)

end
end MainResult
