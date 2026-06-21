import Mathlib

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

variable {A : Set Ω} (hA : MeasurableSet A)

include hA
theorem measurable_compl_A : MeasurableSet Aᶜ := by
  exact hA.compl

variable {P: Measure Ω} [IsProbabilityMeasure P]


omit hA

theorem P_univ : P Set.univ = 1 := by
  exact MeasureTheory.measure_univ (μ := P)

variable {X: Ω → ℝ} (hX: Measurable X)

theorem my_Markov_inequality  (hXpos : ∀ ω, 0 ≤ X ω) :
    P {ω | 1 ≤ X ω} ≤ ∫⁻ ω, ENNReal.ofReal (X ω) ∂P := by
  sorry

variable {U : Type*}
example {A B : Set U} : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  constructor
  intro hx
  simp at hx
  by_cases hy: x∈ A
  right
  apply hx
  apply hy
  left
  apply hy
  intro hxx h
  rcases hxx with hA | hB
  apply hA
  exact h.1
  apply hB
  exact h.2

example {P Q: Prop}: P → Q  → P∧Q := by
  intro h1 h2
  refine ⟨?_,?_⟩
  exact h1
  exact h2
