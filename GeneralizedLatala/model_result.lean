import latala

open MeasureTheory ProbabilityTheory

namespace SpinGlass
namespace GeneralizedLatala

universe uΩ uι

variable {Ω : Type uΩ} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ) [NeZero N] (β h q : ℝ)
variable (sk : SKDisorder.{uΩ, uι} (Ω := Ω) N β h)
variable (sim : SimpleDisorder.{uΩ, uι} (Ω := Ω) N β q)

/-- The finite-volume SK pressure `φ_N` from the blueprint. -/
noncomputable abbrev finiteVolumePressure : ℝ :=
  interpolatedPressure
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1

/-- The centered overlap moment `E⟨(R₁₂ - q)²⟩` from the blueprint. -/
noncomputable abbrev centeredOverlapSecondMoment : ℝ :=
  overlapVariance
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim) 1

/-- The overlap concentration and replica-symmetric pressure bounds from the blueprint. -/
theorem model_result
    (hN : 0 < N) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfp : IsRSFixedPoint β h q)
    (hρ : rho β q < 1)
    (hIndep : IndepFun sk.U sim.V (ℙ : Measure Ω)) :
    centeredOverlapSecondMoment N β h q sk sim
        ≤ quadraticConstant β q / (lambdaStar β q * (N : ℝ)) ∧
      0 ≤ rsPressure β h q - finiteVolumePressure N β h q sk sim ∧
      rsPressure β h q - finiteVolumePressure N β h q sk sim
        ≤ (β ^ 2 * quadraticConstant β q) /
            (4 * lambdaStar β q * (N : ℝ)) := by
  exact generalized_latala
    (N := N) (β := β) (h := h) (q := q) (sk := sk) (sim := sim)
    hN hq0 hq1 hfp hρ hIndep

end GeneralizedLatala
end SpinGlass
