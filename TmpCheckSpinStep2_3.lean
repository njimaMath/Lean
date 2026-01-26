import Mathlib
import perceptronFixed.derivative_of_B.derivative_B
import perceptronFixed.Prop_A_P.Prop_A_P

open scoped BigOperators Topology NNReal Real ENNReal Interval
open MeasureTheory Filter

namespace Scratch

noncomputable section

def sech (x : ℝ) : ℝ := 1 / Real.cosh x

lemma log_cosh_le_mul_tanh (x : ℝ) : Real.log (Real.cosh x) ≤ x * Real.tanh x := by
  let f : ℝ → ℝ := fun x => x * Real.tanh x - Real.log (Real.cosh x)
  have hf0 : f 0 = 0 := by
    simp [f]
  have hf_differentiable : Differentiable ℝ f := by
    intro x
    have hg : DifferentiableAt ℝ (fun x => x * Real.tanh x) x := by
      exact ((hasDerivAt_id x).mul (PropAP.hasDerivAt_tanh x)).differentiableAt
    have hh : DifferentiableAt ℝ (fun x => Real.log (Real.cosh x)) x := by
      have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
      exact ((Real.hasDerivAt_log hcosh).comp x (Real.hasDerivAt_cosh x)).differentiableAt
    exact hg.sub hh
  have hderiv : ∀ x : ℝ, deriv f x = x * (sech x) ^ 2 := by
    intro x
    have hmul :
        HasDerivAt (fun x => x * Real.tanh x)
          (Real.tanh x + x * (1 / (Real.cosh x) ^ 2)) x := by
      simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using
        (hasDerivAt_id x).mul (PropAP.hasDerivAt_tanh x)
    have hlog :
        HasDerivAt (fun x => Real.log (Real.cosh x)) (Real.tanh x) x := by
      have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
      have h := (Real.hasDerivAt_log hcosh).comp x (Real.hasDerivAt_cosh x)
      simpa [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
    have hf : HasDerivAt f (x * (sech x) ^ 2) x := by
      have h := hmul.sub hlog
      simpa [f, sech] using h
    simpa using hf.deriv
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (D := Set.Ici 0) (convex_Ici 0)
      (hf_differentiable.continuous.continuousOn) ?_ ?_
    · simpa [interior_Ici] using (hf_differentiable.differentiableOn : DifferentiableOn ℝ f (Set.Ioi 0))
    · intro x hx
      have hx' : (0 : ℝ) < x := by
        simpa [interior_Ici] using hx
      have hx0 : 0 ≤ x := le_of_lt hx'
      have hsech : 0 ≤ (sech x) ^ 2 := by nlinarith
      simpa [hderiv x] using mul_nonneg hx0 hsech
  by_cases hx : 0 ≤ x
  · have h := hmono (a := 0) (b := x) (by simp) hx hx
    have hxnonneg : 0 ≤ f x := by
      simpa [hf0] using h
    exact (sub_nonneg).1 (by simpa [f] using hxnonneg)
  · have hxpos : 0 ≤ -x := by linarith
    have h := hmono (a := 0) (b := -x) (by simp) hxpos hxpos
    have hxnonneg : 0 ≤ f (-x) := by
      simpa [hf0] using h
    have hxnonneg' : 0 ≤ f x := by
      simpa [f, Real.tanh_neg, Real.cosh_neg] using hxnonneg
    exact (sub_nonneg).1 (by simpa [f] using hxnonneg')

end

end Scratch
