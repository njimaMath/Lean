import Mathlib
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Data.Matrix.Mul

open scoped BigOperators
open MeasureTheory
namespace ProbabilityTheory
noncomputable section
abbrev E (n : ℕ) := Fin n → ℝ
abbrev e (n : ℕ) (i : Fin n) : E n := Pi.single i 1
/-- Standard iid Gaussian measure on Fin n → ℝ. -/
def gaussianStd (n : ℕ) : Measure (E n) :=
  Measure.pi (fun _ : Fin n => gaussianReal (0 : ℝ) (1 : NNReal))

def gaussianLin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Measure (E n) :=
  Measure.map (fun z : E n => A.mulVec z) (gaussianStd n)

def covCoord (n : ℕ) (μ : Measure (E n)) (i j : Fin n) : ℝ :=
  covariance (fun x : E n => x i) (fun x : E n => x j) μ

lemma test {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    covCoord n (gaussianLin A) i j = 0 := by
  classical
  unfold covCoord gaussianLin
  change cov[fun x : E n => x i, fun x : E n => x j; (gaussianStd n).map (fun z : E n => A.mulVec z)] = 0
  have hX : AEStronglyMeasurable (fun x : E n => x i) ((gaussianStd n).map (fun z : E n => A.mulVec z)) := by
    exact (measurable_pi_apply i).aestronglyMeasurable
  have hY : AEStronglyMeasurable (fun x : E n => x j) ((gaussianStd n).map (fun z : E n => A.mulVec z)) := by
    exact (measurable_pi_apply j).aestronglyMeasurable
  have hZ : AEMeasurable (fun z : E n => A.mulVec z) (gaussianStd n) := by
    fun_prop
  rw [covariance_map (μ := gaussianStd n) (Z := fun z : E n => A.mulVec z)
    (X := fun x : E n => x i) (Y := fun x : E n => x j) hX hY hZ]
  -- what is the goal now?
  admit

end ProbabilityTheory
