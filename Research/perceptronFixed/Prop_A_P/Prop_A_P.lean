import Mathlib

open scoped BigOperators Topology NNReal Interval
open MeasureTheory Filter

namespace PropAP

noncomputable section

/-!
File following `perceptronFixed/Prop_A_P/blueprint.txt`.

Goal: formalize the basic properties of
  - `P(r) = 𝔼[tanh^2(√r Z)]` on `[0,∞)`, and
  - `A(r) = r * (1 - P(r))^2` on `[0,∞)`,
where `Z ~ N(0,1)`.
-/

/-! ## 0. Base measure / expectation -/

/-- Standard normal law on `ℝ`. -/
def γ : Measure ℝ :=
  ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))

abbrev Expect (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂γ

/-! ## Definitions (matching main.tex) -/

/-- Hyperbolic secant `sech(x) = 1 / cosh(x)`. -/
def sech (x : ℝ) : ℝ :=
  (Real.cosh x)⁻¹

/-- `P(r) = 𝔼[tanh^2(√r Z)]` for `Z ~ N(0,1)`. -/
def P (r : ℝ≥0) : ℝ :=
  ∫ z : ℝ, (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 ∂γ

/-- `S(r) = 𝔼[sech^2(√r Z)]` for `Z ~ N(0,1)`. -/
def S (r : ℝ≥0) : ℝ :=
  ∫ z : ℝ, (sech (Real.sqrt (r : ℝ) * z)) ^ 2 ∂γ

/-- `A(r) = r * (1 - P(r))^2`. -/
def A (r : ℝ≥0) : ℝ :=
  (r : ℝ) * (1 - P r) ^ 2

/-! ## Basic identities -/

/-! ### Step A0: pointwise identity `tanh^2 + sech^2 = 1` -/

lemma tanh_sq_add_sech_sq (x : ℝ) : (Real.tanh x) ^ 2 + (sech x) ^ 2 = 1 := by
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hcosh2 : (Real.cosh x ^ 2) ≠ 0 := pow_ne_zero 2 hcosh
  -- Reduce to the identity `cosh^2 = sinh^2 + 1`.
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, sech, inv_pow]
  -- Clear the denominator `cosh(x)^2`.
  field_simp [hcosh2]
  -- `field_simp` turns the goal into `sinh^2 + 1 = cosh^2`.
  simpa using (Real.cosh_sq x).symm

lemma sech_sq_eq_one_sub_tanh_sq (x : ℝ) : (sech x) ^ 2 = 1 - (Real.tanh x) ^ 2 := by
  -- Rearrange the identity `tanh^2 + sech^2 = 1`.
  have h : (Real.tanh x) ^ 2 + (sech x) ^ 2 = 1 := by
    simpa using (tanh_sq_add_sech_sq x)
  linarith

/-! ### Hyperbolic calculus facts (`tanh` continuity/derivative/limits) -/

@[simp] lemma cosh_ne_zero (x : ℝ) : Real.cosh x ≠ 0 :=
  (Real.cosh_pos x).ne'

@[continuity, fun_prop]
lemma continuous_sech : Continuous sech := by
  -- `sech x = (cosh x)⁻¹`, and `cosh` never vanishes.
  simpa [sech] using (Continuous.inv₀ Real.continuous_cosh cosh_ne_zero)

@[continuity, fun_prop]
lemma continuous_tanh : Continuous Real.tanh := by
  have hs : Continuous Real.sinh := Real.continuous_sinh
  have hc : Continuous Real.cosh := Real.continuous_cosh
  have hne : ∀ x : ℝ, Real.cosh x ≠ 0 := fun x => cosh_ne_zero x
  -- `tanh = sinh / cosh`, and `cosh` never vanishes.
  refine (hs.div hc hne).congr ?_
  intro x
  simpa [Pi.div_apply] using (Real.tanh_eq_sinh_div_cosh x).symm

lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / (Real.cosh x) ^ 2) x := by
  have hcosh : Real.cosh x ≠ 0 := cosh_ne_zero x
  -- Differentiate `tanh = sinh / cosh`.
  have h' :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcosh
  -- Simplify the derivative using `cosh^2 - sinh^2 = 1`.
  -- The derivative coming from the quotient rule is
  --   `(cosh x * cosh x - sinh x * sinh x) / (cosh x)^2`.
  have hnum : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    simpa [pow_two] using Real.cosh_sq_sub_sinh_sq x
  -- Rewrite `tanh` and clean up.
  have htanh : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x := by
    funext x
    simpa [Pi.div_apply] using (Real.tanh_eq_sinh_div_cosh x)
  -- Convert the statement from `sinh/cosh` to `tanh`.
  have h : HasDerivAt Real.tanh ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) x := by
    simpa [htanh] using h'
  simpa [hnum, pow_two, one_div] using h

lemma deriv_tanh (x : ℝ) : deriv Real.tanh x = 1 / (Real.cosh x) ^ 2 :=
  (hasDerivAt_tanh x).deriv

lemma strictMono_tanh : StrictMono Real.tanh := by
  refine strictMono_of_deriv_pos ?_
  intro x
  -- `deriv tanh x = 1 / cosh(x)^2 > 0`.
  have hcosh : 0 < Real.cosh x := Real.cosh_pos x
  have hcosh2 : 0 < (Real.cosh x) ^ 2 := pow_pos hcosh 2
  -- `1 / cosh^2` is positive.
  simpa [deriv_tanh, one_div] using (inv_pos.2 hcosh2)

lemma tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 (1 : ℝ)) := by
  -- Use the representation `tanh x = (1 - exp(-2x)) / (1 + exp(-2x))`.
  have hform : (fun x : ℝ => Real.tanh x) =
      fun x => (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
    funext x
    have hx0 : Real.exp x ≠ 0 := Real.exp_ne_zero x
    have hexp : Real.exp (-x) = Real.exp x * Real.exp (-(2 * x)) := by
      -- `-x = x + (-(2x))`.
      have : -x = x + (-(2 * x)) := by ring
      calc
        Real.exp (-x) = Real.exp (x + (-(2 * x))) := by simpa [this]
        _ = Real.exp x * Real.exp (-(2 * x)) := by simp [Real.exp_add]
    -- Start from `tanh_eq` and cancel `exp x`.
    rw [Real.tanh_eq, hexp]
    have hnum : Real.exp x - Real.exp x * Real.exp (-(2 * x)) = Real.exp x * (1 - Real.exp (-(2 * x))) := by
      ring
    have hden : Real.exp x + Real.exp x * Real.exp (-(2 * x)) = Real.exp x * (1 + Real.exp (-(2 * x))) := by
      ring
    rw [hnum, hden, mul_div_mul_left _ _ hx0]
  -- `exp (-(2x)) → 0` as `x → ∞`.
  have hmul : Tendsto (fun x : ℝ => (2 : ℝ) * x) atTop atTop := by
    simpa [mul_comm] using (tendsto_id.atTop_mul_const (show (0 : ℝ) < 2 by norm_num))
  have hexp0 : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul)
  -- Apply continuity of `t ↦ (1 - t)/(1 + t)` at `t = 0`.
  have hcont : ContinuousAt (fun t : ℝ => (1 - t) / (1 + t)) 0 := by
    have : (1 + (0 : ℝ)) ≠ 0 := by norm_num
    -- `div` is continuous when the denominator is nonzero.
    simpa using (continuousAt_const.sub continuousAt_id).div
      (continuousAt_const.add continuousAt_id) this
  -- Finish.
  simpa [hform] using (hcont.tendsto.comp hexp0)

lemma tendsto_tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1 : ℝ)) := by
  -- Use oddness: `tanh(-x) = -tanh(x)`.
  have h : Tendsto (fun x : ℝ => Real.tanh (-x)) atBot (𝓝 (1 : ℝ)) :=
    tendsto_tanh_atTop.comp tendsto_neg_atBot_atTop
  have hneg : Tendsto (fun x : ℝ => -Real.tanh (-x)) atBot (𝓝 (-1 : ℝ)) :=
    h.neg
  -- `-tanh(-x) = tanh x`.
  simpa [Real.tanh_neg] using hneg

/-! ## Properties of `P` (main.tex Lemma `P_properties`) -/

/-! ### Step P0: measurability / integrability helpers -/

lemma measurable_tanh_sq (r : ℝ≥0) :
    Measurable fun z : ℝ => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 := by
  -- `tanh` and `sqrt` are measurable/continuous; composition preserves measurability.
  have hcont : Continuous fun z : ℝ => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 := by
    have h1 : Continuous fun z : ℝ => Real.tanh (Real.sqrt (r : ℝ) * z) :=
      continuous_tanh.comp (continuous_const.mul continuous_id')
    simpa using h1.pow 2
  exact hcont.measurable

lemma tanh_sq_ae_stronglyMeasurable (r : ℝ≥0) :
    AEStronglyMeasurable (fun z : ℝ => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) γ := by
  -- `Measurable` implies `AEStronglyMeasurable`.
  exact (measurable_tanh_sq r).aestronglyMeasurable

lemma tanh_sq_nonneg (r : ℝ≥0) (z : ℝ) :
    0 ≤ (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 := by
  -- Squares are nonnegative.
  nlinarith

lemma tanh_sq_le_one (r : ℝ≥0) (z : ℝ) :
    (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 ≤ 1 := by
  have h := tanh_sq_add_sech_sq (Real.sqrt (r : ℝ) * z)
  have hs : 0 ≤ (sech (Real.sqrt (r : ℝ) * z)) ^ 2 := by
    nlinarith
  linarith

lemma integrable_tanh_sq (r : ℝ≥0) :
    Integrable (fun z : ℝ => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) γ := by
  -- Bounded by `1` and `γ` is a probability measure.
  haveI : IsProbabilityMeasure γ := by
    simpa [γ] using
      (inferInstance :
        IsProbabilityMeasure (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))))
  haveI : IsFiniteMeasure γ := by infer_instance
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) γ :=
    integrable_const (μ := γ) (1 : ℝ)
  refine h1.mono' (tanh_sq_ae_stronglyMeasurable r) ?_
  refine (Filter.Eventually.of_forall fun z => ?_)
  have h0 : 0 ≤ (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 := tanh_sq_nonneg r z
  have hle : (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 ≤ 1 := tanh_sq_le_one r z
  simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle

/-! ### Step A0 (continued): relating `S` and `P` -/

lemma S_eq_one_sub_P (r : ℝ≥0) : S r = 1 - P r := by
  -- Expand definitions, then use the pointwise identity under the integral.
  -- Outline:
  -- 1) `sech^2 = 1 - tanh^2` pointwise.
  -- 2) rewrite the integral of `1 - f` as `1 - integral f` (since `γ` is a probability measure).
  -- 3) conclude `S r = 1 - P r`.
  haveI : IsProbabilityMeasure γ := by
    simpa [γ] using
      (inferInstance :
        IsProbabilityMeasure (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))))
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) γ :=
    integrable_const (μ := γ) (1 : ℝ)
  have h2 : Integrable (fun z : ℝ => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) γ :=
    integrable_tanh_sq r
  have hfun :
      (fun z : ℝ => (sech (Real.sqrt (r : ℝ) * z)) ^ 2) =
        fun z : ℝ => (1 : ℝ) - (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 := by
    funext z
    simpa using (sech_sq_eq_one_sub_tanh_sq (Real.sqrt (r : ℝ) * z))
  -- Rewrite the integrand using `sech^2 = 1 - tanh^2`, then use linearity of the integral.
  simp [S, P, hfun, integral_sub h1 h2, MeasureTheory.integral_const]

lemma A_eq_r_mul_S_sq (r : ℝ≥0) : A r = (r : ℝ) * (S r) ^ 2 := by
  -- Replace `1 - P r` by `S r` and simplify.
  -- This is purely algebraic once `S_eq_one_sub_P` is available.
  simp [A, S_eq_one_sub_P]

/-! ### Steps P2–P3: pointwise monotonicity and strictness -/

lemma tanh_sq_pointwise_mono {r₁ r₂ : ℝ≥0} (h : r₁ ≤ r₂) (z : ℝ) :
    (Real.tanh (Real.sqrt (r₁ : ℝ) * z)) ^ 2 ≤ (Real.tanh (Real.sqrt (r₂ : ℝ) * z)) ^ 2 := by
  -- Split into cases `z = 0`, `z > 0`, `z < 0` as in the blueprint.
  by_cases hz : z = 0
  · simp [hz]
  have hr : (r₁ : ℝ) ≤ (r₂ : ℝ) := by exact_mod_cast h
  have hsqrt : Real.sqrt (r₁ : ℝ) ≤ Real.sqrt (r₂ : ℝ) := Real.sqrt_le_sqrt hr
  have hz' : 0 < z ∨ z < 0 := lt_or_gt_of_ne (ne_comm.mp hz)
  cases hz' with
  | inl hzpos =>
      have harg :
          Real.sqrt (r₁ : ℝ) * z ≤ Real.sqrt (r₂ : ℝ) * z :=
        mul_le_mul_of_nonneg_right hsqrt (le_of_lt hzpos)
      have ht :
          Real.tanh (Real.sqrt (r₁ : ℝ) * z) ≤ Real.tanh (Real.sqrt (r₂ : ℝ) * z) :=
        strictMono_tanh.monotone harg
      have ha : 0 ≤ Real.tanh (Real.sqrt (r₁ : ℝ) * z) := by
        have harg0 : 0 ≤ Real.sqrt (r₁ : ℝ) * z :=
          mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hzpos)
        have h0 := strictMono_tanh.monotone harg0
        simpa using h0
      have hb : 0 ≤ Real.tanh (Real.sqrt (r₂ : ℝ) * z) := le_trans ha ht
      have habs : |Real.tanh (Real.sqrt (r₁ : ℝ) * z)| ≤ |Real.tanh (Real.sqrt (r₂ : ℝ) * z)| := by
        -- `tanh` is nonnegative on nonnegative arguments.
        rw [abs_of_nonneg ha, abs_of_nonneg hb]
        exact ht
      exact (sq_le_sq).2 habs
  | inr hzneg =>
      -- Reduce to the case `-z > 0` using oddness of `tanh`.
      have hzpos : 0 < -z := by linarith
      have harg :
          Real.sqrt (r₁ : ℝ) * (-z) ≤ Real.sqrt (r₂ : ℝ) * (-z) :=
        mul_le_mul_of_nonneg_right hsqrt (le_of_lt hzpos)
      have ht :
          Real.tanh (Real.sqrt (r₁ : ℝ) * (-z)) ≤ Real.tanh (Real.sqrt (r₂ : ℝ) * (-z)) :=
        strictMono_tanh.monotone harg
      have ha : 0 ≤ Real.tanh (Real.sqrt (r₁ : ℝ) * (-z)) := by
        have harg0 : 0 ≤ Real.sqrt (r₁ : ℝ) * (-z) :=
          mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hzpos)
        have h0 := strictMono_tanh.monotone harg0
        simpa using h0
      have hb : 0 ≤ Real.tanh (Real.sqrt (r₂ : ℝ) * (-z)) := le_trans ha ht
      have habs : |Real.tanh (Real.sqrt (r₁ : ℝ) * (-z))| ≤ |Real.tanh (Real.sqrt (r₂ : ℝ) * (-z))| := by
        rw [abs_of_nonneg ha, abs_of_nonneg hb]
        exact ht
      have hsq : (Real.tanh (Real.sqrt (r₁ : ℝ) * (-z))) ^ 2 ≤ (Real.tanh (Real.sqrt (r₂ : ℝ) * (-z))) ^ 2 :=
        (sq_le_sq).2 habs
      simpa [Real.tanh_neg] using hsq

lemma tanh_sq_pointwise_lt_of_lt {r₁ r₂ : ℝ≥0} (h : r₁ < r₂) {z : ℝ} (hz : z ≠ 0) :
    (Real.tanh (Real.sqrt (r₁ : ℝ) * z)) ^ 2 < (Real.tanh (Real.sqrt (r₂ : ℝ) * z)) ^ 2 := by
  -- Use strict monotonicity of `Real.tanh` on `ℝ` together with `hz : z ≠ 0`.
  have hr : (r₁ : ℝ) < (r₂ : ℝ) := by exact_mod_cast h
  have hsqrt : Real.sqrt (r₁ : ℝ) < Real.sqrt (r₂ : ℝ) :=
    Real.sqrt_lt_sqrt r₁.2 hr
  have hz' : 0 < z ∨ z < 0 := lt_or_gt_of_ne (ne_comm.mp hz)
  cases hz' with
  | inl hzpos =>
      have harg :
          Real.sqrt (r₁ : ℝ) * z < Real.sqrt (r₂ : ℝ) * z :=
        mul_lt_mul_of_pos_right hsqrt hzpos
      have ht :
          Real.tanh (Real.sqrt (r₁ : ℝ) * z) < Real.tanh (Real.sqrt (r₂ : ℝ) * z) :=
        strictMono_tanh harg
      have ha : 0 ≤ Real.tanh (Real.sqrt (r₁ : ℝ) * z) := by
        have harg0 : 0 ≤ Real.sqrt (r₁ : ℝ) * z :=
          mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hzpos)
        have h0 := strictMono_tanh.monotone harg0
        simpa using h0
      have hb : 0 ≤ Real.tanh (Real.sqrt (r₂ : ℝ) * z) := le_trans ha (le_of_lt ht)
      have habs : |Real.tanh (Real.sqrt (r₁ : ℝ) * z)| < |Real.tanh (Real.sqrt (r₂ : ℝ) * z)| := by
        rw [abs_of_nonneg ha, abs_of_nonneg hb]
        exact ht
      exact (sq_lt_sq).2 habs
  | inr hzneg =>
      have hzpos : 0 < -z := by linarith
      have harg :
          Real.sqrt (r₁ : ℝ) * (-z) < Real.sqrt (r₂ : ℝ) * (-z) :=
        mul_lt_mul_of_pos_right hsqrt hzpos
      have ht :
          Real.tanh (Real.sqrt (r₁ : ℝ) * (-z)) < Real.tanh (Real.sqrt (r₂ : ℝ) * (-z)) :=
        strictMono_tanh harg
      have ha : 0 ≤ Real.tanh (Real.sqrt (r₁ : ℝ) * (-z)) := by
        have harg0 : 0 ≤ Real.sqrt (r₁ : ℝ) * (-z) :=
          mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hzpos)
        have h0 := strictMono_tanh.monotone harg0
        simpa using h0
      have hb : 0 ≤ Real.tanh (Real.sqrt (r₂ : ℝ) * (-z)) := le_trans ha (le_of_lt ht)
      have habs : |Real.tanh (Real.sqrt (r₁ : ℝ) * (-z))| < |Real.tanh (Real.sqrt (r₂ : ℝ) * (-z))| := by
        rw [abs_of_nonneg ha, abs_of_nonneg hb]
        exact ht
      have hsq :
          (Real.tanh (Real.sqrt (r₁ : ℝ) * (-z))) ^ 2 < (Real.tanh (Real.sqrt (r₂ : ℝ) * (-z))) ^ 2 :=
        (sq_lt_sq).2 habs
      simpa [Real.tanh_neg] using hsq

lemma P_mono {r₁ r₂ : ℝ≥0} (h : r₁ ≤ r₂) : P r₁ ≤ P r₂ := by
  -- Integrate the pointwise inequality from `tanh_sq_pointwise_mono`.
  have hle :
      (fun z : ℝ => (Real.tanh (Real.sqrt (r₁ : ℝ) * z)) ^ 2) ≤ᵐ[γ]
        fun z : ℝ => (Real.tanh (Real.sqrt (r₂ : ℝ) * z)) ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro z
    simpa using tanh_sq_pointwise_mono h z
  simpa [P] using
    (MeasureTheory.integral_mono_ae (integrable_tanh_sq r₁) (integrable_tanh_sq r₂) hle)

lemma P_strictMonoOn_Ici : StrictMonoOn P (Set.Ici (0 : ℝ≥0)) := by
  -- Use `tanh_sq_pointwise_lt_of_lt` plus `γ {0} = 0`.
  intro r₁ _ r₂ _ hlt
  haveI : IsProbabilityMeasure γ := by
    simpa [γ] using
      (inferInstance :
        IsProbabilityMeasure (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))))
  haveI : NoAtoms γ := by
    simpa [γ] using
      (ProbabilityTheory.noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (by simp))
  let f₁ : ℝ → ℝ := fun z => (Real.tanh (Real.sqrt (r₁ : ℝ) * z)) ^ 2
  let f₂ : ℝ → ℝ := fun z => (Real.tanh (Real.sqrt (r₂ : ℝ) * z)) ^ 2
  have hnonneg : 0 ≤ᵐ[γ] fun z => f₂ z - f₁ z := by
    refine Filter.Eventually.of_forall ?_
    intro z
    have hle : f₁ z ≤ f₂ z := by
      simpa [f₁, f₂] using tanh_sq_pointwise_mono (le_of_lt hlt) z
    exact (sub_nonneg).2 hle
  have hfi : Integrable (fun z => f₂ z - f₁ z) γ :=
    (integrable_tanh_sq r₂).sub (integrable_tanh_sq r₁)
  have hsupp : (({0} : Set ℝ)ᶜ) ⊆ Function.support (fun z => f₂ z - f₁ z) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    have hltz : f₁ z < f₂ z := by
      simpa [f₁, f₂] using tanh_sq_pointwise_lt_of_lt hlt (z := z) hz0
    have hne : f₂ z - f₁ z ≠ 0 := ne_of_gt ((sub_pos).2 hltz)
    simpa [Function.support, hne]
  have hcomp : 0 < γ (({0} : Set ℝ)ᶜ) := by
    -- `γ {0} = 0`, hence `γ {0}ᶜ = 1`.
    have : γ (({0} : Set ℝ)ᶜ) = 1 := by
      have h0 : γ ({0} : Set ℝ) = 0 := by simp
      exact (MeasureTheory.prob_compl_eq_one_iff (μ := γ) (s := ({0} : Set ℝ)) (by simp)).2 h0
    simpa [this]
  have hsupp_pos : 0 < γ (Function.support fun z => f₂ z - f₁ z) :=
    lt_of_lt_of_le hcomp (measure_mono hsupp)
  have hint : 0 < ∫ z, (f₂ z - f₁ z) ∂γ :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg_ae (μ := γ) (f := fun z => f₂ z - f₁ z)
        hnonneg hfi).2 hsupp_pos
  have : 0 < P r₂ - P r₁ := by
    simpa [P, f₁, f₂, integral_sub (integrable_tanh_sq r₂) (integrable_tanh_sq r₁)] using hint
  exact (sub_pos).1 this

theorem continuous_P : Continuous P := by
  -- Step P1 (blueprint): dominated convergence with domination by `1`.
  -- Reduce to continuity at each `r₀`, then apply DCT to the integrand
  -- `z ↦ tanh(√r z)^2`.
  haveI : IsProbabilityMeasure γ := by
    simpa [γ] using
      (inferInstance :
        IsProbabilityMeasure (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))))
  haveI : IsFiniteMeasure γ := by infer_instance
  refine (continuous_iff_continuousAt).2 ?_
  intro r₀
  -- Use dominated convergence on the neighborhood filter `𝓝 r₀`.
  have h_meas :
      ∀ᶠ r : ℝ≥0 in 𝓝 r₀,
        AEStronglyMeasurable (fun z : ℝ => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) γ := by
    refine Filter.Eventually.of_forall ?_
    intro r
    exact tanh_sq_ae_stronglyMeasurable r
  have h_bound :
      ∀ᶠ r : ℝ≥0 in 𝓝 r₀,
        ∀ᵐ z : ℝ ∂γ, ‖(Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2‖ ≤ (1 : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro r
    refine Filter.Eventually.of_forall ?_
    intro z
    have h0 : 0 ≤ (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 := tanh_sq_nonneg r z
    have hle : (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 ≤ 1 := tanh_sq_le_one r z
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle
  have h_bound_int : Integrable (fun _ : ℝ => (1 : ℝ)) γ :=
    integrable_const (μ := γ) (1 : ℝ)
  have h_lim :
      ∀ᵐ z : ℝ ∂γ,
        Tendsto (fun r : ℝ≥0 => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) (𝓝 r₀)
          (𝓝 ((Real.tanh (Real.sqrt (r₀ : ℝ) * z)) ^ 2)) := by
    refine Filter.Eventually.of_forall ?_
    intro z
    have hcont : Continuous fun r : ℝ≥0 => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 := by
      have hsqrt : Continuous fun r : ℝ≥0 => Real.sqrt (r : ℝ) :=
        Real.continuous_sqrt.comp NNReal.continuous_coe
      have harg : Continuous fun r : ℝ≥0 => Real.sqrt (r : ℝ) * z := by
        simpa using hsqrt.mul (continuous_const : Continuous fun _ : ℝ≥0 => z)
      have ht : Continuous fun r : ℝ≥0 => Real.tanh (Real.sqrt (r : ℝ) * z) :=
        continuous_tanh.comp harg
      simpa using ht.pow 2
    simpa using (hcont.tendsto r₀)
  have h_tendsto :
      Tendsto
        (fun r : ℝ≥0 => ∫ z : ℝ, (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 ∂γ) (𝓝 r₀)
        (𝓝 (∫ z : ℝ, (Real.tanh (Real.sqrt (r₀ : ℝ) * z)) ^ 2 ∂γ)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := 𝓝 r₀)
      (F := fun r z => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2)
      (f := fun z => (Real.tanh (Real.sqrt (r₀ : ℝ) * z)) ^ 2) (bound := fun _ : ℝ => (1 : ℝ))
      h_meas h_bound h_bound_int h_lim
  simpa [P] using h_tendsto

theorem strictMono_P : StrictMono P := by
  -- Steps P2–P3 (blueprint):
  -- 1) pointwise monotonicity in `r` for each fixed `z`,
  -- 2) strictness for `z ≠ 0` and `γ {0} = 0`.
  intro r₁ r₂ hlt
  exact P_strictMonoOn_Ici (by simp) (by simp) hlt

@[simp] theorem P_zero : P 0 = 0 := by
  -- Step P4: the integrand is identically `0` when `r = 0`.
  simp [P]

theorem P_lt_one (r : ℝ≥0) : P r < 1 := by
  -- Step P5: pointwise strict inequality `tanh(·)^2 < 1`, then strict inequality of integrals.
  haveI : IsProbabilityMeasure γ := by
    simpa [γ] using
      (inferInstance :
        IsProbabilityMeasure (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))))
  haveI : IsFiniteMeasure γ := by infer_instance
  -- Show `S r > 0`, hence `1 - P r > 0`.
  let f : ℝ → ℝ := fun z => (sech (Real.sqrt (r : ℝ) * z)) ^ 2
  have hf_nonneg : 0 ≤ f := by
    intro z
    have : 0 ≤ (sech (Real.sqrt (r : ℝ) * z)) ^ 2 := by nlinarith
    simpa [f] using this
  have hf_integrable : Integrable f γ := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) γ := integrable_const (μ := γ) (1 : ℝ)
    have h2 : Integrable (fun z : ℝ => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) γ :=
      integrable_tanh_sq r
    have hf_eq :
        f = fun z : ℝ => (1 : ℝ) - (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 := by
      funext z
      simpa [f] using (sech_sq_eq_one_sub_tanh_sq (Real.sqrt (r : ℝ) * z))
    simpa [hf_eq] using h1.sub h2
  have hf_ne : ∀ z : ℝ, f z ≠ 0 := by
    intro z
    have hcosh : Real.cosh (Real.sqrt (r : ℝ) * z) ≠ 0 := cosh_ne_zero (Real.sqrt (r : ℝ) * z)
    have hsech : sech (Real.sqrt (r : ℝ) * z) ≠ 0 := by
      simp [sech, hcosh]
    simpa [f] using (pow_ne_zero 2 hsech)
  have hsupp : Function.support f = Set.univ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      simpa [Function.support, hf_ne z]
  have hSpos : 0 < ∫ z, f z ∂γ := by
    have hsupp_pos : 0 < γ (Function.support f) := by
      simpa [hsupp]
    exact
      (MeasureTheory.integral_pos_iff_support_of_nonneg (μ := γ) (f := f) hf_nonneg hf_integrable).2
        hsupp_pos
  have hSpos' : 0 < S r := by
    simpa [S, f] using hSpos
  have hpos : 0 < 1 - P r := by
    simpa [S_eq_one_sub_P r] using hSpos'
  linarith

theorem tendsto_P_atTop : Filter.Tendsto P Filter.atTop (𝓝 (1 : ℝ)) := by
  -- Step P6: for `z ≠ 0`, `tanh(√r z)^2 → 1`; apply dominated convergence.
  haveI : IsProbabilityMeasure γ := by
    simpa [γ] using
      (inferInstance :
        IsProbabilityMeasure (ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))))
  haveI : IsFiniteMeasure γ := by infer_instance
  haveI : NoAtoms γ := by
    simpa [γ] using
      (ProbabilityTheory.noAtoms_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (by simp))
  -- First show that `√r` tends to `+∞` as `r → ∞` in `ℝ≥0`.
  have hsqrt : Tendsto (fun r : ℝ≥0 => Real.sqrt (r : ℝ)) atTop atTop := by
    refine (Filter.tendsto_atTop_atTop).2 ?_
    intro b
    by_cases hb : b ≤ 0
    · refine ⟨0, ?_⟩
      intro r _
      have : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
      exact le_trans hb this
    · let i : ℝ≥0 := ⟨b ^ 2, by nlinarith⟩
      refine ⟨i, ?_⟩
      intro r hr
      have hir : (i : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      have hb2 : b ^ 2 ≤ (r : ℝ) := by simpa [i] using hir
      exact Real.le_sqrt_of_sq_le hb2
  have h_meas :
      ∀ᶠ r : ℝ≥0 in (atTop : Filter ℝ≥0),
        AEStronglyMeasurable (fun z : ℝ => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) γ := by
    refine Filter.Eventually.of_forall ?_
    intro r
    exact tanh_sq_ae_stronglyMeasurable r
  have h_bound :
      ∀ᶠ r : ℝ≥0 in (atTop : Filter ℝ≥0),
        ∀ᵐ z : ℝ ∂γ, ‖(Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2‖ ≤ (1 : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro r
    refine Filter.Eventually.of_forall ?_
    intro z
    have h0 : 0 ≤ (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 := tanh_sq_nonneg r z
    have hle : (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 ≤ 1 := tanh_sq_le_one r z
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle
  have h_bound_int : Integrable (fun _ : ℝ => (1 : ℝ)) γ :=
    integrable_const (μ := γ) (1 : ℝ)
  have h_lim :
      ∀ᵐ z : ℝ ∂γ,
        Tendsto (fun r : ℝ≥0 => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    have hne : ∀ᵐ z : ℝ ∂γ, z ≠ 0 := by
      -- `γ {0} = 0`.
      simp [MeasureTheory.ae_iff]
    filter_upwards [hne] with z hz0
    have hz' : 0 < z ∨ z < 0 := lt_or_gt_of_ne (ne_comm.mp hz0)
    cases hz' with
    | inl hzpos =>
        have harg :
            Tendsto (fun r : ℝ≥0 => Real.sqrt (r : ℝ) * z) atTop atTop :=
          hsqrt.atTop_mul_const hzpos
        have ht : Tendsto (fun r : ℝ≥0 => Real.tanh (Real.sqrt (r : ℝ) * z)) atTop (𝓝 (1 : ℝ)) :=
          tendsto_tanh_atTop.comp harg
        simpa using (ht.pow 2)
    | inr hzneg =>
        have harg :
            Tendsto (fun r : ℝ≥0 => Real.sqrt (r : ℝ) * z) atTop atBot :=
          hsqrt.atTop_mul_const_of_neg hzneg
        have ht :
            Tendsto (fun r : ℝ≥0 => Real.tanh (Real.sqrt (r : ℝ) * z)) atTop (𝓝 (-1 : ℝ)) :=
          tendsto_tanh_atBot.comp harg
        have ht2 :
            Tendsto (fun r : ℝ≥0 => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) atTop
              (𝓝 ((-1 : ℝ) ^ 2)) :=
          ht.pow 2
        simpa using ht2
  -- Apply dominated convergence.
  have h_tendsto :
      Tendsto
        (fun r : ℝ≥0 => ∫ z : ℝ, (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2 ∂γ) atTop
        (𝓝 (∫ z : ℝ, (1 : ℝ) ∂γ)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := atTop)
      (F := fun (r : ℝ≥0) z => (Real.tanh (Real.sqrt (r : ℝ) * z)) ^ 2) (f := fun _ : ℝ => (1 : ℝ))
      (bound := fun _ : ℝ => (1 : ℝ)) h_meas h_bound h_bound_int (by simpa using h_lim)
  simpa [P] using h_tendsto

/-! ## Change-of-variables integral `I(r)` (main.tex Eq. `A_as_I`) -/

/-- Scalar integral used in the representation `A(r) = (1/(2π)) * I(r)^2`. -/
def I (r : ℝ) : ℝ :=
  ∫ y : ℝ, (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))

/-! ### Step A2: elementary facts about the integrand of `I` -/

lemma sech_sq_nonneg (y : ℝ) : 0 ≤ (sech y) ^ 2 := by
  -- Squares are nonnegative.
  nlinarith

lemma exp_neg_sq_div_nonneg (y r : ℝ) : 0 ≤ Real.exp (-(y ^ 2) / (2 * r)) := by
  -- `exp` is always positive.
  exact le_of_lt (Real.exp_pos _)

lemma I_integrand_nonneg (r y : ℝ) : 0 ≤ (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) := by
  -- Product of nonnegative terms.
  exact mul_nonneg (sech_sq_nonneg y) (exp_neg_sq_div_nonneg y r)

lemma sech_sq_pos (y : ℝ) : 0 < (sech y) ^ 2 := by
  -- `cosh y > 0`, so `sech y = (cosh y)⁻¹` is positive, hence its square is positive.
  have hcosh : 0 < Real.cosh y := Real.cosh_pos y
  have hsech : 0 < sech y := by
    simpa [sech] using (inv_pos.2 hcosh)
  simpa using (pow_pos hsech 2)

lemma exp_neg_sq_div_le_one (y r : ℝ) (hr : 0 < r) : Real.exp (-(y ^ 2) / (2 * r)) ≤ 1 := by
  -- For `r > 0`, the exponent is `≤ 0`, so `exp` is `≤ 1`.
  have hy2 : 0 ≤ y ^ 2 := by nlinarith
  have hden : 0 < 2 * r := by nlinarith [hr]
  have hq : 0 ≤ (y ^ 2) / (2 * r) := div_nonneg hy2 (le_of_lt hden)
  have hexp : -(y ^ 2) / (2 * r) ≤ 0 := by
    have : -(y ^ 2 / (2 * r)) ≤ 0 := neg_nonpos.2 hq
    simpa [neg_div] using this
  exact (Real.exp_le_one_iff).2 hexp

lemma exp_neg_sq_div_mono {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ ≤ r₂) (y : ℝ) :
    Real.exp (-(y ^ 2) / (2 * r₁)) ≤ Real.exp (-(y ^ 2) / (2 * r₂)) := by
  -- Monotonicity in `r` of the map `r ↦ exp(-y^2/(2r))` on `(0,∞)`.
  have hy2 : 0 ≤ y ^ 2 := by nlinarith
  have hmul : 2 * r₁ ≤ 2 * r₂ := by nlinarith [h]
  have hinv : 1 / (2 * r₂) ≤ 1 / (2 * r₁) :=
    one_div_le_one_div_of_le (by nlinarith [hr₁]) hmul
  have hdiv : y ^ 2 / (2 * r₂) ≤ y ^ 2 / (2 * r₁) := by
    have hmul' : y ^ 2 * (1 / (2 * r₂)) ≤ y ^ 2 * (1 / (2 * r₁)) :=
      mul_le_mul_of_nonneg_left hinv hy2
    -- Avoid `simp` recursion by rewriting the goal explicitly.
    have hleft : y ^ 2 / (2 * r₂) = y ^ 2 * (1 / (2 * r₂)) := by
      rw [div_eq_mul_one_div]
    have hright : y ^ 2 / (2 * r₁) = y ^ 2 * (1 / (2 * r₁)) := by
      rw [div_eq_mul_one_div]
    -- Now the goal matches `hmul'`.
    simpa [hleft, hright] using hmul'
  have hneg : -(y ^ 2 / (2 * r₁)) ≤ -(y ^ 2 / (2 * r₂)) := neg_le_neg hdiv
  have hexp : -(y ^ 2) / (2 * r₁) ≤ -(y ^ 2) / (2 * r₂) := by
    simpa [neg_div] using hneg
  exact (Real.exp_le_exp).2 hexp

lemma exp_neg_sq_div_lt {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h : r₁ < r₂) {y : ℝ} (hy : y ≠ 0) :
    Real.exp (-(y ^ 2) / (2 * r₁)) < Real.exp (-(y ^ 2) / (2 * r₂)) := by
  -- Strictness for `y ≠ 0`.
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hmul : 2 * r₁ < 2 * r₂ := by nlinarith [h]
  have hinv : 1 / (2 * r₂) < 1 / (2 * r₁) :=
    one_div_lt_one_div_of_lt (by nlinarith [hr₁]) hmul
  have hdiv : y ^ 2 / (2 * r₂) < y ^ 2 / (2 * r₁) := by
    have hmul' : y ^ 2 * (1 / (2 * r₂)) < y ^ 2 * (1 / (2 * r₁)) :=
      mul_lt_mul_of_pos_left hinv hy2
    -- Avoid `simp` recursion by rewriting the goal explicitly.
    have hleft : y ^ 2 / (2 * r₂) = y ^ 2 * (1 / (2 * r₂)) := by
      rw [div_eq_mul_one_div]
    have hright : y ^ 2 / (2 * r₁) = y ^ 2 * (1 / (2 * r₁)) := by
      rw [div_eq_mul_one_div]
    -- Now the goal matches `hmul'`.
    simpa [hleft, hright] using hmul'
  have hneg : -(y ^ 2 / (2 * r₁)) < -(y ^ 2 / (2 * r₂)) := neg_lt_neg hdiv
  have hexp : -(y ^ 2) / (2 * r₁) < -(y ^ 2) / (2 * r₂) := by
    simpa [neg_div] using hneg
  exact (Real.exp_lt_exp).2 hexp

lemma tendsto_exp_neg_sq_div_atTop (y : ℝ) :
    Tendsto (fun r : ℝ => Real.exp (-(y ^ 2) / (2 * r))) atTop (𝓝 (1 : ℝ)) := by
  -- As `r → ∞`, the exponent `-(y^2)/(2r) → 0`, so `exp` tends to `1`.
  have hmul : Tendsto (fun r : ℝ => (2 : ℝ) * r) atTop atTop := by
    simpa [mul_comm] using (tendsto_id.atTop_mul_const (show (0 : ℝ) < 2 by norm_num))
  have hinv : Tendsto (fun r : ℝ => (2 * r)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hmul
  have harg0 : Tendsto (fun r : ℝ => (-(y ^ 2) : ℝ) * (2 * r)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa using (Filter.Tendsto.const_mul (-(y ^ 2) : ℝ) hinv)
  have harg : Tendsto (fun r : ℝ => -(y ^ 2) / (2 * r)) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using harg0
  exact Real.tendsto_exp_nhds_zero_nhds_one.comp harg

theorem integral_sech_sq : (∫ y : ℝ, (sech y) ^ 2) = (2 : ℝ) := by
  -- Compute the integral as an improper integral over `Ioc (-n) n`.
  have hcont : Continuous fun y : ℝ => (sech y) ^ 2 := by
    simpa using continuous_sech.pow 2
  have hderiv : deriv Real.tanh = fun y : ℝ => (sech y) ^ 2 := by
    funext y
    -- `deriv tanh = 1/cosh^2` and `sech^2 = (1/cosh)^2`.
    simp [deriv_tanh, sech, one_div, inv_pow]
  have hinterval (n : ℕ) :
      ∫ y in (-(n : ℝ))..(n : ℝ), (sech y) ^ 2 = 2 * Real.tanh (n : ℝ) := by
    have hdiff : ∀ x ∈ Set.uIcc (-(n : ℝ)) (n : ℝ), DifferentiableAt ℝ Real.tanh x := by
      intro x _hx
      exact (hasDerivAt_tanh x).differentiableAt
    have hcont' :
        ContinuousOn (fun y : ℝ => (sech y) ^ 2) (Set.uIcc (-(n : ℝ)) (n : ℝ)) :=
      hcont.continuousOn
    have hFTC :
        ∫ y in (-(n : ℝ))..(n : ℝ), (sech y) ^ 2 =
          Real.tanh (n : ℝ) - Real.tanh (-(n : ℝ)) := by
      simpa using
        (intervalIntegral.integral_deriv_eq_sub' (a := (-(n : ℝ))) (b := (n : ℝ))
          (f := Real.tanh) (f' := fun y : ℝ => (sech y) ^ 2) hderiv hdiff hcont')
    -- `tanh n - tanh (-n) = 2 * tanh n`.
    simpa [Real.tanh_neg, sub_eq_add_neg, two_mul] using hFTC
  -- Use an `AECover` by `Ioc (-n) n`.
  let a : ℕ → ℝ := fun n => -(n : ℝ)
  let b : ℕ → ℝ := fun n => (n : ℝ)
  have ha : Tendsto a atTop atBot := by
    have hb' : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop (R := ℝ)
    dsimp [a]
    exact tendsto_neg_atTop_atBot.comp hb'
  have hb : Tendsto b atTop atTop := by
    simpa [b] using (tendsto_natCast_atTop_atTop (R := ℝ))
  have hφ : AECover (μ := volume) (l := atTop) (fun n : ℕ => Set.Ioc (a n) (b n)) :=
    aecover_Ioc (μ := volume) (l := atTop) ha hb
  have hnng : 0 ≤ᵐ[volume] fun y : ℝ => (sech y) ^ 2 :=
    Filter.Eventually.of_forall sech_sq_nonneg
  have hfi :
      ∀ n : ℕ, IntegrableOn (fun y : ℝ => (sech y) ^ 2) (Set.Ioc (a n) (b n)) volume := by
    intro n
    have hIcc :
        IntegrableOn (fun y : ℝ => (sech y) ^ 2) (Set.Icc (a n) (b n)) volume := by
      simpa using (hcont.integrableOn_Icc (μ := volume) (a := a n) (b := b n))
    exact hIcc.mono_set (Set.Ioc_subset_Icc_self)
  have htendsto :
      Tendsto (fun n : ℕ => ∫ y in Set.Ioc (a n) (b n), (sech y) ^ 2 ∂volume) atTop (𝓝 (2 : ℝ)) := by
    have htanh : Tendsto (fun n : ℕ => Real.tanh (n : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_tanh_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have htanh2 : Tendsto (fun n : ℕ => 2 * Real.tanh (n : ℝ)) atTop (𝓝 (2 : ℝ)) := by
      simpa using (Filter.Tendsto.const_mul 2 htanh)
    have hrewrite :
        ∀ n : ℕ, 2 * Real.tanh (n : ℝ) = ∫ y in Set.Ioc (a n) (b n), (sech y) ^ 2 ∂volume := by
      intro n
      have hab : a n ≤ b n := by
        have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        linarith [hn]
      calc
        2 * Real.tanh (n : ℝ) = ∫ y in (a n)..(b n), (sech y) ^ 2 ∂volume := by
          simpa [a, b] using (hinterval n).symm
        _ = ∫ y in Set.Ioc (a n) (b n), (sech y) ^ 2 ∂volume := by
          simpa using (intervalIntegral.integral_of_le (μ := volume) (f := fun y : ℝ => (sech y) ^ 2) hab)
    have hrewrite' :
        (fun n : ℕ => 2 * Real.tanh (n : ℝ)) =
          fun n : ℕ => ∫ y in Set.Ioc (a n) (b n), (sech y) ^ 2 ∂volume := by
      funext n
      exact hrewrite n
    simpa [hrewrite'] using htanh2
  -- Conclude by the `AECover` lemma.
  simpa using hφ.integral_eq_of_tendsto_of_nonneg_ae (f := fun y : ℝ => (sech y) ^ 2) (I := (2 : ℝ)) hnng hfi
    htendsto

lemma integrable_sech_sq : Integrable (fun y : ℝ => (sech y) ^ 2) (μ := volume) := by
  -- Use the contrapositive of `integral_undef`.
  by_contra h
  have h0 : (∫ y : ℝ, (sech y) ^ 2) = 0 := MeasureTheory.integral_undef (μ := volume) h
  have : (2 : ℝ) = 0 := by simpa [integral_sech_sq] using h0
  norm_num at this

lemma integrable_I_integrand (r : ℝ) (hr : 0 < r) :
    Integrable (fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) (μ := volume) := by
  -- Dominate by `sech(y)^2`, using `exp(-y^2/(2r)) ≤ 1` for `r > 0`.
  have h_meas :
      AEStronglyMeasurable (fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) volume := by
    have hcont : Continuous fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  refine (integrable_sech_sq).mono' h_meas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have h0 : 0 ≤ (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) :=
    mul_nonneg (sech_sq_nonneg y) (le_of_lt (Real.exp_pos _))
  have hle : (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) ≤ (sech y) ^ 2 := by
    have hexp : Real.exp (-(y ^ 2) / (2 * r)) ≤ 1 := exp_neg_sq_div_le_one y r hr
    have hsech : 0 ≤ (sech y) ^ 2 := sech_sq_nonneg y
    have := mul_le_mul_of_nonneg_left hexp hsech
    simpa [mul_one] using this
  simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle

lemma A_eq_const_I_sq (r : ℝ) (hr : 0 < r) :
    A ⟨r, le_of_lt hr⟩ = (1 / (2 * Real.pi)) * (I r) ^ 2 := by
  -- Change of variables in the Gaussian expectation defining `S(r)`,
  -- then use `A(r) = r * S(r)^2`.
  let rNN : ℝ≥0 := ⟨r, le_of_lt hr⟩
  have hv : rNN ≠ 0 := by
    intro h
    have : (r : ℝ) = 0 := by
      have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
      simpa [rNN] using this
    exact hr.ne' this
  -- Start from `A(r) = r * S(r)^2`.
  have hA : A rNN = (r : ℝ) * (S rNN) ^ 2 := by
    simpa [rNN] using (A_eq_r_mul_S_sq (r := rNN))
  -- Rewrite `S(r)` as an integral under the mapped Gaussian measure.
  have hS_gauss :
      S rNN =
        ∫ y : ℝ, (sech y) ^ 2 ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := rNN)) := by
    let φ : ℝ → ℝ := fun x => Real.sqrt r * x
    let f : ℝ → ℝ := fun y => (sech y) ^ 2
    have hφ_meas : AEMeasurable φ γ := (measurable_const.mul measurable_id').aemeasurable
    have hf_meas : AEStronglyMeasurable f (Measure.map φ γ) :=
      (continuous_sech.pow 2).aestronglyMeasurable
    have hmap :=
      (MeasureTheory.integral_map (μ := γ) (φ := φ) hφ_meas hf_meas (f := f))
    have hS_map : S rNN = ∫ y : ℝ, f y ∂Measure.map φ γ := by
      simpa [S, f, φ, rNN] using hmap.symm
    have hvar : (⟨(Real.sqrt r) ^ 2, sq_nonneg (Real.sqrt r)⟩ : ℝ≥0) = rNN := by
      apply Subtype.ext
      simp [rNN, Real.sq_sqrt (le_of_lt hr)]
    have hmap_measure :
        Measure.map φ γ = ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := rNN) := by
      have h :=
        (ProbabilityTheory.gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
            (c := Real.sqrt r))
      simpa [γ, φ, hvar] using h
    simpa [hS_map, f, hmap_measure]
  -- Rewrite `S` as a Lebesgue integral with the Gaussian density.
  have hS_density :
      S rNN =
        ∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (μ := (0 : ℝ)) (v := rNN) y * (sech y) ^ 2 := by
    have hgauss :
        (∫ y : ℝ, (sech y) ^ 2 ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := rNN))) =
          ∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (μ := (0 : ℝ)) (v := rNN) y • (sech y) ^ 2 := by
      simpa using
        (ProbabilityTheory.integral_gaussianReal_eq_integral_smul (E := ℝ) (μ := (0 : ℝ))
          (v := rNN) (f := fun y : ℝ => (sech y) ^ 2) hv)
    have hgauss' :
        (∫ y : ℝ, (sech y) ^ 2 ∂(ProbabilityTheory.gaussianReal (μ := (0 : ℝ)) (v := rNN))) =
          ∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (μ := (0 : ℝ)) (v := rNN) y * (sech y) ^ 2 := by
      simpa [smul_eq_mul] using hgauss
    simpa [hS_gauss] using hgauss'
  -- Extract the constant `(√(2πr))⁻¹` from the density and match `I(r)`.
  have hS_I : S rNN = (Real.sqrt (2 * Real.pi * r))⁻¹ * I r := by
    have hpdf :
        ∀ y : ℝ,
          ProbabilityTheory.gaussianPDFReal (μ := (0 : ℝ)) (v := rNN) y =
            (Real.sqrt (2 * Real.pi * r))⁻¹ * Real.exp (-(y ^ 2) / (2 * r)) := by
      intro y
      simp [ProbabilityTheory.gaussianPDFReal, rNN, sub_eq_add_neg]
    calc
      S rNN
          = ∫ y : ℝ, ProbabilityTheory.gaussianPDFReal (μ := (0 : ℝ)) (v := rNN) y * (sech y) ^ 2 := hS_density
      _ = ∫ y : ℝ,
            ((Real.sqrt (2 * Real.pi * r))⁻¹ * Real.exp (-(y ^ 2) / (2 * r))) * (sech y) ^ 2 := by
            refine integral_congr_ae ?_
            refine Filter.Eventually.of_forall ?_
            intro y
            simp [hpdf y]
      _ = ∫ y : ℝ,
            (Real.sqrt (2 * Real.pi * r))⁻¹ * ((sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) := by
            refine integral_congr_ae ?_
            refine Filter.Eventually.of_forall ?_
            intro y
            ring_nf
      _ = (Real.sqrt (2 * Real.pi * r))⁻¹ *
            ∫ y : ℝ, (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) := by
            simpa using
              (MeasureTheory.integral_const_mul (μ := volume) ((Real.sqrt (2 * Real.pi * r))⁻¹)
                (fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))))
      _ = (Real.sqrt (2 * Real.pi * r))⁻¹ * I r := by
            simp [I]
  -- Finish: `A = r * S^2 = (1/(2π)) * I^2`.
  have hpos : 0 ≤ 2 * Real.pi * r := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith [hr, hpi]
  calc
    A rNN = (r : ℝ) * (S rNN) ^ 2 := hA
    _ = (r : ℝ) * ((Real.sqrt (2 * Real.pi * r))⁻¹ * I r) ^ 2 := by simp [hS_I]
    _ = (1 / (2 * Real.pi)) * (I r) ^ 2 := by
      calc
        (r : ℝ) * ((Real.sqrt (2 * Real.pi * r))⁻¹ * I r) ^ 2
            = (r : ℝ) * ((Real.sqrt (2 * Real.pi * r))⁻¹) ^ 2 * (I r) ^ 2 := by
                simp [mul_assoc, mul_left_comm, mul_comm, mul_pow]
        _ = (r : ℝ) * ((Real.sqrt (2 * Real.pi * r) ^ 2)⁻¹) * (I r) ^ 2 := by
                simp [inv_pow]
        _ = (r : ℝ) * ((2 * Real.pi * r)⁻¹) * (I r) ^ 2 := by
                simp [Real.sq_sqrt hpos]
        _ = (1 / (2 * Real.pi)) * (I r) ^ 2 := by
                field_simp [hr.ne', Real.pi_ne_zero]

theorem strictMonoOn_I : StrictMonoOn I (Set.Ioi (0 : ℝ)) := by
  -- For `0 < r₁ < r₂`, compare `exp(-y^2/(2r))` pointwise and integrate.
  intro r₁ hr₁ r₂ hr₂ hlt
  let f₁ : ℝ → ℝ := fun y => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁))
  let f₂ : ℝ → ℝ := fun y => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂))
  have hf₁ : Integrable f₁ (μ := volume) := integrable_I_integrand r₁ hr₁
  have hf₂ : Integrable f₂ (μ := volume) := integrable_I_integrand r₂ hr₂
  have hnonneg : 0 ≤ᵐ[volume] fun y => f₂ y - f₁ y := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have hleexp :
        Real.exp (-(y ^ 2) / (2 * r₁)) ≤ Real.exp (-(y ^ 2) / (2 * r₂)) :=
      exp_neg_sq_div_mono hr₁ hr₂ (le_of_lt hlt) y
    have hsech : 0 ≤ (sech y) ^ 2 := sech_sq_nonneg y
    have hle :
        f₁ y ≤ f₂ y := by
      have : (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁)) ≤
          (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂)) :=
        mul_le_mul_of_nonneg_left hleexp hsech
      simpa [f₁, f₂] using this
    exact (sub_nonneg).2 hle
  have hfi : Integrable (fun y => f₂ y - f₁ y) (μ := volume) := hf₂.sub hf₁
  have hsupp : Set.Ioc (0 : ℝ) 1 ⊆ Function.support (fun y => f₂ y - f₁ y) := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    have hlt_exp :
        Real.exp (-(y ^ 2) / (2 * r₁)) < Real.exp (-(y ^ 2) / (2 * r₂)) :=
      exp_neg_sq_div_lt hr₁ hr₂ hlt hy0
    have hsech_pos : 0 < (sech y) ^ 2 := sech_sq_pos y
    have hlt_f : f₁ y < f₂ y := by
      have : (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₁)) <
          (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r₂)) :=
        mul_lt_mul_of_pos_left hlt_exp hsech_pos
      simpa [f₁, f₂] using this
    have hne : f₂ y - f₁ y ≠ 0 := ne_of_gt ((sub_pos).2 hlt_f)
    simpa [Function.support, hne]
  have hIoc_pos : 0 < volume (Set.Ioc (0 : ℝ) 1) := by
    simp [Real.volume_Ioc]
  have hsupp_pos : 0 < volume (Function.support fun y => f₂ y - f₁ y) :=
    lt_of_lt_of_le hIoc_pos (measure_mono hsupp)
  have hint : 0 < ∫ y, (f₂ y - f₁ y) ∂volume :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg_ae (μ := volume) (f := fun y => f₂ y - f₁ y)
        hnonneg hfi).2 hsupp_pos
  have : 0 < I r₂ - I r₁ := by
    simpa [I, f₁, f₂, integral_sub hf₂ hf₁] using hint
  exact (sub_pos).1 this

theorem tendsto_I_atTop : Filter.Tendsto I Filter.atTop (𝓝 (2 : ℝ)) := by
  -- Dominated convergence: `exp(-y^2/(2r)) → 1` and domination by `sech(y)^2`.
  have h_meas :
      ∀ᶠ r : ℝ in (atTop : Filter ℝ),
        AEStronglyMeasurable (fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) volume := by
    refine Filter.Eventually.of_forall ?_
    intro r
    have hcont : Continuous fun y : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  have h_bound :
      ∀ᶠ r : ℝ in (atTop : Filter ℝ),
        ∀ᵐ y : ℝ ∂volume, ‖(sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))‖ ≤ (sech y) ^ 2 := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    refine Filter.Eventually.of_forall ?_
    intro y
    have h0 : 0 ≤ (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) :=
      mul_nonneg (sech_sq_nonneg y) (le_of_lt (Real.exp_pos _))
    have hle : (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r)) ≤ (sech y) ^ 2 := by
      have hexp : Real.exp (-(y ^ 2) / (2 * r)) ≤ 1 := exp_neg_sq_div_le_one y r hr
      have hsech : 0 ≤ (sech y) ^ 2 := sech_sq_nonneg y
      have := mul_le_mul_of_nonneg_left hexp hsech
      simpa [mul_one] using this
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using hle
  have h_lim :
      ∀ᵐ y : ℝ ∂volume,
        Tendsto (fun r : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) atTop (𝓝 ((sech y) ^ 2)) := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have ht : Tendsto (fun r : ℝ => Real.exp (-(y ^ 2) / (2 * r))) atTop (𝓝 (1 : ℝ)) :=
      tendsto_exp_neg_sq_div_atTop y
    have ht' :
        Tendsto (fun r : ℝ => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) atTop (𝓝 ((sech y) ^ 2 * 1)) :=
      Filter.Tendsto.const_mul ((sech y) ^ 2) ht
    simpa using ht'
  have h_tendsto :
      Tendsto (fun r : ℝ => ∫ y : ℝ, (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) atTop
        (𝓝 (∫ y : ℝ, (sech y) ^ 2)) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun r y => (sech y) ^ 2 * Real.exp (-(y ^ 2) / (2 * r))) (f := fun y => (sech y) ^ 2)
      (bound := fun y => (sech y) ^ 2) h_meas h_bound (integrable_sech_sq) h_lim
  simpa [I, integral_sech_sq] using h_tendsto

/-! ## Properties of `A` (main.tex Lemma `A`) -/

@[simp] theorem A_zero : A 0 = 0 := by
  -- `A(0) = 0 * (1 - P 0)^2`.
  simp [A]

theorem continuous_A : Continuous A := by
  -- Continuity follows from continuity of `P` plus algebraic operations.
  unfold A
  simpa [sub_eq_add_neg] using
    (NNReal.continuous_coe.mul ((continuous_const.sub continuous_P).pow 2))

theorem strictMonoOn_A : StrictMonoOn A (Set.Ioi (0 : ℝ≥0)) := by
  -- Use `A(r) = (1/(2π)) * I(r)^2` and strict monotonicity of `I`.
  intro r₁ hr₁ r₂ hr₂ hlt
  have hr₁' : 0 < (r₁ : ℝ) := (NNReal.coe_pos).2 hr₁
  have hr₂' : 0 < (r₂ : ℝ) := (NNReal.coe_pos).2 hr₂
  have hsub₁ : (⟨(r₁ : ℝ), le_of_lt hr₁'⟩ : ℝ≥0) = r₁ := by
    apply Subtype.ext
    rfl
  have hsub₂ : (⟨(r₂ : ℝ), le_of_lt hr₂'⟩ : ℝ≥0) = r₂ := by
    apply Subtype.ext
    rfl
  have hA₁ : A r₁ = (1 / (2 * Real.pi)) * (I (r₁ : ℝ)) ^ 2 := by
    simpa [hsub₁] using (A_eq_const_I_sq (r := (r₁ : ℝ)) hr₁')
  have hA₂ : A r₂ = (1 / (2 * Real.pi)) * (I (r₂ : ℝ)) ^ 2 := by
    simpa [hsub₂] using (A_eq_const_I_sq (r := (r₂ : ℝ)) hr₂')
  have hlt' : (r₁ : ℝ) < (r₂ : ℝ) := by exact_mod_cast hlt
  have hIlt : I (r₁ : ℝ) < I (r₂ : ℝ) :=
    strictMonoOn_I (by simpa [Set.mem_Ioi] using hr₁') (by simpa [Set.mem_Ioi] using hr₂') hlt'
  have hI₁ : 0 ≤ I (r₁ : ℝ) := by
    unfold I
    refine integral_nonneg ?_
    intro y
    exact I_integrand_nonneg (r := (r₁ : ℝ)) (y := y)
  have hI₂ : 0 ≤ I (r₂ : ℝ) := by
    unfold I
    refine integral_nonneg ?_
    intro y
    exact I_integrand_nonneg (r := (r₂ : ℝ)) (y := y)
  have hsq : (I (r₁ : ℝ)) ^ 2 < (I (r₂ : ℝ)) ^ 2 :=
    (sq_lt_sq₀ hI₁ hI₂).2 hIlt
  have hconst : 0 < (1 / (2 * Real.pi) : ℝ) := by
    have hden : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    simpa [one_div] using (inv_pos.2 hden)
  have hmul :
      (1 / (2 * Real.pi) : ℝ) * (I (r₁ : ℝ)) ^ 2 <
        (1 / (2 * Real.pi) : ℝ) * (I (r₂ : ℝ)) ^ 2 :=
    (mul_lt_mul_of_pos_left hsq hconst)
  simpa [hA₁, hA₂] using hmul

theorem tendsto_A_atTop : Filter.Tendsto A Filter.atTop (𝓝 (2 / Real.pi)) := by
  -- First, `I (r : ℝ) → 2` along `r : ℝ≥0 → ∞`.
  have hcoe : Tendsto (fun r : ℝ≥0 => (r : ℝ)) atTop atTop := by
    have : Tendsto (fun r : ℝ≥0 => r) atTop atTop := tendsto_id
    exact (NNReal.tendsto_coe_atTop).2 this
  have hI : Tendsto (fun r : ℝ≥0 => I (r : ℝ)) atTop (𝓝 (2 : ℝ)) :=
    tendsto_I_atTop.comp hcoe
  -- Then the right-hand side tends to `2/π`.
  have hcont : Continuous fun x : ℝ => (1 / (2 * Real.pi)) * x ^ 2 := by
    fun_prop
  have hRHS :
      Tendsto (fun r : ℝ≥0 => (1 / (2 * Real.pi)) * (I (r : ℝ)) ^ 2) atTop
        (𝓝 ((1 / (2 * Real.pi) : ℝ) * (2 : ℝ) ^ 2)) :=
    (hcont.tendsto 2).comp hI
  have hAevent :
      (fun r : ℝ≥0 => (1 / (2 * Real.pi)) * (I (r : ℝ)) ^ 2) =ᶠ[atTop] A := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ≥0)] with r hr0
    have hr0' : 0 < (r : ℝ) := (NNReal.coe_pos).2 hr0
    have hsub : (⟨(r : ℝ), le_of_lt hr0'⟩ : ℝ≥0) = r := by
      apply Subtype.ext
      rfl
    simpa [hsub] using (A_eq_const_I_sq (r := (r : ℝ)) hr0').symm
  have hlimit : (Real.pi⁻¹ * (2 : ℝ)⁻¹ * (2 : ℝ) ^ 2) = (2 / Real.pi : ℝ) := by
    ring_nf
  have hA : Tendsto A atTop (𝓝 ((1 / (2 * Real.pi) : ℝ) * (2 : ℝ) ^ 2)) :=
    Filter.Tendsto.congr' hAevent hRHS
  simpa [hlimit] using hA

theorem range_A : Set.range A = Set.Ico (0 : ℝ) (2 / Real.pi) := by
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    constructor
    · -- `A r ≥ 0`.
      have : 0 ≤ (r : ℝ) := by exact_mod_cast (show (0 : ℝ≥0) ≤ r by simp)
      have : 0 ≤ A r := by
        -- `A r = r * (1 - P r)^2` and both factors are nonnegative.
        have hsq : 0 ≤ (1 - P r) ^ 2 := by nlinarith
        exact mul_nonneg this hsq
      exact this
    · -- `A r < 2/π`.
      by_cases hr0 : r = 0
      ·
        have hpos : (0 : ℝ) < 2 / Real.pi := by
          exact div_pos (by norm_num) Real.pi_pos
        simpa [hr0, A_zero] using hpos
      have hr0' : (0 : ℝ≥0) < r := lt_of_le_of_ne (by simp) (Ne.symm hr0)
      have hlt : r < r + 1 :=
        lt_add_of_pos_right r (by simpa using (one_pos : (0 : ℝ≥0) < 1))
      have hr_mem : r ∈ Set.Ioi (0 : ℝ≥0) := hr0'
      have hr1_mem : r + 1 ∈ Set.Ioi (0 : ℝ≥0) := lt_trans hr0' hlt
      have hA_lt : A r < A (r + 1) := strictMonoOn_A hr_mem hr1_mem hlt
      -- Show `A (r+1) ≤ 2/π` from the limit.
      have hlim := tendsto_A_atTop
      have hevent : (∀ᶠ s : ℝ≥0 in atTop, A (r + 1) ≤ A s) := by
        have hmono : MonotoneOn A (Set.Ioi (0 : ℝ≥0)) := strictMonoOn_A.monotoneOn
        refine (Filter.eventually_ge_atTop (r + 1)).mono (fun s hs => ?_)
        have hs_mem : s ∈ Set.Ioi (0 : ℝ≥0) := by
          exact lt_of_lt_of_le hr1_mem hs
        exact hmono hr1_mem hs_mem hs
      have hlelim : A (r + 1) ≤ 2 / Real.pi := by
        have := (isClosed_Ici.mem_of_tendsto hlim hevent)
        simpa [Set.mem_Ici] using this
      -- Conclude `A r < 2/π` from `A r < A (r+1) ≤ 2/π`.
      exact lt_of_lt_of_le hA_lt hlelim
  · intro hy
    -- `y = 0` is realized at `r = 0`.
    by_cases hy0 : y = 0
    · refine ⟨0, by simpa [hy0, A_zero]⟩
    have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
    -- Find `R` with `y < A R` using the limit `A r → 2/π` and `y < 2/π`.
    have hmem : (2 / Real.pi : ℝ) ∈ Set.Ioi y := hy.2
    have hnhds : Set.Ioi y ∈ 𝓝 (2 / Real.pi : ℝ) :=
      IsOpen.mem_nhds isOpen_Ioi hmem
    have hEventually : ∀ᶠ r : ℝ≥0 in atTop, y < A r :=
      (tendsto_A_atTop).eventually hnhds
    rcases (Filter.eventually_atTop.1 hEventually) with ⟨R, hR⟩
    have h0R : (0 : ℝ≥0) ≤ R := by simp
    have hAR : y < A R := hR R (le_rfl)
    -- Apply IVT on `[0, R]` for the continuous function `A`.
    have hcont : ContinuousOn A (Set.Icc (0 : ℝ≥0) R) :=
      (continuous_A.continuousOn)
    have hyIcc : y ∈ Set.Icc (A (0 : ℝ≥0)) (A R) := by
      have hA0 : A (0 : ℝ≥0) = 0 := by simp [A_zero]
      refine ⟨?_, ?_⟩
      · simpa [hA0] using hypos.le
      · exact le_of_lt hAR
    have hyimg : y ∈ A '' Set.Icc (0 : ℝ≥0) R :=
      (intermediate_value_Icc (a := (0 : ℝ≥0)) (b := R) h0R hcont) hyIcc
    rcases hyimg with ⟨r, hr, rfl⟩
    exact ⟨r, rfl⟩

end
end PropAP
