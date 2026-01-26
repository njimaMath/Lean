import io
from pathlib import Path

path = Path(r"perceptronFixed/Theorem1/Theorem.lean")
text = path.read_text(encoding="utf-8")
lines = text.splitlines(True)  # keep line endings

start = None
for i, line in enumerate(lines):
    if line.startswith("lemma tendsto_B_atOne_left"):
        start = i
        break
if start is None:
    raise SystemExit("start marker not found")

end = None
for j in range(start + 1, len(lines)):
    if lines[j].startswith("/-!"):
        end = j
        break
if end is None:
    raise SystemExit("end marker not found")

new_block = """lemma tendsto_B_atOne_left (κ : ℝ) :
    Tendsto (fun q => B κ q) (𝓝[<] (1 : ℝ)) (𝓝 (Cκ κ)) := by
  -- `q → 1-` limit gives `Cκ` (main.tex Lemma `B_endpoints`).
  let F : ℝ → ℝ → ℝ := fun q z => (1 - q) * (E (U κ q z)) ^ 2
  let bound : ℝ → ℝ := fun z => 4 * (κ ^ 2 + z ^ 2) + 10

  have hF_meas :
      ∀ᶠ q in (𝓝[<] (1 : ℝ)), AEStronglyMeasurable (fun z : ℝ => F q z) γ := by
    -- Everything is measurable for each fixed `q` (hence a.e. strongly measurable).
    refine Filter.Eventually.of_forall (fun q => ?_)
    have hE_cont : Continuous E := by
      simpa [Theorem1.E, UniformBoundOfG.E] using
        (UniformBoundOfG.E_continuous : Continuous UniformBoundOfG.E)
    have hE_meas : Measurable E := hE_cont.measurable
    have hU_meas : Measurable (fun z : ℝ => U κ q z) := by
      have hmul : Measurable (fun z : ℝ => Real.sqrt q * z) := measurable_const.mul measurable_id'
      have hnum : Measurable (fun z : ℝ => κ - Real.sqrt q * z) := measurable_const.sub hmul
      simpa [U] using hnum.div_const (Real.sqrt (1 - q))
    have hEu : Measurable (fun z : ℝ => E (U κ q z)) := hE_meas.comp hU_meas
    have hpow : Measurable (fun z : ℝ => (E (U κ q z)) ^ 2) := hEu.pow_const 2
    have hF : Measurable (fun z : ℝ => F q z) := by
      simpa [F] using measurable_const.mul hpow
    exact hF.aestronglyMeasurable

  have h_bound : ∀ᶠ q in (𝓝[<] (1 : ℝ)), ∀ᵐ z : ℝ ∂γ, ‖F q z‖ ≤ bound z := by
    refine (Theorem1.integrand_bound κ).mono ?_
    intro q hq
    refine MeasureTheory.ae_of_all _ (fun z => ?_)
    have hnonneg : 0 ≤ F q z := by
      have : 0 ≤ 1 - q := sub_nonneg.2 (le_of_lt hq.2)
      exact mul_nonneg this (sq_nonneg _)
    simpa [F, bound, Real.norm_of_nonneg hnonneg] using hq z

  have bound_int : Integrable bound γ := by
    have hz2_int : Integrable (fun z : ℝ => z ^ 2) γ := by
      simpa [γ] using
        (MeasureTheory.MemLp.integrable_sq
          (ProbabilityTheory.memLp_id_gaussianReal
            (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (p := (2 : ℝ≥0))))
    have hκ2_int : Integrable (fun _ : ℝ => κ ^ 2) γ := by
      simpa using (MeasureTheory.integrable_const (μ := γ) (κ ^ 2))
    have hsum : Integrable (fun z : ℝ => κ ^ 2 + z ^ 2) γ := hκ2_int.add hz2_int
    have hmul : Integrable (fun z : ℝ => (4 : ℝ) * (κ ^ 2 + z ^ 2)) γ := hsum.const_mul 4
    have hconst : Integrable (fun _ : ℝ => (10 : ℝ)) γ := by
      simpa using (MeasureTheory.integrable_const (μ := γ) (10 : ℝ))
    simpa [bound, mul_add, add_assoc, add_left_comm, add_comm] using hmul.add hconst

  have h_lim :
      ∀ᵐ z : ℝ ∂γ,
        Tendsto (fun q : ℝ => F q z) (𝓝[<] (1 : ℝ)) (nhds ((max (κ - z) 0) ^ 2)) := by
    refine MeasureTheory.ae_of_all _ (fun z => ?_)
    simpa [F] using Theorem1.integrand_limit κ z

  have h :=
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := γ) (l := (𝓝[<] (1 : ℝ))) bound hF_meas h_bound bound_int h_lim

  -- Convert back to `B`/`Cκ`.
  have hB :
      (fun q : ℝ => B κ q) =
        (fun q : ℝ => ∫ z : ℝ, F q z ∂γ) := by
    funext q
    -- Move the constant `(1 - q)` inside the integral.
    simpa [B, Expect, F, mul_assoc] using
      (MeasureTheory.integral_const_mul (μ := γ) (1 - q) (fun z : ℝ => (E (U κ q z)) ^ 2)).symm

  simpa [hB, Cκ, Expect, F] using h

"""

new_lines = [ln + ("\n" if not ln.endswith("\n") else "") for ln in new_block.splitlines()]
# Preserve the existing line ending style by using the first line's ending if available.
line_ending = "\n"
for ln in lines:
    if ln.endswith("\r\n"):
        line_ending = "\r\n"
        break
    if ln.endswith("\n"):
        line_ending = "\n"
        break
new_lines = [ln.rstrip("\n") + line_ending for ln in new_lines]

out = "".join(lines[:start] + new_lines + lines[end:])
path.write_text(out, encoding="utf-8")
print(f"Replaced tendsto_B_atOne_left block: lines {start+1}-{end}.")
