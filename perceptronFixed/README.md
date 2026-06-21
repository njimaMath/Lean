# perceptronFixed

This directory is the Lean 4 formalization accompanying [main.tex](./main.tex) for the paper "Uniqueness of RS Saddle Point for Ising Perceptron".

The submission-facing Lean file is [mainresult.lean](./mainresult.lean). It restates the main definitions and theorem statements in paper notation and then transfers them from the detailed proof development in [Theorem1/Theorem.lean](./Theorem1/Theorem.lean).

## What is formalized

- Existence and uniqueness of the RS saddle point for `0 < alpha < alpha_c(kappa)`, and nonexistence for `alpha >= alpha_c(kappa)`.
- The limiting behavior `q_alpha -> 1` and `r_alpha -> +infty` as `alpha -> alpha_c(kappa)` from below, both in direct manuscript-facing form and in the underlying sequential form used by the proof transfer.
- Divergence of the replica-symmetric free energy to `-infty` along the same limit, again with both direct and sequential statements.
- The closed-form identity `C_kappa = (kappa^2 + 1) Phi(kappa) + kappa phi(kappa)` and the corresponding closed form for `alpha_c(kappa)`.

## Main entry points

- [main.tex](./main.tex): manuscript source.
- [mainresult.lean](./mainresult.lean): compact manuscript-facing interface.
- [Theorem1/Theorem.lean](./Theorem1/Theorem.lean): main formal proof file.
- Supporting analytic lemmas are organized in the sibling directories `conditionalGaussianMoments`, `decreasing_g`, `derivative_of_B`, `Prop_A_P`, `rational_function_bound`, `uniform_bound_of_g`, `negative_F_bound`, `Millo`, and `GIP`.

The third main result is formalized in the namespace `Theorem3`, which is defined inside [Theorem1/Theorem.lean](./Theorem1/Theorem.lean).

## Paper-to-Lean correspondence

- Paper Theorem 1 -> `Theorem1.theorem_main` and `MainResult.main`
- Paper Theorem 2 -> `MainResult.second_main`
- Paper Theorem 3 -> `MainResult.third_main`
- Sequential limit transfer used underneath -> `Theorem1.theorem_second_main_seq`, `MainResult.second_main_seq`, `Theorem3.theorem_three_seq`, and `MainResult.third_main_seq`
- The selected solution branch -> `MainResult.qSol` and `MainResult.rSol`
- Total manuscript-facing extensions of that branch -> `MainResult.qAlpha` and `MainResult.rAlpha`
- The RS value at that solution -> `MainResult.RSStar`
- Total manuscript-facing extension of the RS value -> `MainResult.RSStarAlpha`
- Closed-form setup identities -> `MainResult.Cκ_closed_form` and `MainResult.αc_closed_form`

## Build and verification

This project is pinned by [lean-toolchain](./lean-toolchain) and [lakefile.toml](./lakefile.toml):

- Lean `v4.26.0`
- mathlib `v4.26.0`

From this directory, run:

```bash
lake build perceptronFixed
```

In the current checkout, this command completes successfully.

## Submission workflow

If [main.tex](./main.tex) changes before submission, the file to keep aligned first is [mainresult.lean](./mainresult.lean). The intent is:

1. Update the manuscript.
2. Update `mainresult.lean` so the paper-level notation and statements still match the manuscript.
3. Re-run `lake build perceptronFixed`.

The lower-level modules can remain more detailed than the paper, but the exported statements in `MainResult` should continue to match the submission text.
