# Lean workspace migration, 2026-11-07

Validation is in progress. The dependency configuration is migrated; this is not yet a claim that all research sources compile.

## Selected versions

| Component | Selected revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0` |
| Actual compiler commit | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| mathlib | Stable tag `v4.35.0` |
| Canonical mathlib commit | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Verso Blueprint | `4943d3335ffa9221a39949e60836a8ad5dc2a456`, using Lean 4.35.0 |
| MD4Lean | `6a3fb240133bcb7e1a066fdc784b3fdc304e3fc5`, pinned in root and Blueprint |

The official [Lean release](https://github.com/leanprover/lean4/releases/tag/v4.35.0) and
[mathlib release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0)
were checked when selecting the newest compatible stable versions. Lean 4.36 was
still a release candidate. The selected mathlib revision's `lean-toolchain`
determines every retained project pin. Elan installed the project toolchain;
unrelated global toolchains were retained. The root cache retrieval completed
all 9031 cache files.

The newer transitive MD4Lean revision failed to link the Markdown parser on
Windows (`lean_md4c_markdown_parse`). The selected upstream revision passed
native parser/shared-library tests and the full Blueprint library, site
generation and reference checks. Lake regenerated both manifests; comparison
confirmed that this adjustment changed only MD4Lean's package record.

## Dependency layout

The root owns the mathlib Git pin and Lake-generated resolved manifest. Consumer
manifests were regenerated with Lake and verified against the canonical Git
commit and mathlib's transitive dependency revisions.

| Lake project | Direct mathlib path, relative to the project |
| --- | --- |
| Workspace root | Git dependency at `.lake/packages/mathlib` |
| `SYK_CLT` | `../.lake/packages/mathlib` |
| `SYK_CLT/Blueprint` | `../../.lake/packages/mathlib` |
| `Research/chemical_LDP/Lemma3.9` | `../../../.lake/packages/mathlib` |
| `SpinGlass` | `../.lake/packages/mathlib` |
| `LeanTokyo` | `../.lake/packages/mathlib` |
| `research_public/perceptronFixed/Lean` | `../../../.lake/packages/mathlib` |

The LeanGame native checker uses the same compiler and imports core Lean only.
Its optional mathlib environment comes from LeanTokyo's `lake env`. Its npm
dependencies, course content, and native checker source were retained. The old
LeanTokyo packages-directory junction was removed as a link only. LeanTokyo
now has its own physical `.lake/packages` directory. The standard local package
layout also matches mathlib's dependency artifact cache paths.

The root `lakefile.lean` retains the target/option union of the former two root
configurations. `lakefile.toml` is removed. Independent project boundaries and
module names are retained; legacy root SYK target names forward to that
project's complete library. Perceptron's own Lake environment separates its
`SpinGlass.*` modules from GeneralizedLatala's copies; both root Perceptron aliases
share one forwarding build job. Extra globs expose formerly uncovered local leaves.
The generated TeX listing is excluded from module targets.

Root, SYK and Perceptron libraries use the documented Lean compatibility option
`backward.isDefEq.respectTransparency.types = false`; normal kernel checking
remains enabled. Some proofs also need the new `simpa using!` form for default
transparency. No dependency source was patched to make proofs compile.

Setup instructions and the existing CI checkout layout were adapted to initialize
the root dependency before consumer builds. Workflow YAML and local verification
scripts were checked statically; no remote workflow was run or deployment made.

## Preservation and baseline

The initial root, nested-repository, ignored-source, link and dependency inventory
is retained locally in `.lake/migration-audit/inventory-before.json`; original
configuration files and selected source backups are in that audit directory.
No unrelated files were reset, restored, staged or committed. Pre-existing
deletions, untracked research sources and the broken `research_public` submodule
mapping were preserved.

Before the upgrade, `lake build RSATMain` passed with Lean 4.32.2. A broader
baseline already found failures in `percolation/PercolationZd.lean`,
`Research/oriented_animal/animal_bound/starconnected.lean` and
`Research/oriented_animal/animal_comparison/animal_comparison.lean`, together
with stale root SYK paths and a cGM/CGM filename collision. The broad baseline
did not finish, so failures elsewhere cannot all be classified as pre-existing.

The initial actual modules contained 18 `sorry` occurrences and four declared
axioms across the recorded research developments. These were not introduced by
the migration. New FPP developments appeared during validation and include
intentional statement placeholders governed by their own instructions. A passing
elaboration of such a file is not a proof of its admitted claims.

## Validation records

The table records native command results. Failed multi-target commands do not
mean that every target failed. Per-module compiler artifacts, source freshness
and direct-check results are recorded in `.lake/migration-audit/module-results.json`.
Unchecked dependency cones must not be treated as checked. Full command output
and exact diagnostics are retained in the local audit directory.

The portable [source-status table](Lean-migration-source-status.tsv) lists every
inventoried module, its project, source SHA256, result and blocking import when
known. Successful compiler artifacts must match the exact Lean 4.35 compiler
commit and Lake source hash. Five standalone checks are recorded separately.
Sources in LeanGame's `.local` directories are generated stories and rehearsal
copies, checked through their generators and native game tests. The 34 content
fragments are compiler inputs assembled by that checker. The generated
`percolation/FPPtex/*.listings.lean` file is a TeX output, not a source module.

| Check | Result | Seconds |
| --- | --- | --- |
| `environment-checkouts` | Passed | 34.66 |
| `environments-final` | Pending | |
| `smoke-mathlib` | Passed | 100.73 |
| `game-types` | Passed | 2.69 |
| `build-game` | Passed | 39.61 |
| `game-content` | Passed | 137.03 |
| `game-integration` | Passed | 93.66 |
| `game-browser` | Passed | 249.54 |
| `game-mathlib-fixed` | Passed | 7.66 |
| `build-syk-final` | Passed | 304.86 |
| `build-rsat-glat-verified` | Passed | 260.61 |
| `build-perceptron-passed` | Passed | 54.16 |
| `build-blueprint-linked` | Passed | 824.62 |
| `blueprint-site-linked` | Passed | 50.61 |
| `blueprint-check-linked` | Passed | 5.2 |
| `root-syk-md4lean` | Passed | 701.79 |
| `documentation-checkouts` | Passed | 0.22 |
| `md4lean-parser-build` | Passed | 3.24 |
| `md4lean-parser-run` | Passed | 1.19 |
| `build-Research-chemical_LDP-Lemma3_9` | Passed | 347.27 |
| `build-spin-complete-check` | Failed, exit 1 | 56.01 |
| `parisi-wrapper-final` | Failed, exit 1 | 78.76 |
| `parisi-leaf-axioms` | Passed | 21.44 |
| `spin-map-compat-audit` | Passed | 21.07 |
| `gaussian-comparison-axioms` | Passed | 18.68 |
| `gaussian-map-obstruction-final` | Passed | 14.72 |
| `gaussian-review-proposal-fixed` | Passed | 44.58 |
| `standalone-0` | Passed | 135.54 |
| `standalone-proposition19-final` | Passed | 85.62 |
| `standalone-2` | Passed | 28.93 |
| `standalone-lemma5-final` | Passed | 34.8 |
| `standalone-4` | Passed | 39.43 |
| `build-tap-complete` | Pending | |
| `build-root-validated-targets` | Pending | |
| `tap-all-final` | Pending | |
| `tap-presentation-final` | Pending | |
| `tap-audit-final` | Pending | |
| `tap-extension-final` | Pending | |
| `build-fpp-snapshot-final` | Pending | |
| `percolation-final-check` | Failed, exit 1 | 38.21 |
| `workflow-static` | Passed | 0.39 |

The game checks include 93 uncached real checks across 23 exercises, 17
integration tests and three real browser workflows. Command-scoped
`LEAN_NUM_THREADS=2` limits memory pressure during large Lean checks. A stalled
`starconnected.lean` compiler was stopped after more than 35 minutes with no
CPU progress; its broad build result is not a completed check of that file.

All eight Lake environments reported Lean 4.35.0; all seven mathlib consumers
(including the root owner) resolved exactly the same physical mathlib directory.
Root VS Code language-server process paths also showed Lean 4.35.0. SpinGlass
has a pre-existing Git ownership mismatch for dependency repositories. Validation
uses command-scoped `safe.directory` entries, as does its Parisi wrapper; no
global Git safety configuration or filesystem ownership was changed. An editor
started under a different Windows account may still encounter that ownership
restriction.

## Mathematical source changes

These are compatibility edits to initially inventoried modules. Statements,
hypotheses and mathematical formulas were retained. Files not listed were not
edited by this migration. Separately recorded concurrent work under `FPP_tail`
includes new modules and a later change to the initially inventoried model file;
that directory was left untouched by this migration.

| Source | Compatibility change |
| --- | --- |
| `2Dcollision/lean_formalization/Proposition19/proposition19.lean` | Adapt conversion/simpa transparency, coordinate measurability and product bounds; unfold lowerCutoff explicitly. |
| `percolation/PercolationZd.lean` | Limit two singleton-mass simplifications affected by the new simplifier behavior; preserve baseline proof failures. |
| `Research/chemical_LDP/Lemma5.4/lemma5_4.lean` | Use Fin.removeNth_apply explicitly when checking equality of projected coordinates. |
| `Research/KignmanSubadditiveErgodic/KSE.lean` | Adapt simpa transparency and bridge strict invariant-set ergodicity to the new PreErgodic interface. |
| `Research/TAP_ANNEALED/Main_overlap.lean` | Import Lean.Elab.Recall after the command moved into Lean; presentation bodies and claims retained. |
| `Research/TAP_ANNEALED/Lemmas/Aristotle/Calculus/AnalyticDivision.lean` | Use the ordered-ring product bound prod_le_one₀. |
| `Research/TAP_ANNEALED/Lemmas/FixedOverlap/HerglotzCircle.lean` | Import the MeanValue module that owns the harmonic mean-value theorem. |
| `Research/TAP_ANNEALED/Lemmas/FixedOverlap/SpectralRealMeasure.lean` | Infer the probability instance for the unchanged boundary-value pushforward. |
| `Research/TAP_ANNEALED/Lemmas/FixedOverlap/SpectralZero.lean` | Use the current probability instance for a mapped measure. |
| `research_public/generalizedLatala/SpinGlass/Core/Defs.lean` | Make distribution of a scalar over a finite sum explicit in the Gibbs derivative proof. |
| `research_public/generalizedLatala/SpinGlass/Gaussian/ComplexIBP.lean` | Adapt simpa transparency and Lp norm names/arguments; remove a tactic after simp already closes its goal. |
| `research_public/generalizedLatala/SpinGlass/Interpolation/GibbsBridge.lean` | Adapt simpa transparency when coercing the existing Gibbs weights to real numbers. |
| `research_public/generalizedLatala/SpinGlass/Interpolation/GuerraToninelli.lean` | Apply the now-pointwise Fin.addCases identity, and use explicit function continuity/transparency APIs. |
| `research_public/generalizedLatala/SpinGlass/Mathlib/Probability/Distributions/GaussianIntegrationByParts.lean` | Use measurable_norm and Measurable.norm for real-valued absolute values. |
| `research_public/generalizedLatala/SpinGlass/Mathlib/Probability/Distributions/Gaussian_IBP_Hilbert.lean` | Replace the removed Real.CompleteField import, use norm measurability, and adapt simpa transparency in the isolated Perceptron copy. |
| `research_public/generalizedLatala/SpinGlass/Replica/Replicas.lean` | Use Measurable.of_eval and prod_le_one₀ with the existing nonnegativity proofs. |
| `research_public/perceptronFixed/Lean/decreasing_g/decreasing_g.lean` | Match the lowercase cGM import to the actual module filename. |
| `research_public/perceptronFixed/Lean/derivative_of_B/derivative_B.lean` | Derive AE measurability from the Gaussian law using its null singletons and the new nonmeasurable-map fallback. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Potential.lean` | Transport the cylinder sigma-algebra equality explicitly; use pointwise measurability APIs and simpa using!. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Specification.lean` | Use mapped probability instances, current forall/DFunLike names, explicit kernel simplification and simpa transparency. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/SpinGlass.lean` | Use pointwise measurable multiplication, negation and addition in the existing finite sums. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Examples/Arithmetic.lean` | Use pointwise measurable subtraction/multiplication and transport singleton-cylinder coercions explicitly. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` | Import LpSeminorm.Indicator, the current owner of MemLp.indicator. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Mathlib/MeasureTheory/Measure/Prod.lean` | Qualify Set.prod_mono to avoid the new measure lemma with the same short name. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Prereqs/CylinderEvents.lean` | Adapt simpa transparency and transport measurable sets along the proved sigma-algebra equality. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Prereqs/LebesgueCondExp.lean` | Use simpa using! for the function-valued equality. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Prereqs/Kernel/CondExp.lean` | Use simpa using! for conditional-expectation coercions. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Prereqs/Kernel/Feller.lean` | Use simpa using! for the continuous-map coercion. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Prereqs/Kernel/Proper.lean` | Make indicator integrability and function-one simplification explicit; supply Lp measurability; adapt simpa transparency. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Specification/ChoquetLaw.lean` | Use the current zero_le lemma and simpa using! for measurable-set coercions. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Specification/ErgodicDecomposition.lean` | Use the mapped probability instance for the unchanged tail-kernel law. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Specification/Extremal.lean` | Transport the proved equality of tail sigma-algebras explicitly. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Specification/Quasilocal.lean` | Mark the unchanged definition noncomputable because its instance is noncomputable. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Specification/QuasilocalSpecification.lean` | Use simpa using! for closure and submodule coercions. |
| `research_public/perceptronFixed/Lean/GibbsMeasure/Specification/Structure.lean` | Use simpa using! when identifying a measurable preimage with its set-builder form. |
| `research_public/perceptronFixed/Lean/Millo/Mill.lean` | Use simpa using! where the supplied proof needs default transparency. |
| `research_public/perceptronFixed/Lean/SpinGlass/Calculus.lean` | Use simpa using! for smoothness coercions and pointwise function division. |
| `research_public/perceptronFixed/Lean/SpinGlass/ComplexIBP.lean` | Adapt simpa transparency and Lp norm names/arguments; remove a tactic after simp already closes its goal. |
| `research_public/perceptronFixed/Lean/SpinGlass/Defs.lean` | Adapt derivative transparency, use pointwise scalar conversions, remove a closed proof tail and normalize scalar finite sums. |
| `research_public/perceptronFixed/Lean/SpinGlass/GibbsBridge.lean` | Adapt simpa transparency when coercing the existing Gibbs weights to real numbers. |
| `research_public/perceptronFixed/Lean/SpinGlass/GuerraToninelli.lean` | Apply the now-pointwise Fin.addCases identity, and use explicit function continuity/transparency APIs. |
| `research_public/perceptronFixed/Lean/SpinGlass/KS_inequality.lean` | Use explicit quotient/log derivative APIs and adapt simpa transparency in summability proofs. |
| `research_public/perceptronFixed/Lean/SpinGlass/Replicas.lean` | Use coordinate measurability and the nonnegative product bound, adapt simpa transparency, and expose the unchanged NNReal scalar action. |
| `research_public/perceptronFixed/Lean/SpinGlass/SKModel.lean` | Name the existing probability-space and basis-index universes explicitly, preserving arbitrary basis-index universes. |
| `research_public/perceptronFixed/Lean/SpinGlass/Mathlib/Probability/Distributions/GaussianIntegrationByParts.lean` | Use measurable_norm and Measurable.norm for real-valued absolute values. |
| `research_public/perceptronFixed/Lean/SpinGlass/Mathlib/Probability/Distributions/Gaussian_IBP_Hilbert.lean` | Replace the removed Real.CompleteField import, use norm measurability, and adapt simpa transparency in the isolated Perceptron copy. |
| `research_public/perceptronFixed/Lean/Theorem1/Theorem.lean` | Match the lowercase cGM import to its filename and use Integrable.fun_neg for function negation. |
| `research_public/RSAT/Lemmas/AT/PsiContinuity.lean` | Use Set.domRestrict, the current domain-restriction API in ContinuousOn. |
| `research_public/RSAT/Lemmas/Cavity/Estimates.lean` | Remove four no-op simp calls after norm_num already performs their simplifications. |
| `research_public/RSAT/Lemmas/Cavity/Interpolation.lean` | Use prod_le_one₀ and run the existing algebra normalization on the goal left by the current convert tactic. |
| `research_public/RSAT/Lemmas/CLT/CLT_Main.lean` | Infer the probability proof for the unchanged mapped overlap law. |
| `research_public/RSAT/Lemmas/Concentration/Weak.lean` | State the set-membership inequality explicitly before applying linarith to the existing bounds. |
| `research_public/RSAT/Lemmas/Price/Cosh.lean` | Package the existing continuous linear map measurability and Gaussian law equality as HasLaw for mgf_gaussianReal. |
| `research_public/RSAT/Lemmas/Price/Gaussian.lean` | Use the current mapped probability-measure instance. |
| `research_public/RSAT/Lemmas/Price/Key.lean` | Use PiLp.single_apply after the Euclidean-space lemma moved. |
| `research_public/RSAT/Lemmas/Price/Moments.lean` | Use PiLp.single_apply after the Euclidean-space lemma moved. |
| `research_public/RSAT/Lemmas/SpinGlass/Defs.lean` | Make distribution of a scalar over a finite sum explicit in the Gibbs derivative proof. |
| `research_public/RSAT/Lemmas/SpinGlass/GaussianIntegrationByParts.lean` | Use measurable_norm and Measurable.norm for real-valued absolute values. |
| `research_public/RSAT/Lemmas/SpinGlass/gaussian_concentration.lean` | Adapt mapped probability and Gaussian-law instances, and coordinate measurability with Measurable.of_eval. |
| `research_public/RSAT/Lemmas/SpinGlass/Gaussian_IBP_Hilbert.lean` | Replace the removed Real.CompleteField import, use norm measurability, and adapt simpa transparency in the isolated Perceptron copy. |
| `research_public/RSAT/Lemmas/SpinGlass/Replicas.lean` | Use Measurable.of_eval and prod_le_one₀ with the existing nonnegativity proofs. |
| `SpinGlass/Common/Mathlib/MeasureTheory/Measure/InvariantWeakLimit.lean` | Pass the existing continuous function explicitly to ProbabilityMeasure.map. |
| `SpinGlass/Common/Mathlib/Probability/InfinitePiMarginal.lean` | Use Measurable.of_eval for coordinatewise measurability. |
| `SpinGlass/Common/Mathlib/Probability/ProductMeasureProd.lean` | Use Measurable.of_eval for the existing coordinatewise zip maps. |
| `SpinGlass/Common/Mathlib/Probability/Distributions/Gaussian_ComparisonIndep.lean` | Supply existing measurability to Gaussian-law integrability; handle the new nonmeasurable-map Dirac fallback without changing the joint-law lemma statement. |
| `SpinGlass/Common/Mathlib/Probability/Distributions/Gaussian_ProdCovariance.lean` | Supply the existing measurability hypotheses to IsGaussian.hasGaussianLaw. |
| `SpinGlass/Common/Mathlib/Probability/Distributions/Gaussian/CameronMartinIBPAnalytic.lean` | Remove five proof tails after convert now closes their goals. |
| `SpinGlass/Common/Mathlib/Probability/Distributions/Gaussian/CameronMartinThm.lean` | Infer the probability instances for the existing mapped laws. |
| `SpinGlass/Common/Mathlib/Probability/Distributions/Gaussian/MultivariateSum.lean` | Infer the probability proof for the existing mapped product law. |
| `SpinGlass/Common/Mathlib/Probability/Distributions/Gaussian/SubGaussian.lean` | Package the existing measurability and Gaussian map equality as HasLaw for mgf_gaussianReal. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/CascadeBranchLaw.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. Use Set.equivOfEq for the unchanged range subtype equivalence. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/CascadeNodeMarks.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/CascadePair.lean` | Use Measurable.of_eval for pair-coordinate projections. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/CascadeTiltMeasure.lean` | Use Measurable.of_eval for Fin.tail. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/CascadeTrunc.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. Use Set.equivOfEq for the unchanged range subtype equivalence. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/CascadeUnzip.lean` | Use Measurable.of_eval for the existing nested coordinate maps. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/Marking.lean` | Use Measurable.of_eval for the existing zip maps. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/Mecke.lean` | Use Measurable.of_eval for the existing coordinatewise sample updates. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/PoissonFinite.lean` | Use the mapped probability instance and prod_le_one₀ with the existing nonnegativity proof. |
| `SpinGlass/Common/Mathlib/Probability/PointProcess/PoissonSuperposition.lean` | Import the shared map compatibility theorem, and use Measurable.of_eval and prod_le_one₀. |
| `SpinGlass/SpinGlass/Defs.lean` | Import the shared local map compatibility theorem to preserve existing proof calls. |
| `SpinGlass/SpinGlass/FreeEnergyConvexity.lean` | Derive the existing L2 function measurability from its proved smoothness. |
| `SpinGlass/SpinGlass/GaussFieldFluctuation.lean` | Derive free-energy measurability from the existing smoothness theorem after MemLp stopped carrying measurability. |
| `SpinGlass/SpinGlass/MixedPSpinComponent.lean` | Supply the existing measurable function proof to the current L2 norm formula. |
| `SpinGlass/SpinGlass/ParisiFunctional.lean` | Package measurable identity and map_id as HasLaw for mgf_gaussianReal. |
| `SpinGlass/SpinGlass/Poincare.lean` | Derive free-energy measurability from its proved smoothness instead of projecting it from MemLp. |
| `SpinGlass/SpinGlass/ReplicaSymmetricBound.lean` | Supply measurable identity to IsGaussian.hasGaussianLaw for the same Gaussian measure. |
| `SpinGlass/SpinGlass/SKDisorderExists.lean` | Supply the existing measurable projection proofs to IsGaussian.hasGaussianLaw. |
| `SpinGlass/SpinGlass/SKModel.lean` | Derive the unchanged free-energy measurability claims from proved smoothness. |
| `SpinGlass/SpinGlass/ThermodynamicLimit.lean` | Supply the existing measurable projections and constant-function measurability to IsGaussian.hasGaussianLaw. |
| `SpinGlass/SpinGlass/FiniteGibbs/GaussianFieldCoords.lean` | Pass the existing measurable-coordinate proof and probability measure to IsGaussian.hasGaussianLaw. |
| `SpinGlass/SpinGlass/FiniteGibbs/GaussianFieldProd.lean` | Supply the existing composition measurability proof to IsGaussian.hasGaussianLaw. |
| `SpinGlass/SpinGlass/FiniteGibbs/Poincare.lean` | Derive free-energy measurability from its proved smoothness instead of projecting it from MemLp. |
| `SpinGlass/SpinGlass/FiniteGibbs/ReplicaCalculus.lean` | Use prod_le_one₀, which accepts the existing nonnegativity hypothesis. |
| `SpinGlass/SpinGlass/Limit/ExchangeableArray.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Limit/OverlapArrayBracket.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Analytic/Concentration.lean` | Pass the existing measurable indicator set as a null-measurable set to MemLp.indicator. |
| `SpinGlass/SpinGlass/Parisi/Analytic/FieldTruncation.lean` | Infer the probability proof for the unchanged clipped field law. |
| `SpinGlass/SpinGlass/Parisi/Concentration/PairBranchFactorization.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Coupled/CoupledBoundLaw.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Coupled/CoupledLambdaZero.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Coupled/CoupledSite.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Coupled/Derivative/Zero.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Field/FieldLawContinuity.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Field/RandomExternalField.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Interpolation/CascadeMarkTransport.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Interpolation/PairFractionIntegral.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Interpolation/PairFractionLaw.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SpinGlass/SpinGlass/Parisi/Tree/PairTreeFieldIndep.lean` | Use Measurable.of_eval with the same explicitly typed restriction functions. |
| `SpinGlass/SpinGlass/Parisi/Tree/SiteTreeFieldLaw.lean` | Replace the obsolete coordinate-function use of measurable_pi_lambda with Measurable.of_eval; retain all statements. |
| `SYK_CLT/SYK/Main.lean` | Use the current mapped probability-measure instance for the disorder law. |
| `SYK_CLT/SYK/Analysis/Matrix/SingularValues.lean` | Import Matrix.Spectrum explicitly for the Hermitian eigenbasis and eigenvector unitary. |
| `SYK_CLT/SYK/Analysis/Matrix/TraceExpDerivatives.lean` | Expose the iterated derivative import used by public derivative statements. |
| `SYK_CLT/SYK/Analysis/Matrix/TraceExponential.lean` | Import the matrix C-star algebra and spectrum modules explicitly for operator norms and eigenvalues. |
| `SYK_CLT/SYK/CLT/FiniteModel.lean` | Import Matrix.Normed explicitly for the scoped matrix operator norm and its continuity API. |
| `SYK_CLT/SYK/CLT/Chaos/PartitionDerivatives.lean` | Import ParametricIntegral explicitly for differentiation under the integral. |
| `SYK_CLT/SYK/Probability/DistributionTransfer.lean` | Pass the function explicitly to ProbabilityMeasure.map and infer the mapped probability instances. |
| `SYK_CLT/SYK/Probability/GaussianMomentDetermination.lean` | Import Analytic.Uniqueness explicitly for the analytic identity principle. |
| `SYK_CLT/SYK/Probability/LpDistributionTransfer.lean` | Adapt Lp exponent comparison and supply measurability to the L1 norm formula. |
| `SYK_CLT/SYK/Probability/GaussianConcentration/StandardGaussian.lean` | Use the current mapped probability-measure instance. |

The new local module
`SpinGlass/Common/Mathlib/MeasureTheory/Measure/MapCompat.lean` restores the old
measurable-map probability theorem interface using the current mathlib theorem.
Two foundation imports cover 19 other local files without rewriting their proof
calls. Native compilation and its axiom audit pass; it uses only `propext`,
`Classical.choice` and `Quot.sound`.

## Cleanup and remaining errors

The redundant `.lake/spinglass/packages/mathlib` checkout was removed after
dependency rewiring and successful compiler/path verification. The duplicate audit checked
the old SpinGlass mathlib and all eight embedded dependency repositories for
tracked/untracked changes, unique local commits and filesystem links. These
checks found no unique work or links. The absolute removal target was verified
inside this workspace and distinct from canonical mathlib, then removed with
native PowerShell. The post-cleanup inventory found exactly one mathlib checkout.
Project and dependency layout scans found no remaining filesystem links in
their inspected paths. Checkout inventories are retained in the audit directory.

The obsolete `LeanTokyo/.lake/cache-packages-before-layout` directory was also
removed after the replacement mathlib probe passed. It contained generated
artifacts only, with no source, Git metadata or filesystem links.

Two constraints currently prevent a complete SpinGlass migration:

- Its pinned upstream GibbsMeasure commit
  `8a158f018c55665542e071c6c0e54906f903a199` targets Lean 4.34.0-rc2. It fails
  under 4.35.0 in martingale, conditional-expectation, invariant-sigma-algebra,
  measure-monad and coordinate-measurability APIs. All 13 published branch
  toolchains and the tags were inspected. No branch declares 4.35 support;
  main still targets 4.34.0-rc2 and lacks required DeFinetti and martingale
  modules. Switching to main would remove required functionality. Dependency
  sources were left unchanged, as AGENTS.md requires.
- `SpinGlass/Common/Mathlib/Probability/Distributions/Gaussian/Real.lean` uses
  the removed `aemeasurable_of_map_neZero` in `gaussianReal_sub_const'`.
  The original unrestricted statement cannot be recovered by renaming an API:
  mathlib now assigns a fixed Dirac measure to a non-AE-measurable map of a
  nonzero measure. At variance zero the hypothesis no longer forces AE
  measurability, and translation need not translate that fixed fallback.
  The theorem was left unchanged because AGENTS.md forbids strengthening its
  hypotheses. A review-only variant with explicit `AEMeasurable X m` was checked
  outside the source tree and passed with only the three standard axioms; it
  has not been applied. Its local path is
  `.lake/migration-audit/gaussian-proposal.lean`. No local caller of the original
  theorem was found.
  A second native diagnostic proves that for any non-AE-measurable real map
  under a nonzero measure there is a zero-variance Gaussian law whose
  translation by one violates the original conclusion. This diagnostic also
  uses only the three standard axioms.

Additional root failures remain in `percolation/PercolationZd.lean` and the
oriented-animal development. Percolation still reports the same 13 baseline
errors after two migration-specific simplifier fixes. Baseline checks already
reported four errors in `animal_bound/starconnected.lean` and one in
`animal_comparison/animal_comparison.lean`. The later broad check of
`total_percolation.lean` reports 16 diagnostics; its original baseline did not
finish, so these are not all classified as pre-existing. No compatibility
success is claimed for these files or their dependent modules. The preserved
baseline also contains proof placeholders; migration introduced none.

FPP sources are being edited concurrently outside this migration. The original
`FPP_model.lean` passed unchanged before those edits. The final FPP command
checks the files discovered when that build starts; the source-status table
requires matching captured hashes before marking current files successful.
Later edits and newly created files require another check. FPP source files
were not edited by this migration.

## Source coverage snapshot

Inventory captured at the recorded validation snapshot. This covers 1533 local modules, 34 content fragments and 1130 separately classified generated files.

The exhaustive checkout scan inspected 124 toolchain files, including ignored directories, and found only `.lake/packages/mathlib`.

| Project | Passed | Errors recorded | Blocked by imports | Other unchecked |
| --- | --- | --- | --- | --- |
| Blueprint | 6 | 0 | 0 | 0 |
| Game | 1 | 0 | 0 | 0 |
| LDP | 1 | 0 | 0 | 0 |
| Perceptron | 57 | 0 | 0 | 0 |
| SYK | 54 | 0 | 0 | 0 |
| SpinGlass | 220 | 1 | 279 | 0 |
| root | 886 | 4 | 5 | 19 |

The source-status table contains the individual paths and captured hashes. Blocked and unchecked files have not been certified under Lean 4.35.0.

Modified compatibility sources without a complete passing check:

- `percolation/PercolationZd.lean`: error-logged.
- `Research/TAP_ANNEALED/Main_overlap.lean`: unverified-or-blocked.
- `SpinGlass/SpinGlass/Limit/ExchangeableArray.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Limit/OverlapArrayBracket.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Concentration/PairBranchFactorization.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Coupled/CoupledBoundLaw.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Coupled/CoupledLambdaZero.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Coupled/CoupledSite.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Coupled/Derivative/Zero.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Field/FieldLawContinuity.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Field/RandomExternalField.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Interpolation/CascadeMarkTransport.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Interpolation/PairFractionIntegral.lean`: blocked-by-import.
- `SpinGlass/SpinGlass/Parisi/Interpolation/PairFractionLaw.lean`: blocked-by-import.

LeanTokyo's native checker and `Research/chemical_LDP/Lemma3.9` compiled without mathematical source changes. The standalone collision main, distance lemma and swapping development also passed unchanged.
