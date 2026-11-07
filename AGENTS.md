# Repository instructions

This file applies throughout the `Lean` workspace. Read any additional `AGENTS.md` files governing a directory before changing its contents. Follow the user's current instructions when they override repository guidance.

## Migration scope

The user has requested implementation of the workspace migration. Configuration, toolchain pins, manifests, necessary compatibility fixes, validation and safe removal of redundant dependency copies are authorized. Preserve unrelated work and independent repositories. Record the actual results and any remaining failures in `Lean-migration-report.md`.

## Intended migration

When the user requests implementation, complete these goals together:

- Update to the latest compatible Lean 4 and mathlib versions, verified against upstream at execution time.
- Keep exactly one physical mathlib checkout for this workspace at `<workspace-root>/.lake/packages/mathlib`.
- Keep the existing repositories and their project structure. Adapt their dependency configuration to use that checkout and the same Lean toolchain.
- Check all local Lean source files against the selected versions, including sources outside the current default build targets. Keep proof sources unchanged wherever they remain compatible; make only the smallest necessary compatibility fixes.
- Remove redundant mathlib checkouts only after preserving local changes and verifying the replacement configuration.

Here, `<workspace-root>` is the directory containing this file, currently `C:\Users\Public\Github\Lean`. Use relative paths in project configuration so the workspace remains portable.

The user's priority is one centrally updated mathlib with as few changes to each repository's Lean sources as possible. Prefer changes to Lake configuration, toolchain pins, and manifests over changes to mathematical code. Checking every source does not mean rewriting every source.

## Inspect before changing configuration

- Record the working-tree status and preserve existing edits, deletions, and untracked files. Do not reset, restore, stage, or commit unrelated work.
- Inventory all local `.lean` sources, Lake configurations, manifests, toolchain files, editor settings, and mathlib checkouts. Include ignored folders and nested repositories; ordinary `rg --files` omits some of these.
- Exclude dependency sources, compiler installations, and generated build artifacts from the source migration. Classify generated `.lean` files separately and check their generator or intended use before editing them.
- Identify nested Git repositories, submodules, and filesystem links before moving or deleting anything. A nested repository's sources remain part of the requested compatibility work even if the outer repository ignores them.
- Check both root Lake configurations and retain the union of required libraries, executables, options, and documentation targets when consolidating them. Do not assume the current default target covers the workspace.
- Inspect existing project instructions and build documentation before choosing each folder's integration method.

Original starting points, retained as migration context:

- The root initially had both `lakefile.lean` and `lakefile.toml`; preserve their target union when consolidating them.
- The original Lean and mathlib pins were `v4.32.2`. The 2026-11-07 migration selects stable `v4.35.0`; future updates must recheck upstream.
- Separate project configurations exist under `SYK_CLT`, `SYK_CLT/Blueprint`, `Research/chemical_LDP/Lemma3.9`, `SpinGlass`, and `LeanTokyo`.
- Inspect `research_public`, including `research_public/FPP_tail/FPP_model.lean`, explicitly because the outer Git configuration can hide local sources from ordinary searches.
- The outer repository currently has pre-existing changes. Its `research_public` Git link also needs inspection because `git submodule status` reports a missing `.gitmodules` mapping. Preserve its contents and do not repair Git metadata as an incidental cleanup.

This list is a starting inventory, not an exclusion list.

## Select compatible upstream versions

- Resolve the latest versions from the official Lean releases and the upstream `leanprover-community/mathlib4` repository when implementation begins. Do not guess a release number or treat an existing local pin as current.
- Prefer the newest stable Lean release supported by mathlib, with the newest compatible mathlib release or verified commit. Use a release candidate or nightly only when the user requests it. Explain any gap between the newest Lean release and available mathlib support.
- Read `lean-toolchain` at the exact selected mathlib revision and use that toolchain throughout this workspace. Do not combine a Lean version with incompatible compiled mathlib artifacts.
- The root project owns the mathlib Git dependency. Pin it to a concrete release tag or commit and record the resolved commit in the root Lake manifest. Consumer repositories use local path dependencies, with the root pin determining the shared revision.
- Check compatibility of other dependencies, including Verso and Blueprint packages. Preserve required functionality while reconciling their transitive dependencies with the selected mathlib revision.
- Regenerate manifests with Lake after changing dependency declarations. Do not fabricate resolved revisions by editing lock data manually.
- Use the project toolchain through `elan` and Lake. A change to the machine's global default is not a substitute for updating project pins; do not remove unrelated global toolchains or caches.
- Lean compiler installations are managed by `elan`; `.lake` holds the shared mathlib dependency and build artifacts. Synchronize the retained repositories' `lean-toolchain` files with the toolchain required by the canonical mathlib checkout.

## Share one mathlib checkout

- Treat `<workspace-root>/.lake/packages/mathlib` as the sole canonical mathlib checkout, including its compiled artifacts. Never patch upstream dependency files to make local proofs compile.
- Preserve independent repositories and Lake projects by default. Do not merge their sources into one root project merely to share mathlib. Keep standalone sources in the root workspace where appropriate, preserving existing module names and imports.
- Configure each consumer Lake project to use a relative local path dependency pointing directly to the canonical checkout. Do not use a copied path dependency, a separate Git checkout, or a separate mathlib version pin in a consumer project. Check resolution of mathlib's transitive dependencies as well.
- Only the root project updates the shared mathlib revision. A consumer's dependency update must not replace or independently advance that checkout. Verify the canonical Git commit against the root manifest before validation.
- Do not blindly point independent projects at one shared `packagesDir`; reconcile their manifests and dependency versions first. No project may independently replace the canonical checkout with another revision.
- Consolidate conflicting root configuration files into one authoritative Lake configuration after preserving all required targets and options. Retain independent repositories' configurations and adapt their mathlib dependency declarations in place.
- Retained nested toolchain pins must match the canonical toolchain. Adapt commands, scripts, documentation, and editor configuration so opening or checking a file in a subfolder uses the intended Lake environment.
- Do not use machine-specific absolute paths or ad hoc `LEAN_PATH` overrides as the permanent solution.
- Keep each independent project's own `.lake/build` and Lake configuration artifacts separate. Sharing mathlib does not require sharing every project's entire `.lake` directory. A mathlib dependency's internal build directory is not a second mathlib checkout.
- Document how to initialize the canonical root dependency before building consumer projects on another machine. A relative local path assumes the documented workspace layout and does not by itself pin the checkout's Git commit.

For a consumer project immediately inside the workspace, such as `SYK_CLT`, its mathlib dependency would use one of the following forms, matching that project's authoritative configuration format:

```toml
[[require]]
name = "mathlib"
path = "../.lake/packages/mathlib"
```

```lean
require mathlib from "../.lake/packages/mathlib"
```

Compute the relative path from each actual project directory; a deeper project needs a different path. Do not retain a conflicting `git`, `rev`, or registry-based mathlib declaration alongside the local path.

When updating the central checkout later, synchronize consumer toolchain pins, refresh their manifests through Lake, and recheck their sources. Sharing the checkout makes its new revision visible to all consumers; it does not automatically update their toolchain files or repair incompatible proofs. Avoid updating the checkout while consumer builds are running.

## Adapt local Lean sources

- Establish the baseline build results and record existing proof gaps before changing configuration or sources. Distinguish existing failures from failures introduced by the migration.
- Attempt the configuration and dependency migration with mathematical source files unchanged first. Classify resulting failures before editing sources.
- Preserve mathematical statements, definitions, assumptions, and intended results. Do not weaken a theorem, strengthen its hypotheses, remove a declaration, or disable a target merely to obtain a successful build.
- Edit a local Lean source only when a verified incompatibility requires it. Use the smallest change to obsolete imports, renamed declarations, changed APIs, instance arguments, or tactic syntax, using the selected mathlib sources as the reference.
- Avoid bulk rewrites, formatting changes, import reorganization, module moves, and unrelated proof repairs. Preserve already compiling sources byte for byte whenever possible.
- Search the shared mathlib for the current theorem or API before recreating a result locally. Prefer small, idiomatic changes and shared compatibility helpers where useful.
- Do not introduce `sorry`, `admit`, new axioms, or proof-checking bypasses to hide migration failures. Do not increase existing proof gaps.
- Preserve existing module paths and source directories. If configuration changes expose a module-name collision, prefer separate project boundaries or a configuration fix before renaming sources.
- Include standalone files and developments in ignored or nested repositories. If a file is intentionally generated or cannot be migrated, report its path and the concrete reason; do not silently omit it.

## Remove redundant copies safely

- Locate duplicate mathlib checkouts by their contents and dependency configuration, not just their directory names. Do not delete user-written files merely because they mention mathlib or are named `Mathlib`.
- Inspect each duplicate for tracked changes, untracked files, and unique commits before removal. Preserve any unique work outside the deletion target; never discard it as a cache.
- Complete dependency rewiring and initial validation before removing redundant checkouts. Remove only confirmed redundant dependency copies and obsolete generated artifacts.
- On Windows, resolve each removal target to an absolute path and verify that it lies inside this workspace. Inspect junctions and symbolic links so removing a redundant link cannot remove the canonical checkout or an external directory.
- Use native PowerShell operations with `-LiteralPath` for filesystem cleanup. Do not pass enumerated paths to another shell for deletion.
- Preserve local research sources, nested Git metadata, the canonical mathlib checkout, and required transitive dependencies. Do not delete entire `.lake` trees indiscriminately.

## Verify completion

- Update the canonical mathlib dependency and retrieve its cache from the root after selecting versions. Use `lake exe cache get` for the pinned mathlib revision when needed. Refresh each consumer's manifest through Lake after configuring its path dependency; do not fetch separate mathlib copies in subfolders.
- Verify the actual compiler with `lake env lean --version` and confirm that project pins, manifests, and the shared checkout agree.
- Build every local library, executable, and required documentation target explicitly, or configure an aggregate target that covers them. A successful default `lake build` alone is insufficient unless its coverage has been established.
- Compile all inventoried local source modules in dependency order through their correct Lake workspace. Use `lake env lean <file>` for standalone checks where appropriate, building their imported local modules first.
- Check from each retained independent project that Lake and the editor resolve mathlib to the same physical canonical directory, the canonical Git commit matches the root pin, and the active Lean compiler matches its required toolchain.
- Repeat the dependency-copy inventory after cleanup and after the final builds. Confirm that subsequent Lake commands have not recreated nested mathlib checkouts.
- Record the exact Lean version, mathlib tag and commit, targets and files checked, removed duplicate paths, and any unresolved errors or existing proof gaps. Do not report full migration success while local sources remain unchecked or failing.
- List every mathematical source file that required editing and the specific incompatibility it fixes. Report which repositories compiled without proof-source changes and any substantial compatibility work still needed.

Upstream references: [Lake configuration and dependencies](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/) and [updating a mathlib project](https://leanprover-community.github.io/install/project).

## Mathematical writing and shortcut tags

- Respect the user's vocabulary restrictions. Avoid bold formatting and long dash punctuation.
- Do not number proof stages. Use `$...$` for mathematical formulas in prose. In HTML, use MathJax with dollar delimiters.
- `[math]`: Write as a research mathematician, expressing proof arguments with formulas where possible.
- `[PHYS]`: Use the conventions and precision of a professional physicist.
- `[proofcheck]`: Check the proof line by line and list only errors that have been verified to be actual errors.
- `[numcheck]`: Investigate the claim numerically with numerical-analysis care, distinguishing numerical evidence from proof.
- `[TEACH]`: Explain at undergraduate mathematical-physics level with patient, warm language.
- `[REPHRASE]`: Produce a precise, self-contained problem statement, explicitly defining symbols and assumptions. Add only minimal standard assumptions when necessary.
- Recognize comma-separated tags in square brackets at the beginning of a query, in any order.
