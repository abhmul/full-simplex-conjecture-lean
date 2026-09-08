# Environment, ownership, integration and acceptance

## Status and immutable inputs

This is an implementation handoff, not an FSC Lean repository or build certificate. The inspection archive is incomplete as a checkout. The files under `probe_project/` are uncompiled source probes, not a replacement for the supplied WSC sources. No implementation agent was launched and no source repository was modified by this consultation.

Create a new local FSC repository with its own `FSC` namespace, public root, state ledger, statement review and trust audit. Leave the old WSC checkout unchanged. Use these exact dependencies:

| Item | Pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.31.0` |
| WSC repository | `https://github.com/abhmul/weak-simplex-conjecture-lean.git` |
| WSC commit | `a204c53cae45652d12524132dbb9a2e0ffe8cf78` |
| mathlib repository | `https://github.com/leanprover-community/mathlib4.git` |
| mathlib commit | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |

The supplied WSC manifest, toolchain and inspected mathlib source agree on these pins. No claim about the latest remote branch is needed. The new repository must commit its own resolved `lake-manifest.json`, rather than just copying a branch name or relying on an unrecorded cache. The supplied probe project has an explicit direct mathlib pin; dependency resolution must confirm that WSC and FSC use one matching mathlib revision.

The owner chooses a local path. No public repository creation or publication is authorized here. The commands below are instructions for that owner, **not commands executed in this consultation**. They presuppose an actually available matching Lean installation; do not claim success before checking the output.

```sh
cd <new-local-fsc-or-probe-project>
lake --version
lake env lean --version
lake update
# Inspect lake-manifest.json, then verify actual resolved repositories:
git -C .lake/packages/weak-simplex-conjecture-lean rev-parse HEAD
git -C .lake/packages/mathlib rev-parse HEAD
lake build --wfail
lake env lean --json -DwarningAsError=true FSCProbes/Audit.lean
```

Confirm the package checkout paths from Lake's resolved manifest if they differ. `lake update` is for initial resolution of the exact pins; do not permit it silently to float them. The configuration and command forms are source-informed but were not compiler tested here. Capture stdout, stderr, status and the exact commands. The owner may use a verified matching mathlib cache for iteration, but the final clean-clone procedure must have a documented way to reconstruct the result without trusting stale local build products.

## A module graph, not an arbitrary package count

Use narrow imports. The following names describe responsibilities; the owner may merge tiny modules or split large ones in response to compiler evidence.

```
FSC/Definitions
  ├─ Gaussian/AffineLaw ─ Gaussian/CanonicalRegression
  │                       └─ Support/Strips ─ Gaussian/ThresholdExpansion
  │                                           └─ Gaussian/FeasibleVariation
  ├─ Gaussian/CDFContinuity ─ Compactness
  ├─ LinearAlgebra/GramRealization
  ├─ Support/Reciprocal       (existing WSC Prékopa)
  ├─ Support/Dilation        (product density, scaling, moments)
  └─ Scalar/Componentwise

CanonicalRegression + GramRealization + Support/Strips + Support/Dilation
  └─ Facet/IdentitiesAndPositivity

FeasibleVariation + Compactness + Facet/IdentitiesAndPositivity
  └─ Minimizers/FiniteDirections

FiniteDirections + Support/Reciprocal + Scalar/Componentwise
  └─ Minimizers/SlopeAndRigidity  (uses lower-size comparison only)

CDFContinuity + BaseCases + Exclusions + Threshold/LinearBarrier
  + Minimizers/SlopeAndRigidity
  └─ Comparison ─ Equality ─ Main

Audit imports Main, not a conditional scaffold.
```

`Gaussian/FeasibleVariation` also imports a reusable bounded-function/finite-second-moment noise-averaging lemma, preferably in a small analysis module independent of Gaussian laws. `Threshold/LinearBarrier` should be an abstract compact-space argument, independent of matrix calculus. `Support/Reciprocal` should expose the quadratic tangent conclusion, so a proved log-tangent conversion can replace its implementation without changing consumers.

Do not develop both the support/noise and regularized Plackett engines by default. First run the support/noise probe described in `PROBES.md`. Keep the original proof locations as a fallback, not as an untracked second codebase.

## Freeze coupled interfaces together

The definitions of the full-index pair residual, remaining-coordinate success event, pair weights, stress, `k_i`, `C_i`, actual facet supports, and padded dimension must be reviewed together. A single owner should control these public definitions. A change to them requires statement review by the owners of all three analytic identities.

In particular, do not let one worker define pair weights through an arbitrary conditional distribution while another uses explicit regression. Do not silently replace the padded energy by an intrinsic-rank energy. Do not add distinctness to the final CDF or its joint continuity theorem. Covariance differentiation has distinctness and positive-threshold hypotheses; the comparison theorem does not.

Once this interface is frozen, the following can progress independently: scalar comparison and equality; elementary matrix bounds/compactness; generic noise averaging; Gaussian affine laws/regression; generic support differentiation; dilation and padding; reciprocal support convexity; and the abstract barrier. The natural dependency graph controls integration order, not a fixed calendar or quota.

Use disjoint files or branches for parallel work, with explicit ownership and a small state ledger. An interface stub may be described in Markdown or proved as a theorem parameterized by its hypotheses. Do **not** add an `axiom`, opaque oracle, global instance or `sorry` and then treat downstream compilation as a certificate. Conditional assembly is a useful engineering checkpoint only when every outstanding hypothesis is displayed in the exported statement and the file is excluded from the release root.

The research coordinator remains the research-repository writer and mathematical-interface reviewer. The separate implementation owner controls Lean source, integration and worker notes. This consultation does not assume any agent has already accepted ownership.

## Acceptance is mathematical before it is cosmetic

Before accepting a module, record its exact statement, hypotheses, universe/index conventions, relevant source provenance, build command, axiom report and remaining consumers. An accepted public theorem must be kernel checked against the pinned imports, not merely have a plausible signature.

The release-critical statement review must independently verify:

- `cdf` is the all-PSD Gaussian orthant probability; `simplex` has diagonal one and off-diagonal `-1/(n-1)`; no normalized-WSC hypothesis occurs, directly or through a predicate alias.
- The comparison is for all real thresholds and all correlations with n≥2. Singular matrices, duplicated coordinates, antipodes, low ranks and n=2 are not excluded. The equality theorem requires exactly t>0, and proves both directions.
- Singular covariance variations are right derivatives along a proved feasible path. Pair success ignores the two deterministic pinned coordinates. The support derivative differentiates actual supports, not a potentially tied reference.
- Dilation allows unbounded caps and integrates the full padded Gaussian energy. The induction invokes lower-size comparison at the stated rescaled threshold, not lower-size uniqueness or an unproved generic-position perturbation.
- The top-level theorem has no analytic certificate record, assumption bundle, extra typeclass instance, or hidden conditional premise remaining. The final result is not obtained by canceling common Gaussian noise.

These checks are a short statement checklist, not a substitute for the source-specific proofs and negative tests in `PROBES.md`.

## Transitive trust gate

Create `FSC/Audit.lean` importing only the actual release root and containing one `#print axioms` command for each release-critical public theorem, plus key regression, derivative and scalar interfaces. It must include the final comparison and equality theorems. Review the printed final declarations as well, so a theorem with a hidden hypothesis cannot pass merely because it has ordinary axioms.

The allowed set is a **subset** of

```
propext
Classical.choice
Quot.sound
```

A theorem need not use all three. Reject `sorryAx`, every project axiom, every native-computation axiom, and every other unapproved dependency. Checking a fixed name such as `Lean.trustCompiler` is insufficient: current Lean documentation records per-native-computation axiom reporting since 4.29. The whitelist catches names not anticipated by a blacklist.

The supplied `scripts/audit_axioms.py` is original consultation code. It runs a fresh compiler process when invoked in the real project, treats warnings/errors as failure, matches each report to the requested name and source position, verifies coverage, accepts empty-axiom reports, and rejects any axiom outside the whitelist. Its **Python parser** passed synthetic tests here; its interaction with the actual Lean 4.31 JSON output has not been tested. Calibrate it with both successful and deliberately rejected fixture reports before using it as a gate. Do not change it to ignore an unexplained compiler diagnostic.

Example owner command, after replacing paths and theorem names by the final real files:

```sh
python scripts/audit_axioms.py FSC/Audit.lean \
  --required FSC.cdf_simplex_le \
  --required FSC.cdf_eq_simplex_iff \
  --required FSC.cdf_simplex_lt \
  --required FSC.lowerOrthant_simplex_le \
  --save-json checks/fresh-axioms.jsonl
```

The parser's expected source positions deliberately require audit commands at column zero. The file should be a plain import plus commands, without macro-generated or nested audit commands. A schema mismatch must fail closed and be repaired with a captured actual compiler output fixture.

Text searches for placeholders are useful additional checks but not a transitive audit. Ordinary kernel-checked arithmetic tactics are acceptable; do not use a trusted numerical shortcut to bridge the analytic proof. A separate kernel replay or comparator can strengthen assurance when its compatibility has actually been established; no such tool was installed or run here.

## Clean-clone certificate and provenance

Before declaring completion, reproduce the release from a clean checkout of the new FSC repository with the committed toolchain and manifest, verify dependency revisions, rebuild all release modules with warnings treated as errors, run the fresh transitive audit, and run the positive and negative statement tests. Save machine-readable logs and a human-readable statement/provenance report in the repository. A copied `.lake` trace or a past WSC report is not this certificate.

WSC is recorded as MIT-licensed; the selected inspection pack does not include its root LICENSE. Preserve and verify that exact license when obtaining the full pinned checkout. Any narrow adaptation must name original path and commit, identify changed hypotheses, preserve applicable notices, and be recompiled and audited in FSC. The vendored StatLean files carry Apache-2.0 provenance and notices; mathlib is also Apache-2.0. Do not fabricate original attribution from a theorem name. Prefer existing public imports unless measured import/build cost or a clean API boundary justifies adaptation.

The historical WSC validation is useful evidence for workflow design, not present FSC evidence. The improvements here are the early genuinely singular derivative probe, shared-weight interface ownership, strict separation of conditional and closed results, fail-closed fresh report coverage, final statement review, and clean-clone reproduction. No fixed staffing, time estimate, pass quota or public-release schedule follows from this handoff.
