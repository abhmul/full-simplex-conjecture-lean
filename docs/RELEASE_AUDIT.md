# FSC implementation acceptance

All mathematical implementation and acceptance gates passed. The certified formalization source is commit `1915b3485c8d61e531374261e7844010b7538eb9`. Subsequent evidence and runner-coverage integration preserves every tracked Lean source, build pin and axiom-checker file byte-for-byte; [the source-equivalence receipt](../checks/release/source-equivalence.json) checks 135 files and the precise runner-only change. Publication, external acceptance and licensing new work remain separate operator decisions.

## Exact accepted statements

The public import is `FSC`.

| Declaration | Contract |
| --- | --- |
| `FSC.cdf_simplex_le` | Every n≥2, every PSD correlation G, every real t: simplex CDF ≤ G CDF. |
| `FSC.cdf_eq_simplex_iff` | At any fixed t>0, equality iff G is the regular simplex covariance. |
| `FSC.cdf_simplex_lt` | Every nonsimplex correlation has strictly larger CDF at t>0. |
| `FSC.lowerOrthant_simplex_le` | The comparison for actual Gaussian event measures. |
| `FSC.coordinateMax_tail_le_simplex`, `coordinateMax_tail_lt_simplex`, `coordinateMax_tail_eq_simplex_iff` | Actual finite-maximum upper tails: G ≤ simplex for all t, strictness and equality characterization at t>0. |

The CDF is the actual zero-mean multivariate Gaussian lower-orthant probability. The simplex covariance is exactly (1/(n−1))•(n•I−J), with real subtraction. No rank, distinctness, balance, minimum, generic-position, lower-size induction or analytic-certificate hypothesis remains. All project-specific analytic inputs are discharged. Generic helper theorems retain their genuine reusable hypotheses.

## Independent reviews

[The statement review](work-packages/WP25-statement-review.md) compiles public-root consumers with literal Euclidean Gaussian measures, separate PSD/unit-diagonal hypotheses, the explicit constant-one matrix and literal existential coordinate exceedance events. It checks all seven public endpoints, including the reversed maximum-tail order, n=2 and every real comparison threshold.

[The provenance review](work-packages/WP25-provenance-review.md) verifies all ten dependency revisions, all 17 original source hashes, the two intentionally evolved probes and preserved notices for the narrow WSC/mathlib adaptations. The original manuscripts and three supplied audit/symbolic scripts remain byte-identical. No generated private declaration is called.

[The runner review](work-packages/WP25-runner-review.md) independently checks cache suppression, artifact-free startup, exact source identity, fail-closed axiom parsing, required regression coverage and the final receipts. Its final check confirms that the evidence integration does not alter certified Lean source.

## Artifact-free reconstruction

The new source checkout was /tmp/fsc-source-reproduction-20260909T012906Z/checkout, detached at the certified commit. Preparation used independent Git object/source clones with no copied working-tree .lake products, no object hardlinks or alternates, and all ten exact dependency pins. The startup scan found zero compiled artifacts. The installed compiler was Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783; Lake was 5.0.0-src+68218e8.

All sources were rebuilt with process-local `LEAN_NUM_THREADS=2`, `LAKE_NO_CACHE=true`, `LAKE_ARTIFACT_CACHE=false`, `LAKE_CACHE_DIR=`, and `MATHLIB_NO_CACHE_ON_UPDATE=1`, with inherited LEAN_PATH and LEAN_SRC_PATH cleared. Independent review checked these controls in the live Lake process. The pinned WSC/mathlib source and source-pinned ProofWidgets assets required no repair, cache fallback or pin change.

| Gate | Fresh result |
| --- | --- |
| `lake --no-cache build FSC FSCProbes --wfail` | Exit 0; 3,839 jobs, source rebuild 3,105.173 seconds. |
| Separate `lake --no-cache env lean -DwarningAsError=true FSC.lean` | Exit 0; empty output. |
| Public `FSC/Audit.lean` | 45 reports passed, with every final endpoint explicitly covered. |
| Independent expanded statements | 17 reports passed. |
| Original regression suite | 216 reports across 27 files passed. |
| Supplemental mixed/empty/vector adapters | Four reports across three already-committed files passed. |
| Audit calibration | 12 parser tests passed; allowed fixture accepted; custom-axiom and missing-endpoint fixtures correctly rejected. |
| Final source/pins | Clean checkout, unchanged source identity and all ten pins; all pin-file hashes unchanged. |

These are 282 mathematical axiom reports, plus two allowed calibration reports. All accepted axiom sets are subsets of propext/Classical.choice/Quot.sound. The deliberately rejected fixture is outside the libraries. The main runner recorded 3,173.358 seconds across its commands; the three supplemental audits recorded 5.403 seconds. These are measured command durations, not model-productivity estimates.

The source-only preparation receipt is [clean-preparation.json](../checks/release/clean-preparation.json). The 37-command reconstruction receipt and raw logs are in [clean-source](../checks/release/clean-source/verification.json); the three supplemental commands and raw reports are in [clean-adapters](../checks/release/clean-adapters/verification.json). Copies in this repository are byte-identical to the external execution receipts. Original file paths inside JSON diagnostics are preserved.

## Reproduction and maintained runner

Read the project Python-environment instructions, then use its documented specialized interpreter:

```sh
python scripts/prepare_clean_checkout.py --destination /absolute/fresh-parent/checkout
cd /absolute/fresh-parent/checkout
python scripts/verify_release.py --require-clean --evidence /absolute/fresh-parent/evidence
```

The destination and evidence directories must not already exist. The preparing checkout must be committed and clean, with its pinned source dependencies present. Preparation reads Git source objects only. The verified compiler toolchain is installed separately. No public root remote is required.

The maintained runner now includes all 30 regression files in one invocation. Its only change after the certified source commit adds the three already-certified adapter files to REGRESSIONS; the remaining Python AST is identical. A fresh 40-command integration run passed with this consolidated coverage; see [final-runner-integration](../checks/release/final-runner-integration/verification.json). That ordinary-checkout integration receipt is distinguished from the preceding artifact-free reconstruction.

The first preparatory suite's unqualified #print/report-name coverage failure remains preserved in checks/release/current-gates. Only command qualification changed in the affected adverse files; mathematical proof bodies and the fail-closed parser were unchanged. Earlier bootstrap, conditional and failed reports retain their historical scopes.
