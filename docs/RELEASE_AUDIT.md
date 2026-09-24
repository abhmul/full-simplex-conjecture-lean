# Verification report

Every mathematical implementation and acceptance check passed. The certified formalization source is commit `1915b3485c8d61e531374261e7844010b7538eb9`. The later integration of the evidence and of added coverage in the verification runner (`scripts/verify_release.py`) leaves every tracked Lean source, build pin, and axiom-checker file byte-for-byte unchanged. [The source-equivalence receipt](../checks/release/source-equivalence.json) checks 135 files and records the exact change, which affects only the runner. Journal publication, external acceptance, and licensing of the new work remain separate decisions for the maintainer. The paper was posted as [arXiv:2609.28452](https://arxiv.org/abs/2609.28452) on September 23, 2026.

## Accepted statements

The public import is `FSC`.

| Declaration | Statement |
| --- | --- |
| `FSC.cdf_simplex_le` | For every $n\ge2$, every correlation matrix $G$ (positive semidefinite with unit diagonal), and every real $t$, the CDF of the simplex at $t$ is at most the CDF of $G$ at $t$. |
| `FSC.cdf_eq_simplex_iff` | At each fixed $t>0$, the two CDFs are equal if and only if $G$ is the regular simplex covariance. |
| `FSC.cdf_simplex_lt` | At every $t>0$, every correlation matrix other than the simplex covariance has a strictly larger CDF than the simplex. |
| `FSC.lowerOrthant_simplex_le` | The same comparison for the Gaussian measures of the lower orthant. |
| `FSC.coordinateMax_tail_le_simplex`, `coordinateMax_tail_lt_simplex`, `coordinateMax_tail_eq_simplex_iff` | The upper tail of the maximum coordinate: at every real $t$, the tail for $G$ is at most the tail for the simplex; at $t>0$, the inequality is strict for every $G$ other than the simplex, and equality holds exactly when $G$ is the simplex. |

Here the CDF of $G$ at $t$ is exactly the probability that the centered multivariate Gaussian distribution with covariance $G$ gives the lower orthant, the set of points whose coordinates are all at most $t$. For $n\ge2$, the simplex covariance is exactly $\frac{1}{n-1}(nI-J)$, where $J$ is the all-ones matrix and $n-1$ is computed in the real numbers. No rank, distinctness, balance, minimum, generic-position, lower-size induction, or analytic-certificate hypothesis remains. All project-specific analytic inputs are discharged. Generic helper theorems retain their genuine reusable hypotheses.

## Independent reviews

[The statement review](work-packages/WP25-statement-review.md) compiles a check file that imports only the top-level file `FSC.lean` and restates the theorems with the following written out: the Gaussian measures on Euclidean space, positive semidefiniteness and unit diagonal as separate hypotheses, the all-ones matrix as an explicit constant matrix, and each maximum-tail event as the event that some coordinate exceeds $t$. It checks all seven declarations in the table above, including the reversed inequality for the maximum tail, the case $n=2$, and every real threshold of the comparison.

[The provenance review](work-packages/WP25-provenance-review.md) verifies all ten dependency revisions and the hashes of all 17 original source files. It also verifies the two probe files that were changed on purpose, and the preserved upstream notices of the two short pieces adapted from WSC and mathlib. The original manuscripts and the three supplied scripts (`audit_axioms.py`, `test_audit_axioms.py`, and `symbolic_checks.py`) remain byte-identical. No proof calls a private declaration through its generated name.

[The runner review](work-packages/WP25-runner-review.md) independently checks the suppression of build caches, the absence of compiled files at startup, the exact identity of the sources, the fail-closed parsing of the axiom checker (it fails on any missing or unexpected report instead of ignoring it), the coverage of the required regression tests, and the final receipts. Its final check confirms that the later integration of the evidence does not alter the certified Lean sources.

## Rebuild from scratch

The rebuild from scratch (mode `artifact-free-source-reconstruction` in its receipt) used a new source checkout at `/tmp/fsc-source-reproduction-20260909T012906Z/checkout`, detached at the certified commit. The preparation step made independent Git clones of the sources at all ten exact dependency pins, with no `.lake` build products copied from a working tree and no hard links or alternates to existing Git objects. The scan at startup found zero compiled files. The installed compiler was Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783, and Lake was version 5.0.0-src+68218e8.

All sources were rebuilt with `LEAN_NUM_THREADS=2`, `LAKE_NO_CACHE=true`, `LAKE_ARTIFACT_CACHE=false`, `LAKE_CACHE_DIR=`, and `MATHLIB_NO_CACHE_ON_UPDATE=1` set only for the runner's processes, and with the inherited `LEAN_PATH` and `LEAN_SRC_PATH` cleared. The independent runner review checked these settings in the running Lake process. The pinned WSC and mathlib sources, and the ProofWidgets assets committed in its pinned source, needed no repair, no fallback to a cache, and no change of pin.

| Check | Result |
| --- | --- |
| `lake --no-cache build FSC FSCProbes --wfail` | Exit 0; 3,839 jobs; the rebuild from source took 3,105.173 seconds. |
| Separate `lake --no-cache env lean -DwarningAsError=true FSC.lean` | Exit 0; empty output. |
| Public audit `FSC/Audit.lean` | 45 reports passed; every final declaration was explicitly required. |
| Restated theorems in `checks/release/IndependentStatements.lean` | 17 reports passed. |
| Original regression suite | 216 reports across 27 files passed. |
| Supplemental adapter files (mixed, empty, and vector cases) | Four reports across three already-committed files passed. |
| Axiom-checker calibration | 12 parser tests passed; the valid fixture was accepted; the custom-axiom and missing-declaration fixtures were correctly rejected. |
| Final source and pins | Clean checkout; source identity and all ten pins unchanged; all pin-file hashes unchanged. |

The table accounts for 282 axiom reports on mathematical declarations (45 + 17 + 216 + 4), plus two reports from the valid calibration fixture. Every accepted axiom set is a subset of {`propext`, `Classical.choice`, `Quot.sound`}. The fixture that must be rejected lies outside both libraries. The main runner recorded 3,173.358 seconds across its commands, and the three supplemental audits recorded 5.403 seconds. These are measured command durations, not model-productivity estimates.

The receipt of the source-only preparation is [clean-preparation.json](../checks/release/clean-preparation.json). The receipt of the 37-command rebuild and its raw logs are in [clean-source](../checks/release/clean-source/verification.json). The three supplemental commands and their raw reports are in [clean-adapters](../checks/release/clean-adapters/verification.json). The copies in this repository are byte-identical to the receipts that the run wrote outside it. The JSON diagnostics keep their original file paths.

## Reproduction and the current runner

Use Python 3.10 or newer, as described in [BUILDING.md](BUILDING.md):

```sh
python scripts/prepare_clean_checkout.py --destination /absolute/fresh-parent/checkout
cd /absolute/fresh-parent/checkout
python scripts/verify_release.py --require-clean --evidence /absolute/fresh-parent/evidence
```

The destination and evidence directories must not already exist. The checkout you prepare from must be clean, with everything committed, and its pinned dependency sources must be present. Preparation reads only Git source objects. The verified Lean toolchain is installed separately. The root repository needs no public remote.

The current runner checks all 30 regression files in one invocation. Its only change after the certified commit adds the three adapter files, already certified by the supplemental run above, to its `REGRESSIONS` table. Apart from this addition, the script's Python abstract syntax tree is unchanged. A fresh 40-command integration run passed with this combined coverage; see [final-runner-integration](../checks/release/final-runner-integration/verification.json). That receipt comes from an ordinary checkout and is separate from the rebuild from scratch above.

The first preliminary run of the suite failed its coverage check because some `#print axioms` commands named declarations without their namespace, so the names in the commands did not match the names in the reports. That failure remains preserved in [checks/release/current-gates](../checks/release/current-gates/). The only change to the affected `Adverse.lean` files was to qualify the names in these commands; the mathematical proof bodies and the fail-closed axiom checker were unchanged. Earlier bootstrap, conditional, and failed reports keep their historical scopes.
