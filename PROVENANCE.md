# Sources, attribution, and licensing

## Project status

The formalization accompanies the paper [arXiv:2609.28452](https://arxiv.org/abs/2609.28452). The [README](README.md#relation-to-the-paper) states which of the paper's results are formalized, and [RELEASE_AUDIT.md](docs/RELEASE_AUDIT.md) records the formalization's exact scope and verification evidence. The original mathematical inputs and consultation notes in [docs/sources/](docs/sources/README.md) and [docs/pro-return/](docs/pro-return/) retain their original bytes. [SOURCE_MANIFEST.json](docs/SOURCE_MANIFEST.json) records their provenance and hashes.

A project-wide license for newly authored FSC material has not yet been selected. The licenses and notices below apply to the identified upstream material.

## Pinned dependencies

| Dependency | Revision | Upstream license |
| --- | --- | --- |
| [Weak Simplex Conjecture Lean](https://github.com/abhmul/weak-simplex-conjecture-lean/tree/a204c53cae45652d12524132dbb9a2e0ffe8cf78) | `a204c53cae45652d12524132dbb9a2e0ffe8cf78` | MIT for project-authored code; its vendored StatLean components retain Apache-2.0 |
| [mathlib](https://github.com/leanprover-community/mathlib4/tree/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f) | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` | Apache-2.0 |

Lean is pinned to `leanprover/lean4:v4.31.0`. [lake-manifest.json](lake-manifest.json) records all ten resolved package revisions. Lake fetches the dependencies, and each package retains its own source and notices. WSC's [upstream provenance ledger](https://github.com/abhmul/weak-simplex-conjecture-lean/blob/a204c53cae45652d12524132dbb9a2e0ffe8cf78/PROVENANCE.md) records the upstream source of each StatLean file that WSC vendors.

## Adapted source in this repository

| Local source | Upstream source at the pin above | Attribution and changes |
| --- | --- | --- |
| [FSC/Gaussian/StandardDensity.lean](FSC/Gaussian/StandardDensity.lean) | WSC `WeakSimplexConjectureLean/Gaussian/DensityRatio.lean`, lines 16–45 and 64–74 | Copyright 2026 Abhijeet Mulgund, MIT. Narrow standard-density declarations renamed into `FSC`, indexed by `Fin n`, and adapted to the shared `Coord` alias; mathematical hypotheses and normalization preserved. The complete MIT notice is also retained in the source. |
| [FSC/Analysis/FinitePartialDerivatives.lean](FSC/Analysis/FinitePartialDerivatives.lean), `variable_slice_remainder` | mathlib `Mathlib/Analysis/Calculus/FDeriv/Partial.lean`, lines 31–50 | Copyright 2025 A Tucker, Apache-2.0. The private variable-slice lemma is renamed; proof and hypotheses preserved. Its attribution and change notice remain immediately above the lemma. |

Copies of the pinned upstream license texts are included at [LICENSES/WSC-MIT.txt](LICENSES/WSC-MIT.txt) and [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt). The Apache notice applies to the adapted lemma; it does not assign a new license to the rest of that file.

These adaptations copy narrow proof bodies with attribution. The formalization does not call private upstream declarations by generated names (names beginning with `_private.`). Gaussian support convexity, the convexity of $1/h$ for the Gaussian mass $h(b)$ of a polyhedral region with offsets $b$ (the paper's Section 5.2), uses WSC's existing public Prékopa foundation (`WeakSimplex.isLogConcave_lintegral_right`).

## Verification and development records

[The provenance review](docs/work-packages/WP25-provenance-review.md) and its [machine-readable receipt](checks/release/provenance.json) record original-input hashes, exact dependency revisions, license checks, and source comparisons. The provenance receipt distinguishes the original inputs from the two probes implemented afterward. Historical receipts are preserved, including original paths and failed experiments.

The development used AI-assisted implementation and review. [The package cards](docs/work-packages/) retain the file ownership and compiler evidence. These records document the implementation process. They do not stand in for the Lean proofs or for external peer review.
