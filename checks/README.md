# Checks and recorded evidence

Run the verification suite with:

```bash
python3 scripts/verify_release.py --evidence "$(mktemp -d)/evidence"
```

Run it from the repository root after fetching the pinned dependencies. [BUILDING.md](../docs/BUILDING.md) gives the complete setup.

## Current checks

- [IndependentStatements.lean](release/IndependentStatements.lean) checks the public theorems against restatements in which the Gaussian events are written out.
- [FSC/Audit.lean](../FSC/Audit.lean) prints the axioms, including indirect dependencies, of the public theorems and of key supporting declarations.
- The files in the `wp*/` directories (named after the work packages in [docs/work-packages/](../docs/work-packages/)) and in [FSCProbes/](../FSCProbes/) test singular, redundant, tied, empty, and other boundary cases. [verify_release.py](../scripts/verify_release.py) defines the complete list of files that the suite checks.
- [fixtures/](fixtures/) calibrates the axiom checker. The file `AuditRejected.lean` contains a custom axiom on purpose, and the checker must reject it. The production library does not import it.

## Recorded evidence

[The verification report](../docs/RELEASE_AUDIT.md) identifies the certified commit and explains these receipts:

| Directory | Evidence |
| --- | --- |
| [release/clean-source/](release/clean-source/) | The rebuild from scratch (artifact-free source reconstruction) and the original regression suite |
| [release/clean-adapters/](release/clean-adapters/) | Additional adapter audits against the same clean source |
| [release/final-runner-integration/](release/final-runner-integration/) | A run of the combined verification suite with all 30 regression files |

The other logs preserve earlier successful checks, failed API experiments, and audit controls that were rejected on purpose. A failure in a historical log does not show the status of the current library; for that, consult the corresponding work-package card in [docs/work-packages/](../docs/work-packages/) and the final receipts. The evidence files keep their original execution paths and bytes, so their hashes can be verified. New runs write to a new evidence directory instead of overwriting these records.
