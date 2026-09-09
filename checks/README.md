# Checks and retained evidence

Run the maintained suite with:

```bash
python3 scripts/verify_release.py --evidence "$(mktemp -d)/evidence"
```

Run this from the repository root after fetching its pinned dependencies. See [building instructions](../docs/BUILDING.md) for the complete setup.

## Current verification

- [IndependentStatements.lean](release/IndependentStatements.lean) checks the public results against expanded Gaussian-event statements.
- [FSC/Audit.lean](../FSC/Audit.lean) prints the transitive axioms of the public endpoints and critical supporting declarations.
- The `wp*/` consumers and [FSCProbes/](../FSCProbes/) exercise singular, redundant, tied, empty, and other boundary cases. The complete coverage list is maintained in [verify_release.py](../scripts/verify_release.py).
- [fixtures/](fixtures/) calibrates the audit tool. `AuditRejected.lean` deliberately contains a custom axiom and must be rejected. It is not imported by the production library.

## Historical evidence

[The acceptance report](../docs/RELEASE_AUDIT.md) identifies the certified source commit and explains these receipts:

| Directory | Evidence |
| --- | --- |
| [release/clean-source/](release/clean-source/) | Artifact-free source reconstruction and original regression suite |
| [release/clean-adapters/](release/clean-adapters/) | Additional adapter audits against the same clean source |
| [release/final-runner-integration/](release/final-runner-integration/) | Consolidated verification runner with all 30 regression files |

Other logs preserve earlier successful checks, failed API experiments, and intentionally rejected audit controls. A failure in a historical log does not identify the status of the current library; consult its package card and the final receipts. Evidence files retain original execution paths and bytes for hash verification. Fresh runs write to a new evidence directory rather than overwriting these records.
