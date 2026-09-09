# Contributing

Read the [public contract](docs/PUBLIC_CONTRACT.md) and [architecture](docs/ARCHITECTURE.md) before changing proofs. The comparison must cover every dimension `n ≥ 2`, every positive-semidefinite correlation matrix and every real threshold. Equality is characterized by the regular simplex at each fixed positive threshold. Singular matrices, duplicates, antipodes and nonpositive comparison thresholds are part of the public scope.

Keep changes focused and state which declaration or mathematical interface they affect. Search the pinned dependency sources and existing consumers before adding infrastructure. Preserve exact dependency pins and source notices; narrowly adapted proofs need their source revision and provenance recorded. Do not call private declarations through generated names. Discuss changes to the mathematical contract, dependency pins or trust policy with the maintainer before proceeding.

Production proofs must contain no `sorry`, `admit`, custom axioms or native-computation axioms. The permitted transitive axiom set is any subset of `propext`, `Classical.choice` and `Quot.sound`. Reusable generic theorems may have genuine hypotheses: for example, an averaging theorem may assume a proved second-order expansion. The final FSC theorems must discharge every project-specific analytic input. Keep provisional assemblies with unpaid assumptions outside the public root; do not hide those assumptions in instances or certificate fields.

Use incremental builds while developing. For example, after changing the maximum-probability dictionary, install its target before checking the importing consumer:

```sh
lake build FSC.Gaussian.Maximum --wfail
lake env lean -DwarningAsError=true checks/wp24/Adverse.lean
```

Choose the corresponding target and regression for your change. Record exact failed goals and useful counterexamples, particularly when changing singular, redundant or tied-support representations. Add tests that exercise the mathematical issue, and preserve existing adverse cases and historical receipts.

Before requesting review of proof changes, build both libraries and run a fresh public audit:

```sh
lake build FSC FSCProbes --wfail
lake env lean -DwarningAsError=true FSC.lean
python3 scripts/audit_axioms.py FSC/Audit.lean \
  --required FSC.cdf_simplex_le \
  --required FSC.cdf_eq_simplex_iff
```

Changes to audit tooling also need `python3 scripts/test_audit_axioms.py`. Include the relevant commands and results in the contribution, and review the exact theorem statement as well as its axiom closure. [BUILDING.md](docs/BUILDING.md) documents the full maintained suite and the artifact-free reconstruction required for release acceptance.

The preprint is in preparation. Historical teaching and review notes describe implementation inputs and should not be presented as a released preprint. No repository-wide license for the original FSC work has been selected. Preserve existing dependency licenses and adapted-source notices; public availability does not establish a new license. Licensing decisions remain with the maintainer.
