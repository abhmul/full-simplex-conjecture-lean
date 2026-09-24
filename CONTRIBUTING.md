# Contributing

## Scope

Before changing a proof, read the [public contract](docs/PUBLIC_CONTRACT.md) and the [architecture of the formal proof](docs/ARCHITECTURE.md). In the notation of the [README](README.md#main-theorem), the comparison $F_{\Delta_n}(t)\le F_G(t)$ must cover every dimension $n\ge2$, every positive-semidefinite correlation matrix $G$, and every real threshold $t$. At each fixed $t>0$, equality $F_G(t)=F_{\Delta_n}(t)$ must hold exactly when $G=\Delta_n$. Singular matrices, repeated coordinates ($g_{ij}=1$), antipodal coordinates ($g_{ij}=-1$), and nonpositive comparison thresholds are part of the public scope.

## Making changes

Keep changes focused, and state which declaration or mathematical interface they affect. Search the pinned dependency sources and existing consumers before adding infrastructure. Preserve exact dependency pins and source notices. A narrowly adapted proof needs its source revision and provenance recorded, as in [PROVENANCE.md](PROVENANCE.md). Do not call private declarations through generated names. Discuss changes to the mathematical contract, the dependency pins, or the trust policy with the maintainer before proceeding.

## Trust policy

Production proofs must not contain `sorry`, `admit`, custom axioms, or native-computation axioms. The permitted transitive axiom set (the axioms a declaration uses, including through its dependencies) is any subset of `propext`, `Classical.choice`, and `Quot.sound`. A reusable generic theorem may have genuine hypotheses. For example, an averaging theorem may assume a proved second-order expansion. The final FSC theorems must discharge every project-specific analytic input. Keep provisional assemblies with unproved assumptions outside the public root (`FSC.lean`), and do not hide those assumptions in instances or certificate fields.

## Building and checking

Use incremental builds while developing. For example, after changing the maximum-probability dictionary (`FSC/Gaussian/Maximum.lean`, which relates the CDF to the maximum coordinate), build its target before checking the file that imports it:

```sh
lake build FSC.Gaussian.Maximum --wfail
lake env lean -DwarningAsError=true checks/wp24/Adverse.lean
```

Choose the target and regression test that correspond to your change. Record exact failed goals and useful counterexamples, particularly when changing how singular matrices, redundant constraints, or tied support numbers are represented (the [architecture](docs/ARCHITECTURE.md) defines these). Add tests that exercise the mathematical issue. Preserve the existing adverse cases (tests of singular, redundant, tied, and other boundary cases) and the historical receipts in [checks/](checks/README.md).

Before requesting review of a proof change, build both libraries and run a fresh axiom audit of the public theorems:

```sh
lake build FSC FSCProbes --wfail
lake env lean -DwarningAsError=true FSC.lean
python3 scripts/audit_axioms.py FSC/Audit.lean \
  --required FSC.cdf_simplex_le \
  --required FSC.cdf_eq_simplex_iff
```

For a change to the audit tooling, also run `python3 scripts/test_audit_axioms.py`. Include the relevant commands and their results in the contribution. Review the exact theorem statement as well as its axiom closure. [BUILDING.md](docs/BUILDING.md) documents the full verification suite and the rebuild from scratch (a rebuild from source with no cached build products) required for release acceptance.

## Paper and licensing

The accompanying paper is [arXiv:2609.28452](https://arxiv.org/abs/2609.28452). Historical teaching and review notes describe implementation inputs and should not be presented as the paper. No repository-wide license for the original FSC work has been selected. Preserve existing dependency licenses and adapted-source notices. Public availability does not establish a new license. Licensing decisions remain with the maintainer.
