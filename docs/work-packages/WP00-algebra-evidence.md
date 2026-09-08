# WP00 algebra probe evidence

Status: kernel-checked local; shared audit and integration owned by the lead. Owner: worker `/root/wp00_algebra`; integration owner: `/root`. Exclusive worker files are `FSCProbes/Algebra.lean` and this evidence note. The worker does not edit shared roots, audit files, definitions or pins and does not commit.

The worker read the project instructions, governing state/architecture/public contract, WP00, the local Lean work-package skill and Pro's probe/environment specifications before source edits. No Lean LSP tool is exposed in the current tool catalog; verification uses the actual compiler.

Initial environment: repository revision `449f42623d7442b27bff20df165bb9829196b67c`; initial `git status --short` was empty. `lake env lean --version` reports Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`. The resolved mathlib checkout reports `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. A guessed checkout `.lake/packages/weak_simplex` does not exist; inspect the resolved manifest for the actual WSC path instead of treating that name as an API.

Scope: compile the supplied rational algebra and triangle Gram-PSD probes, retaining the explicit boundary that these establish no Gaussian law, support regularity or covariance derivative.

## Compiler attempt 1: unavailable upstream build artifacts

`lake env lean -DwarningAsError=true FSCProbes/Algebra.lean` exited 1 before elaboration with `unknown module prefix 'Mathlib'`: `.lake/packages/mathlib/.lake/build/lib/lean` does not exist yet. The source checkout itself is present. Repeating after replacing the `Mathlib` umbrella with narrow source-supported imports reports the same absent-prefix failure. The lead was asked to install upstream targets or their pinned cache before the next consumer attempt; this is environment setup, not a mathematical obstruction.

The four selected imports are `Mathlib.Analysis.InnerProductSpace.GramMatrix`, `Mathlib.Analysis.InnerProductSpace.PiL2`, `Mathlib.Tactic.FieldSimp` and `Mathlib.Tactic.Ring`. Exact source search located public `Matrix.gram` and `Matrix.posSemidef_gram` in `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`; no private generated name is used. The actual WSC checkout is `.lake/packages/weak-simplex-conjecture-lean` and reports revision `a204c53cae45652d12524132dbb9a2e0ffe8cf78`.

## Compiler attempt 2 and accepted local source

After the lead installed the cache, `lake env lean -DwarningAsError=true FSCProbes/Algebra.lean` reached all proofs but exited 1 because the unnecessary-sequence-focus linter rejected each `field_simp [...]; <;> ring` pair. The diagnostics were `Used tac1 <;> tac2 where (tac1; tac2) would suffice` at then-lines 17, 24 and 30. Replacing each `<;> ring` with the sequential tactic `ring` preserved the statements and proof strategy. No linter was disabled.

The repeated command `lake env lean -DwarningAsError=true FSCProbes/Algebra.lean` exited 0 with empty output. `git diff --check` also exited 0. This uses the actual Lean compiler and elaborator; it is not a cached nominal target receipt. The worker did not build shared Lake targets or run the shared audit, which the integration lead owns.

The accepted local declarations have their unchanged explicit types in `FSCProbes/Algebra.lean`: `FSCProbes.quadraticRemainder` (three nonzero denominator hypotheses), `FSCProbes.signedRowRemainder` (nonzero n), `FSCProbes.pairPinOrthogonality` (nonzero regression denominator), `FSCProbes.noiseDiagonalCancellation`, `FSCProbes.pairTraceNormalization`, `FSCProbes.triangleGramPSD`, and `FSCProbes.deterministicThirdBelow`. The first five and last are real polynomial/rational identities. `triangleGramPSD` applies public `Matrix.posSemidef_gram ℝ triangle` to the supplied vectors in `EuclideanSpace ℝ (Fin 2)`; it does not yet prove the entries, exact rank, Gaussian law or derivative of that Gram matrix.

Remaining acceptance: the lead installs `FSCProbes.Algebra`, runs fresh `FSCProbes/Audit.lean` and records printed types/transitive axiom coverage before WP00 integration. Remaining mathematical consumers are the production scalar remainder and exact pin/stress identities; this probe file is outside the public FSC root.
