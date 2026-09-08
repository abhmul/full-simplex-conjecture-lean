# WP05 coordinate partial derivative adapter

Status: product adapter reviewed; finite-Pi extension in progress. Owner: `/root/wp00_imports`, assigned by the implementation lead on 2026-09-08. Exclusive files: `FSC/Analysis/PartialDerivatives.lean`, `FSC/Analysis/FinitePartialDerivatives.lean`, `checks/wp05/`, and this evidence note. The lead retains the main WP05 package card, shared definitions and Git integration. Ownership of the separate finite-Pi module was explicitly approved by the lead before edits so the installed product module stays stable for the triangle worker.

The triangle worker needs an actual product-domain derivative from the two continuous scalar slice derivatives of its bivariate Gaussian CDF. Frozen core contract: for `f,p,q : ℝ × ℝ → ℝ`, eventual first/second coordinate `HasDerivAt` statements around a base point, plus `ContinuousAt p` and `ContinuousAt q` there, imply `HasFDerivAt f (p x • fst + q x • snd) x`. Global C1/C2 wrappers will consume actual continuous or C1 partial fields. No project-specific regularity oracle is introduced.

Read the support slicing and telescope argument in `docs/pro-return/SUPPORT_NOISE_VARIATION.md` section 2. Search exact pinned Prod/Pi/Partial/MeanValue APIs before implementing the adapter. The 2-coordinate theorem is the first target so the concrete triangle is not delayed by a finite-Pi generalization.

## Product acceptance

The pinned `Mathlib.Analysis.Calculus.FDeriv.Partial` module exposes `hasStrictFDerivAt_uncurry_coprod`, which already proves the local product telescope with a mean-value estimate. It was found by searching the actual `Partial.lean`; no new telescope proof was necessary. The 102-line module ends after this theorem and does not contain a finite-Pi input theorem. The `pi` theorems in `FDeriv.Prod` and `FDeriv.Pi` differentiate Pi-valued outputs, so they do not discharge this input-space regularity step.

Exact accepted scalar adapter:

```lean
FSC.hasFDerivAt_prod_of_partials
    {f p q : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hp : ∀ᶠ y in 𝓝 x, HasDerivAt (fun a : ℝ ↦ f (a, y.2)) (p y) y.1)
    (hq : ∀ᶠ y in 𝓝 x, HasDerivAt (fun b : ℝ ↦ f (y.1, b)) (q y) y.2)
    (hcp : ContinuousAt p x) (hcq : ContinuousAt q x) :
    HasFDerivAt f (FSC.prodGradient (p x) (q x)) x
```

`prodGradient p q` is transparently `p • ContinuousLinearMap.fst ℝ ℝ ℝ + q • ContinuousLinearMap.snd ℝ ℝ ℝ`, and `prodGradient_apply` evaluates it as `p * h.1 + q * h.2`.

`FSC.hasFDerivAt_prod_of_partials_global` specializes eventual derivatives and continuity to globally provided slice derivatives and continuous partial fields. `FSC.contDiff_one_prod_of_partials` derives `ContDiff ℝ 1 f` from those global premises. `FSC.contDiff_two_prod_of_partials` instead assumes each partial field is `ContDiff ℝ 1` and derives `ContDiff ℝ 2 f`. The triangle worker received these exact signatures and can supply its explicit bivariate Gaussian slice formulas.

`lake env lean -DwarningAsError=true FSC/Analysis/PartialDerivatives.lean` exited 0. The lead installed `FSC.Analysis.PartialDerivatives --wfail` with exit 0 and independently reviewed the derivative-field hypotheses and wrappers. An audit invocation before installation failed solely on missing `.olean`; it was retried after installation. Fresh required-endpoint audits are stored in `checks/wp05/audit.jsonl` and `checks/wp05/consumer-axioms.jsonl`.

The actual compiler rejected automatic `ext z` because it selected real-linear-map basis extensionality and did not consume `z`. The repair explicitly uses `ContinuousLinearMap.ext` and introduces the evaluation point. The C2 wrapper's first attempt supplied the two conjuncts in the wrong order; the actual `contDiff_succ_iff_hasFDerivAt` type requires smoothness of the derivative field before its derivative witnesses. Both are ordinary elaboration repairs with unchanged mathematical contracts.

No WSC private implementation was copied. Existing pinned mathlib public proofs supply the mean-value estimate. The new wrappers assign no license to new work and alter no trust boundary.
