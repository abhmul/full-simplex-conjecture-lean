# WP05 coordinate partial derivative adapter

Status: product and finite-Pi adapters independently reviewed, installed warning-clean and freshly audited. The generic work is tracked as WP26 after the lead's dependency refinement. Owner: `/root/wp00_imports`, assigned by the implementation lead on 2026-09-08. Exclusive files: `FSC/Analysis/PartialDerivatives.lean`, `FSC/Analysis/FinitePartialDerivatives.lean`, `checks/wp05/`, and this evidence note. The lead retains Git integration. Ownership of the separate finite-Pi module was explicitly approved by the lead before edits so the installed product module stays stable for the triangle worker.

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

## Finite-input extension

`FSC/Analysis/FinitePartialDerivatives.lean` preserves the original finite index space: `piGradient p = ∑ i, p i • ContinuousLinearMap.proj i`. Its core theorem is:

```lean
FSC.hasFDerivAt_pi_of_partials
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {p : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hp : ∀ i, ∀ᶠ y in 𝓝 x,
      HasDerivAt (fun a : ℝ ↦ f (Function.update y i a)) (p y i) (y i))
    (hcp : ∀ i, ContinuousAt (fun y ↦ p y i) x) :
    HasFDerivAt f (FSC.piGradient (p x)) x
```

The proof telescopes over finite subsets. Each increment changes one coordinate while the other changed coordinates approach the base. A variable-slice mean-value remainder is little-o of that coordinate increment, hence little-o of the full increment by the continuous coordinate projection. Summing finitely many remainders proves the actual Fréchet derivative. No nonempty index or dimension hypothesis occurs.

`FSC.eventually_hasFDerivAt_pi_of_partials` uses the same local derivative premises plus eventual continuity of each coordinate field around the base to obtain assembled derivatives throughout a neighborhood. `FSC.contDiffAt_one_pi_of_partials` derives local C1 from these hypotheses. `FSC.contDiffAt_two_pi_of_partials` instead assumes each coordinate field is locally C1 and derives local C2. The global wrappers are `FSC.hasFDerivAt_pi_of_partials_global`, `FSC.contDiff_one_pi_of_partials`, and `FSC.contDiff_two_pi_of_partials`. These local contracts allow the support consumer to restrict to a neighborhood where boundary hyperplanes remain distinct; there is no global tie exclusion.

The actual compiler rejected `isLittleO_sub_sub_fderiv` as an unknown identifier despite importing its defining module. Source inspection explains this: pinned `Mathlib/Analysis/Calculus/FDeriv/Partial.lean` uses the new module visibility system; the product theorem is explicitly public and the preceding variable-slice helper is not. With the lead's explicit authorization, lines 31–50 were adapted narrowly into a private helper `variable_slice_remainder`, preserving its mathematical hypotheses and proof. Its source notice preserves the original A Tucker copyright, authorship, Apache 2.0 attribution and exact mathlib pin `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. No generated private declaration name is used and no license is assigned to other new project work.

Additional failed experiments and compiled repairs: the original helper's default `s` and segment arguments consumed positional derivative arguments, repaired with named `s`, `df'`, `cf'`; `Function.update_same` and guessed repeated-update names were replaced by actual `Function.update_self` and `Function.update_idem`; an untyped coordinate projection inferred an unintended natural-valued domain, repaired by annotating `(ι → ℝ) →L[ℝ] ℝ`; deprecated `continuous_finset_sum` was replaced by `continuous_finsetSum`. The local C1 wrapper first treated `ContDiffAt ℝ 0` as point continuity, but the pinned definition requires continuity on a neighborhood; the final proof explicitly supplies the neighborhood of simultaneous coordinate continuity and proves continuity there. This strengthens the proof evidence while retaining the originally stated neighborhood hypotheses.

`lake env lean -DwarningAsError=true FSC/Analysis/FinitePartialDerivatives.lean` exited 0 after the complete local and global wrappers. The lead installed `FSC.Analysis.FinitePartialDerivatives --wfail`, exit 0, and independently reviewed the complete finite telescope, norm comparison, local C1/C2 wrappers and empty-index scope. The fresh required-endpoint audit of `checks/wp05/FiniteAudit.lean` passed all eight declarations, each using exactly `[propext, Classical.choice, Quot.sound]`; actual JSON output is retained in `checks/wp05/finite-axioms.jsonl`.

`checks/wp05/FiniteConsumer.lean` compiles with warnings as errors. Its `FSCChecks.WP05.empty_input_C2` proves every function on the empty finite coordinate space is C2 by the finite-input adapter. Its `FSCChecks.WP05.three_coordinate_C2` proves C2 of `y 0 * y 1 + (y 2)^2` from all three explicit scalar derivatives. No smoothness premise remains in either consumer. The initial consumer used an unavailable derivative power API and omitted the explicit scalar/type parameters to `contDiff_apply`; the repair uses the product rule for the square and the actual `contDiff_apply ℝ ℝ i` signature. Fresh required-endpoint consumer evidence is stored in `checks/wp05/finite-consumer-axioms.jsonl`.

Reproduction: `/home/abhmul/.local/share/agent-python/.venv/bin/python scripts/audit_axioms.py checks/wp05/FiniteAudit.lean --required FSC.piGradient_apply --required FSC.hasFDerivAt_pi_of_partials --required FSC.eventually_hasFDerivAt_pi_of_partials --required FSC.contDiffAt_one_pi_of_partials --required FSC.contDiffAt_two_pi_of_partials --required FSC.hasFDerivAt_pi_of_partials_global --required FSC.contDiff_one_pi_of_partials --required FSC.contDiff_two_pi_of_partials --save-json checks/wp05/finite-axioms.jsonl`; the analogous consumer invocation names both closed consumer endpoints above and saves `finite-consumer-axioms.jsonl`. These are generic calculus certificates only; actual Gaussian slice laws and local support C1 remain WP05 work.
