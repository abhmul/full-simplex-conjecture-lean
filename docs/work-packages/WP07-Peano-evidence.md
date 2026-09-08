# WP07 generic Peano adapter evidence

Status: reviewed and integrated as WP27; generic adapter only. Owner: `/root/wp00_imports`, assigned by the lead on 2026-09-08. Exclusive files: `FSC/Analysis/PeanoTaylor.lean`, `checks/wp07/`, and this evidence note. The lead retains ownership of the WP07 threshold package card, shared definitions and Git integration. Ownership is recorded before source edits. The lead independently reviewed the neighborhood derivative hypotheses and automatic Hessian symmetry and installed the module warning-clean.

Read the governing documents and `docs/pro-return/SUPPORT_NOISE_VARIATION.md` sections 2–3. The deliverable is a proved vector-domain bridge from an actual neighborhood derivative field differentiable at the base to the exact shared `FSC.Peano2`; this does not certify threshold regularity.

Pinned source search found `Convex.isLittleO_pow_succ` in `Mathlib/Analysis/Calculus/MeanValue.lean`, a vector-domain derivative-to-remainder theorem, and `second_derivative_symmetric_of_eventually_of_real` in `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`. The univariate `taylor_isLittleO` is not used as a vector-domain theorem. `ContDiff/FTaylorSeries.lean` describes derivative towers but supplies no directly found little-o remainder theorem. The accepted declarations below are compiled consumers of these exact APIs.

## Exact accepted interfaces

```lean
FSC.peano2_of_hasFDerivAt_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {f' : V → V →L[ℝ] ℝ} {x : V}
    {B : V →L[ℝ] V →L[ℝ] ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hB : HasFDerivAt f' B x) :
    FSC.Peano2 f x (f' x) B

FSC.peano2_of_contDiffAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {x : V} (hf : ContDiffAt ℝ 2 f x) :
    FSC.Peano2 f x (fderiv ℝ f x) (fderiv ℝ (fderiv ℝ f) x)
```

The first theorem derives symmetry of `B` from its genuine derivative hypotheses. Its remainder derivative on a small ball is `f'(x+h)-f'(x)-B(h)`, which is little-o of `‖h‖`. The pinned vector-domain `Convex.isLittleO_pow_succ` raises the order to two; neighborhood restriction is removed using the ball's neighborhood membership. The second theorem supplies the actual derivative field from local C2 regularity. No finite-dimensional, completeness, Gaussian, or symmetry hypothesis is added.

## Verification

- `lake env lean -DwarningAsError=true FSC/Analysis/PeanoTaylor.lean`: exit 0.
- The lead installed `FSC.Analysis.PeanoTaylor` with `--wfail` before consumers.
- Specialized-environment `scripts/audit_axioms.py checks/wp07/Audit.lean --required FSC.peano2_of_hasFDerivAt_derivative --required FSC.peano2_of_contDiffAt --save-json checks/wp07/audit.jsonl`: exit 0, fresh audit passed both declarations, each with `[propext, Classical.choice, Quot.sound]`.
- `checks/wp07/VectorConsumer.lean` applies the theorem to the genuinely two-dimensional function `(z : Fin 2 → ℝ) ↦ z 0 * z 1`, with its actual `fderiv` and second `fderiv`; no smoothness premise remains. Specialized-environment `scripts/audit_axioms.py checks/wp07/VectorConsumer.lean --required FSCChecks.WP07.mixed_quadratic_peano --save-json checks/wp07/vector-axioms.jsonl`: exit 0, fresh audit passed with the allowed three axioms.

## Failed source/API experiments

The initially guessed direct `Mathlib/Analysis/Calculus/FTaylorSeries.lean` path does not exist; the actual derivative-tower module is `ContDiff/FTaylorSeries.lean`. No vector remainder theorem was claimed from that inventory.

Ordinary `convert`/`simpa` around current real normed/TVS derivative structures generated elaborator instance and function-coercion mismatches, including a goal comparing `Real.instAddCommGroup` with `Real.normedAddCommGroup.toAddCommGroup`. The compiled repair uses mathlib's `simpa ... using!` form and `HasFDerivAt.congr_fderiv`, preserving the exact statement. The quadratic derivative is proved from `ContinuousLinearMap.hasFDerivAt_of_bilinear` and the already proved second-derivative symmetry, not postulated.

## Remaining consumer

WP05 must prove actual neighborhood slice derivatives and their continuity; WP07 must prove the actual threshold derivative field differentiable at the common positive threshold and identify its entries with canonical weights. These generic adapters close only the C2-to-Peano step. The singular triangle and universal covariance derivative still require those analytic laws. No research source or WSC private implementation was copied; pins and trust boundary are unchanged.
