# WP00 exact imports and consumers evidence

Status: kernel-checked-local, source/API probe only. Owner: `/root/wp00_imports`, assigned by the implementation lead on 2026-09-08. Exclusive authored files: `FSCProbes/Imports.lean` and this evidence file. The lead remains sole integration/Git owner; this worker will not commit.

Read before proof work: `AGENTS.md`, `docs/STATE.md`, `docs/ARCHITECTURE.md`, `docs/PUBLIC_CONTRACT.md`, `.agents/skills/lean-work-package/SKILL.md`, `docs/work-packages/WP00.md`, `docs/pro-return/ENVIRONMENT_AND_ACCEPTANCE.md`, and `docs/pro-return/PROBES.md`. No Lean LSP is exposed in this worker's callable tool surface; all elaboration evidence below comes from the actual compiler.

Live environment: `lake env lean --version` reports Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`, Release. Actual WSC checkout revision is `a204c53cae45652d12524132dbb9a2e0ffe8cf78`; actual mathlib checkout revision is `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The working tree was clean on first inspection. No dependency or toolchain changes were made.

## Scope

Compile exact-name APIs and small consumers for joint Gaussian independence, affine Gaussian laws, existing WSC Prékopa, Schur complements, Haar scaling, and parametric integration. These are infrastructure probes, not the Gaussian regression, singular derivative, or final FSC theorem.

## Commands and actual outcomes

- Initial `lake env lean -DwarningAsError=true FSCProbes/Imports.lean`: exit 1, missing WSC module prefix. The supplied bootstrap had not installed its dependency targets.
- The lead installed the pinned mathlib cache. The coordinated worker command `lake build FSCProbes.Imports WeakSimplexConjectureLean.Coding.BayesValue` installed every WSC prerequisite, including BayesValue, and failed only at the new Gram-event consumer's opaque-wrapper measurability proof.
- After the one-line wrapper unfolding repair, `lake env lean -DwarningAsError=true FSCProbes/Imports.lean > /tmp/fsc-wp00-imports-20260908.log 2>&1`: exit 0. Every original exact-name check succeeded; all seven consumers kernel checked. The same fresh process printed the seven axiom reports below. The temporary log is convenient local evidence; the checked source and receipts in this file are the durable evidence.
- The lead owns the subsequent final warning-clean target installation and combined milestone build.

No Python, native computation or additional dependency was used. This file imports the pinned WSC public APIs; no source implementation was copied, and no new-work license is assigned. The pinned WSC root `LICENSE` is MIT, copyright 2026 Abhijeet Mulgund. WSC's existing vendor module preserves the StatLean provenance.

## Exact compiler-printed consumer statements

The following are the printed types, with only proof bodies omitted. They retain every hypothesis.

```lean
theorem FSCProbes.Imports.gram_lowerOrthant :
  ∀ {m d : ℕ} (code : Fin m → Coord d) (t : ℝ),
  (multivariateGaussian 0 (codeGram code)) (lowerOrthant t) =
    (stdGaussian (Coord d)) {y | ∀ (i : Fin m), ⟪code i, y⟫_ℝ ≤ t}

theorem FSCProbes.Imports.joint_linear_image_factorization :
  ∀ {d m k : ℕ} (G : Matrix (Fin d) (Fin d) ℝ)
    (A : Coord d →L[ℝ] Fin m → ℝ) (B : Coord d →L[ℝ] Fin k → ℝ),
  (∀ (i : Fin m) (j : Fin k),
    cov[fun x => A x i, fun x => B x j; multivariateGaussian 0 G] = 0) →
  Measure.map (fun x => (A x, B x)) (multivariateGaussian 0 G) =
    (Measure.map (⇑A) (multivariateGaussian 0 G)).prod
      (Measure.map (⇑B) (multivariateGaussian 0 G))

theorem FSCProbes.Imports.affine_image_isGaussian :
  ∀ {d m : ℕ} (G : Matrix (Fin d) (Fin d) ℝ)
    (A : Coord d →L[ℝ] Coord m) (b : Coord m),
  IsGaussian (Measure.map (fun x => A x + b) (multivariateGaussian 0 G))

theorem FSCProbes.Imports.convex_support_marginal :
  ∀ {m d : ℕ} (s : Set ((Fin m → ℝ) × (Fin d → ℝ))),
  MeasurableSet s → Convex ℝ s →
  (Measurable fun r => ∫⁻ (y : Fin d → ℝ), convexIndicator s (r, y)) ∧
    IsLogConcave fun r => ∫⁻ (y : Fin d → ℝ), convexIndicator s (r, y)

theorem FSCProbes.Imports.schur_complement_posSemidef :
  ∀ {m d : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin d) ℝ) (D : Matrix (Fin d) (Fin d) ℝ),
  A.PosDef → ∀ [Invertible A],
  (Matrix.fromBlocks A B B.conjTranspose D).PosSemidef →
    (D - B.conjTranspose * A⁻¹ * B).PosSemidef

theorem FSCProbes.Imports.haar_scaling :
  ∀ {d : ℕ} (f : (Fin d → ℝ) → ℝ) (r : ℝ),
  ∫ (x : Fin d → ℝ), f (r • x) = |(r ^ d)⁻¹| * ∫ (x : Fin d → ℝ), f x

theorem FSCProbes.Imports.hasDerivAt_integral_mul.{u_1} :
  ∀ {α : Type u_1} [inst : MeasurableSpace α] (μ : Measure α) (f : α → ℝ),
  Integrable f μ → ∀ (x₀ : ℝ),
  HasDerivAt (fun x => ∫ (a : α), x * f a ∂μ) (∫ (a : α), f a ∂μ) x₀
```

All seven fresh reports are exactly `[propext, Classical.choice, Quot.sound]`. Each endpoint appears explicitly in the source audit commands. This is local source/API evidence; it is not the final required-endpoint release audit.

## Actual APIs and corrections

All supplied exact-name checks elaborate at the frozen revisions. In particular the actual names are `Matrix.PosDef.fromBlocks₁₁`, `MeasureTheory.Measure.integral_comp_smul`, and the root-level `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The prose warning about those names being wrong does not match these pinned sources. The PosDef source header itself lists the obsolete PosSemidef namespace, while its declaration is inside PosDef.

The Schur theorem requires `hA : A.PosDef` and `[Invertible A]`. Haar scaling returns the factor `|(R ^ Module.finrank ℝ E)⁻¹|` and works without integrability assumptions by the integral convention. The scalar parametric-integral theorem returns a conjunction: derivative integrability and the actual derivative of the integral. Its neighborhood, eventual measurability, integrability at the base, measurable derivative, uniform integrable derivative bound and almost-everywhere neighborhood derivative premises are all explicit.

The Gaussian independence API requires a genuinely joint Gaussian law into a product of finite Pi spaces. The consumer builds it from `A.prod B` and the Gaussian identity law, then applies coordinate covariance zero and `IndepFun.map_prod_eq_prod_map_map`. Separate Gaussian marginal declarations are not used as a substitute. No PSD hypothesis is required for this probe's Gaussianity/factorization statement because mathlib defines a Gaussian law even for a non-PSD matrix; covariance identification with the supplied matrix still requires PSD and remains an obligation for canonical regression.

## Failed experiments retained

The new Gram-event consumer initially attempted `Measure.map_apply (by fun_prop) ...`. The compiler rejected the exact goal

```lean
Measurable fun y => Coord.ofFun fun i => ⟪code i, y⟫_ℝ
```

with `No theorems found for WeakSimplex.Coord.ofFun`. Repair: `by unfold Coord.ofFun; fun_prop`. The failed process printed a `sorryAx` footprint for this failed declaration, generated by elaborator error recovery. No authored placeholder was present, and the fresh repaired compiler process removes it. This illustrates why acceptance rejects compiler diagnostics, not merely source placeholders.

An initial worker header used `/-!` before imports; the lead's compiler rejected the following import command. Changing the pre-import header to an ordinary `/-` comment repaired syntax. This was parser friction, not an interface change.

The following independent actual negative probe ran with `lake env lean --stdin -DwarningAsError=true` after importing Gaussian.Regularization, Coding.Gram, Haar.NormedSpace and ParametricIntegral. Exit 1; diagnostics:

```text
<stdin>:5:7: error(lean.unknownIdentifier): Unknown identifier `WeakSimplex.map_weightedGaussianSum`
<stdin>:6:7: error(lean.unknownIdentifier): Unknown identifier `WeakSimplex.regularSimplexGram_isCorrelation`
<stdin>:7:7: error(lean.unknownIdentifier): Unknown constant `Matrix.PosSemidef.fromBlocks₁₁`
<stdin>:8:7: error(lean.unknownIdentifier): Unknown identifier `MeasureTheory.integral_comp_smul`
<stdin>:9:7: error(lean.unknownIdentifier): Unknown identifier `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
```

No generated private names were accessed.

## Reuse and unpaid consumers

`gram_lowerOrthant` is the shortest tested bridge for a rank-deficient concrete Gram configuration. It uses the actual Gaussian event, without rank/unit/threshold assumptions. `WeakSimplex.gramNormalization` exposes simplex correlation as a public conjunct even though the standalone helper is private.

The affine probe proves Gaussianity, not its matrix covariance formula. The private WSC `Gaussian/Regularization.lean` weighted-sum proof is a possible narrow template for arbitrary covariance noise, but the public regularization result only handles independent standard noise and weights summing to one. Canonical pair PSD, cross-covariance calculations, fixed-pin law, event Fubini, threshold regularity and rank-increasing derivative remain unpaid.

The support probe establishes measurable log-concave Lebesgue section volume for arbitrary measurable convex support. It permits unbounded sections and ties; it is not the Gaussian reciprocal-support tangent theorem, nor a support derivative. The Haar and derivative probes exercise real consumers, but do not establish Gaussian dilation domination.
