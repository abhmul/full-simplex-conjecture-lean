# Exact source map and evidence ledger

## Provenance and limits

The source root below is the extracted `FSC_LEAN_INSPECTION.zip`. All 63 entries in its `SHA256SUMS` were checked successfully. This verifies correspondence with the supplied manifest, not an independently cloned Git checkout. WSC provenance is the supplied commit `a204c53cae45652d12524132dbb9a2e0ffe8cf78`; mathlib is `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; Lean is `leanprover/lean4:v4.31.0`. No Lean command succeeded or was claimed to succeed during this consultation.

A status of **public** below means the declaration and its hypotheses were read in the exact source; it does not mean an FSC application has elaborated. **Adapter** means reusable proof material or a public primitive exists, but the required statement differs. **New** means a proof obligation of this proposed FSC development, not a claim that no such theorem exists anywhere in Lean.

In the WSC table, paths are relative to `wsc/WeakSimplexConjectureLean/`. In the mathlib table, paths are relative to `mathlib/Mathlib/`. Private names must not be called through generated internal names.

## WSC public foundations and adaptation boundaries

| Need | Exact source/declaration | Checked scope and disposition |
|---|---|---|
| Correlation predicate | `Core/Correlation.lean:12–18`, `WeakSimplex.IsCorrelation` | PSD plus unit diagonal. `IsWeakSimplexCov` is strictly stronger and is not the FSC hypothesis. Public reuse. |
| Coordinates and event | `Core/Euclidean.lean:19–35,67–74`, `Coord`, `Coord.ofFun`, `Coord.toFun`, `lowerOrthant`, `measurableSet_lowerOrthant` | Euclidean `WithLp` coordinates, not literally the plain Pi normed space. Public reuse; real/measure CDF adapter new. |
| Matrix CLM | `Core/Matrix.lean:19–40`, `allOnesMatrix`, `matrixMul`, `qform`, `qform_eq_dotProduct` | Coordinate/matrix bridges; use rather than reproducing notation. |
| Simplex | `Coding/Gram.lean:28,115–155`, `regularSimplexGram`, `gramNormalization` | Simplex PSD/diagonal/correlation helper declarations at 115,120,127 are private. Public `gramNormalization hn G hG` has simplex correlation as its middle conjunct; `(…).2.1` extracts it. For a G-independent wrapper instantiate a simple correlation, e.g. identity. No WSC comparison theorem is used. |
| Forward Gram law | `Coding/BayesValue.lean:23–37,48–90`, `codeGram`, `codeGram_posSemidef`, `codeGram_isCorrelation`, `map_codeScore_stdGaussian` | Public law for any code in `Coord n`; unit norms only needed for correlation. This does not provide inverse Gram realization or rank padding. The public file imports `Maxima.ExponentialMoments`, so its import footprint is larger than the short law proof. Default to reuse; a narrowly adapted proof is a separately audited option. |
| Normal calculus | `Normal/PDFCDF.lean:12–14,23,31,49,53,63,79,103–115`, `normalPDF`, `normalCDF`, `normalPDF_pos`, `hasDerivAt_normalPDF`, `normalCDF_eq_measure_Iic`, `normalCDF_pos`, `normalCDF_lt_one`, `hasDerivAt_normalCDF`, endpoint limits | Public scalar foundations. Several integrability/continuity helpers in the file are private. Do not claim them as callable wrappers. |
| Scalar second moments | `Normal/TruncatedMoments.lean:59–69,81–90`, `truncated_first_moment`, `truncated_second_moment` | Public half-line integral identities; useful for interval and unbounded-cap diagnostics. The underlying moment integrability helpers are private. |
| Prékopa | `LogConcavity/Prekopa.lean:21–65`, `prekopa_leindler`, `isLogConcave_lintegral_right`, `measurable_isLogConcave_lintegral_right` | Public, finite-dimensional Pi integration of ENNReal-valued measurable functions. Marginalization requires joint log-concavity and measurable sections; the measurable version needs measurable uncurry. Neither bounded supports nor strictly positive integrands are required. This foundation is already paid. |
| Convex indicator/Gaussian kernel | `LogConcavity/Basic.lean:18–61`; `Indicators.lean:19–39,64–89` | Public `IsLogConcave`, multiplication/affine composition, `convexIndicator`, `isLogConcave_convexIndicator`, `gaussianQuadraticKernel`, `isLogConcave_gaussianQuadraticKernel`. Adapter: support vector rather than one scalar translation, and real reciprocal tangent. |
| Gaussian Pi density | `Vendor/StatLean/PiGaussian.lean:29–58`, `WeakSimplex.Vendor.StatLean.AsymptoticStatistics.pi_gaussianReal_eq_withDensity` | Public product standard Gaussian equals Lebesgue measure with product density. Use in Pi coordinates for Prékopa/dilation; transport the probability through `map_pi_eq_stdGaussian`. Provenance and Apache-2.0 license retained by WSC. |
| Regularization | `Gaussian/Regularization.lean:154–165,168–211,283–306`, `map_gaussianRegularization_eq_multivariateGaussian`, `tendstoInDistribution_regularized_multivariateGaussian`, PSD/PD/correlation preservation | Public coupling with identity covariance, parameter 0≤ε≤1; convergence theorem is the specified dyadic sequence. It is not arbitrary covariance continuity or addition of an arbitrary independent covariance. Useful fallback and adapter template; not a missing foundation. |
| Regression | `Product/SymmetricRectangle.lean:231–255,307–331,401–459` | Private residual CLMs, residual independence and product-law proofs permit PSD covariance and singular residuals. `regressionResidual_indep_last` and `map_regressionResidual_last_eq_prod` are private. Adapt to arbitrary selected pair and nonsymmetric lower events. The proof uses joint Gaussianity plus vanishing cross-covariances. |
| Slicing and shifted convex mass | `Product/SymmetricRectangle.lean:166–190,379–399,460–496` | Private log-concave shifted convex mass, general product integration template, and a rectangle specialization. Reuse public Prékopa for the new support family; generalize the Fubini interface, not its symmetry-specific consumer. |
| Orthant frontier | `Orthant/Singular.lean:20–89` | Private topology/null-frontier helpers. The declared Gaussian hypothesis is `IsWeakSimplexCov`, but lines 69–78 use only PSD and unit diagonal. A new correlation-scoped adapter is small and necessary. |
| Positive-definite density bridge | `Gaussian/DensityRatio.lean:245–277`, `gaussianDensityRatio`, `multivariateGaussian_eq_stdGaussian_withDensity` | Public under positive definiteness. It is not an orthant covariance derivative. The proposed support/noise route does not require it. |
| Maximum/event dictionary | `Maxima/CoordinateMax.lean:11–28`, `coordinateMax`, `continuous_coordinateMax`, `coordinateMax_le_iff_mem_lowerOrthant` | Public for nonempty `Fin n`; use only for the final stochastic-order wrapper. |

## Pinned mathlib APIs: exact namespaces and hypotheses

| Need | Exact source | What was checked |
|---|---|---|
| All-PSD Gaussian laws | `Probability/Distributions/Gaussian/Multivariate.lean:128–153,163–177,193–245` | `stdGaussian_map`, `map_pi_eq_stdGaussian`, basis invariance; `multivariateGaussian`; mean, covariance, coordinate law and characteristic function. Covariance/characteristic-function conclusions require PSD. Outside PSD the law is Dirac. |
| Square-root algebra | Same file, covariance proof at 203–214 | The proof explicitly uses `CFC.sqrt_mul_sqrt_self _ hS.nonneg` and `CFC.sqrt_nonneg`. These give an inspected starting point for Gram realization. No claim was made that a ready-made exact rank-padding theorem exists. |
| Gaussian law extensionality | `Probability/Distributions/Gaussian/CharFun.lean:182–196`, `ProbabilityTheory.IsGaussian.ext` | Equality of mean and covariance implies equality only with Gaussian instances for both measures. Suitable for affine-image and independent-sum wrappers. |
| Independence | `Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean:330–366`, `ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eval` | Joint Gaussian law of the two finite real coordinate families and all cross-covariances zero. The statement uses Pi-valued families, so the Euclidean/Pi CLM wrapper is real work. |
| Schur complement | `LinearAlgebra/Matrix/PosDef.lean:433,559–591`, **`Matrix.PosDef.fromBlocks₁₁`** | Requires the pinned block A positive definite and an `Invertible A` instance; conclusion is PSD equivalence for the block matrix and Schur residual. The file's introductory prose and the supplied inventory point to `PosSemidef`, but the declaration actually lies inside `namespace PosDef`. The explicit residual-congruence design avoids this dependency. |
| Gram | `Analysis/InnerProductSpace/GramMatrix.lean:40–43,83–126`, `Matrix.posSemidef_gram`, `Matrix.posDef_gram_iff_linearIndependent` | Forward PSD law and positive-definite/independence relation. Rank-bounded existence remains a new adapter. |
| Cauchy | `Algebra/Order/BigOperators/Ring/Finset.lean:158–178`, `Finset.sum_mul_sq_le_sq_mul_sq`, `Finset.sq_sum_div_le_sum_sq_div` | The division version requires every denominator positive on the finset. It does not expose the equality classification needed by FSC; the exact square remainder is a clean local proof. |
| Lévy | `MeasureTheory/Measure/LevyConvergence.lean:197–219`, `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun` | Sequence of probability measures on a finite-dimensional inner-product space, with pointwise characteristic-function convergence to the characteristic function of a specified probability law. Upgrade the sequential statement to continuity using the finite-dimensional domain. |
| Portmanteau | `MeasureTheory/Measure/Portmanteau.lean:336–359` | `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'` is the ENNReal-valued version. The unprimed theorem uses probability-measure values in NNReal, not ordinary reals. Nullity is required only for the limit frontier. Prove the final toReal conversion. |
| Differentiation under the integral | `Analysis/Calculus/ParametricIntegral.lean:62–77,284–306`, **root-level** `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | Not in namespace `MeasureTheory`. Requires a neighborhood independent of the integration variable, a.e. derivative at every point of it, uniform integrable derivative bound, measurability and base integrability. Gives integrability of the derivative and the derivative of the integral. The unbounded Gaussian majorant must still be proved. |
| Dilation change of variables | `MeasureTheory/Measure/Haar/NormedSpace.lean:24–26,84–114`, **`MeasureTheory.Measure.integral_comp_smul`** | Finite-dimensional real normed space, Borel measure, additive Haar measure; factor is `|(R ^ finrank ℝ E)⁻¹|`. Use positive s near one and a density/indicator integrand. Neither `MeasureTheory.integral_comp_smul` nor a root-level name is the declaration. |

The three namespace corrections above were incorporated into the uncompiled `#check` probe. They illustrate why reading a file banner or inventory is not equivalent to checking a callable API.

## Primary external material actually consulted

URLs are preserved here so the implementation owner can inspect the same content. Public web documentation is guidance, not a replacement for the pinned source.

- Pinned mathlib Gaussian `Multivariate.lean`, `LevyConvergence.lean`, `ParametricIntegral.lean`, and `Matrix/PosDef.lean` were opened through their exact revision URLs under `https://raw.githubusercontent.com/leanprover-community/mathlib4/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/`. The authoritative line locators above use the attached source bytes, not the web renderer's line wrapping.
- `https://raw.githubusercontent.com/leanprover-community/mathlib4/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Analysis/Calculus/Taylor.lean`: inspected its scope, introductory TODO and the `taylor_isLittleO` statements at source lines approximately 215–238 in the web-rendered view. It is a **one-dimensional domain** theorem, not a verified multivariable Peano API. No exhaustive global absence claim is inferred.
- `https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/`: checked Git dependency revision/name semantics. This is current documentation; the actual probe project remains pinned to Lean 4.31.0.
- `https://lean-lang.org/doc/reference/latest/ValidatingProofs/`: checked the distinction between statement meaning, kernel acceptance and transitive axioms; also the optional stronger rechecking discussion. The document explains that newer native computations can introduce individual computation axioms, so a blacklist containing only `Lean.trustCompiler` is insufficient. The handoff instead whitelists only ordinary axioms.
- `https://raw.githubusercontent.com/leanprover/lean4/v4.31.0/src/Lean/Elab/Tactic/Decide.lean` was opened as a pinned implementation cross-check. No native evaluation is used by the supplied probe proofs.
- An attempted versioned Lean manual URL was unavailable. No source claim or version-specific build assertion relies on that failed fetch.

No public Gaussian research literature was needed: the user supplied the mathematical proof, and outside research here concerned the formal foundations and exact APIs. No GitHub write, repository checkout, dependency installation, account-memory lookup, public release or implementation launch was performed.

## Mathematical and historical reading ledger

The supplied `CONTEXT.md` was read first. The manuscript's target, elementary cases, regression, singular differentiation, support calculus, Prékopa, unbounded dilation, finite tests, scalar assembly, rigidity, barrier, and geometric/envelope alternative were inspected in numbered sections. The operative proof locators are:

| Proof obligation | Teaching manuscript source lines / cross-check |
|---|---|
| All ranks, event, compactness, base | 19–216; Chapter 1 |
| Scalar comparison/equality | 228–286; `COMPONENTWISE_COMPARISON.md:8–55` |
| Pair regression, canonical weights, row-max positivity | 314–445 |
| Original covariance derivative fallback | 451–602; fresh audit §§4.1–4.4; continuing audit §3 |
| Support derivatives, no ties, normalization | 606–797; continuing audit §§5–5.1 |
| Support Prékopa | 801–982; existing Lean Prékopa checked separately |
| Unbounded energy and padding | 994–1137; continuing audit §6.3 is an intrinsic bounded-cap cross-check, not permission to assume all preferred-route caps bounded |
| Finite directions and boundary rigidity | 1141–1391; `CORE_PROOF.md` §§1–4 |
| Recursion, exclusions, barrier, equality | 1397–1552; `CORE_PROOF.md` §5 |
| Geometric/log alternative and envelope | 1558–1986; continuing audit §§4.4,6–9 |
| Adverse controls | Chapter 12; fresh audit §§2,5; reading notes' two nonblocking annotations |

The complete analytic audit files were available; their operative singular/support/energy/assembly sections were checked rather than treating their acceptance labels as proof. Not every historical message was reread. For workflow, the inspected material was `history/JULY17_REASSESSMENT.md`'s architecture/reassessment sections, `wsc/AGENTS.md`, `wsc/PROVENANCE.md`, the supplied inspection summaries, and the audit script bodies. July instructions about outer-boundary-only singular treatment do not govern FSC. The missing four original July 17 downloads were not reconstructed or claimed to have been read.

WSC's recorded August validation and stale trace are historical evidence only. This consultation ran neither that build nor its 139-declaration audit. The full source pack, including license/provenance material, remains the separate supplied archive; the handoff does not relicense or silently copy its Lean declarations.
