# WP10 analytic preflight evidence

Status: source-inspected preparation, not compiler acceptance. Owner: worker analytic_preflight, assigned by integration lead on 2026-09-08. This worker owns only this evidence file until the lead assigns an implementation slice; no production source or Git integration is owned here.

Read controls: AGENTS.md, STATE.md, ARCHITECTURE.md, PUBLIC_CONTRACT.md, the local lean-work-package skill, WP01/WP10 cards, WORK_PACKAGES.md, SUPPORT_NOISE_VARIATION.md sections 2–4 and 6, INTERFACES.md through rank/facet compatibility, PROBES.md, and MATHEMATICAL_REVIEW.md. The memory registry search returned no task-specific entry. No Python was used. No callable Lean LSP was discovered in the available tool metadata; compiler consumers remain required.

## Coupled convention review

- Keep Coord n = WeakSimplex.Coord n (Euclidean WithLp, not a definitionally identical normed Pi space). Use Coord.ofFun for explicit coordinates. Threshold vectors can use the same space; generic support indices can remain ι → ℝ.
- Choose matrix columns consistently: single-pin mean coordinate t * G k i, covariance coordinate G k l - G k i * G l i; pair coefficients (G k i - G i j * G k j)/(1-(G i j)^2) and its swapped counterpart. Correlation symmetry proves equivalence to the raw single-pin row formula.
- Pair residual matrix is P * G * P.transpose on all original indices, with P k l = (1 : Mat n) k l - α k * (if l = i then 1 else 0) - β k * (if l = j then 1 else 0). The pair event omits both pins; the single event omits its pin.
- Freeze q at exactly the documented domain i ≠ j ∧ -1 < G i j ∧ G i j < 1; outside-domain zero is a totalization. The same q must enter threshold Hessian, stress, support gradient, and energy. Pair positivity is false universally: the triangle has q 0 2 = 0.
- NoCoincident needs both implications, for distinct indices: equal normals imply unequal support values, and opposite normals imply supports are not negatives. Do not require distinct normals; the first triangle cap has repeated normals with unequal supports.
- Peano2 can retain the exact IsLittleO predicate on 𝓝 0 with remainder f (x+h)-f x-l h-(1/2)*B h h and comparison ‖h‖². A continuous bilinear B need not be assumed symmetric for generic averaging; its quadratic part determines the consumer. Local threshold expansion requires a positive common threshold and distinct scores, not arbitrary positive threshold vectors.

## Exact pinned APIs inspected

Paths below are relative to the pinned dependency roots.

| Declaration | Source | Immediate use |
| --- | --- | --- |
| WeakSimplex.Coord.ofFun, ofFun_apply | WSC Core/Euclidean.lean:24–35 | Explicit rank-two coordinates and means |
| WeakSimplex.map_codeScore_stdGaussian | WSC Coding/BayesValue.lean:83–90 | The actual rank-two score law, with no rank hypothesis |
| WeakSimplex.codeGram_posSemidef, codeGram_isCorrelation | WSC Coding/BayesValue.lean:27–37 | Gram PSD and unit-diagonal law |
| ProbabilityTheory.multivariateGaussian | mathlib Probability/Distributions/Gaussian/Multivariate.lean:168–171 | Defined as the affine image of standard Gaussian using CFC.sqrt |
| CFC.sqrt_zero | mathlib Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:253 | A direct rank-zero law proof should simplify the defining affine image to a constant map |
| ProbabilityTheory.measurePreserving_eval_multivariateGaussian | mathlib Probability/Distributions/Gaussian/Multivariate.lean:227–236 | One-coordinate marginal law under PSD covariance |
| ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_inner | mathlib Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean:330–335 | Hilbert-valued residual/pin independence; avoids mandatory Pi transport |
| ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eval | same file 340–365 | Pi-valued alternative with coordinate covariance proof |
| ProbabilityTheory.IsGaussian.ext | mathlib Probability/Distributions/Gaussian/CharFun.lean:185–190 | Gaussian law equality from actual Gaussian instances, mean, covariance |
| WeakSimplex.normalCDF_eq_measure_Iic | WSC Normal/PDFCDF.lean:49–51 | Exact Gaussian half-line mass bridge; conclusion is ENNReal.ofReal (normalCDF x) = μ (Iic x) |
| WeakSimplex.normalCDF_pos, hasDerivAt_normalCDF | same file 53–61, 79–101 | Positive mass and actual one-dimensional derivative |
| WeakSimplex.hasDerivAt_normalPDF | same file 31–47 | Second derivative for scalar CDF |

The WSC score-law theorem imports a larger existing dependency footprint through Maxima.ExponentialMoments; it remains a public theorem and is the authorized default reuse. Its private scoreCLM implementation is not a callable API.

The inspected WSC regression template is private: Product/SymmetricRectangle.lean:401–459 proves joint Gaussianity using hId.map (residualCLM.prod pinCLM), proves zero cross-covariance, obtains IndepFun, then calls map_prod_eq_prod_map_map. A new arbitrary-pair adapter can either follow the Pi template with provenance or use the public Hilbert-valued independence theorem. Both need an actual joint law; knowing the two marginals separately is insufficient.

## Smallest actual-law consumer and sequencing

1. Prove a named general multivariateGaussian μ 0 = Measure.dirac μ adapter. The inspected definition and CFC.sqrt_zero suggest simp [multivariateGaussian]; this is a proposed proof, not yet compiler evidence.
2. With frozen pair definitions, calculate each triangle residual covariance as zero and its fixed-pin mean. Evaluate the actual omitted-coordinate event under the Dirac law: pairSuccess G 0 1 t = 1, pairSuccess G 0 2 t = 0, pairSuccess G 1 2 t = 1 for t > 0. This proves genuine singular probabilities before any universal regression theorem is complete.
3. Identify the first single-pin cap with the Gaussian half-line under supports (a,b): its mass is normalCDF (min a b). On an open neighborhood of (t,2*t) for t > 0, this is exactly normalCDF a, so the second support derivative is zero. At the tied reference (t,t), both mass and the support tangent comparison remain meaningful, but a separate-support derivative should not be asserted.
4. Use map_codeScore_stdGaussian for the triangle's actual score law, then obtain its local threshold expansion and the rank-increasing normalized-addition derivative from the proved support and averaging infrastructure. The final target remains -(2/5) * q G t 1 2; no trace-only proof accepts WP10.

Required adverse boundaries remain: rank-zero pair residuals; unbounded cap; redundant parallel inequality; tied reference; zero canonical weight; rank-increasing positive-semidefinite addition; duplicates and zero threshold excluded only from internal calculus; full pair-law orthant frontier is not null because the pins lie on it.

No mathematical inconsistency was found in the scoped support/noise route. No build, derivative, axiom audit, or WP10 acceptance is claimed by this preflight.
