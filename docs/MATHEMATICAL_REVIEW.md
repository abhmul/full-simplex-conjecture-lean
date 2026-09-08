# Independent review of the support/noise variant

2026-09-08. Two independent mathematical reconstructions plus coordinator review accepted the variant at its stated FSC scope. This is analytic review, not Lean verification.

The first review reconstructed slicing/dominated convergence, the support-C¹ neighborhood, repeated differentiation, sequential-versus-joint pair-pin equality, all threshold-Hessian factors, finite-second-moment Peano averaging, and the normalized right derivative. The second checked every downstream consumer: PD exclusion, frozen finite directions, shared weights, padded energy, scalar comparison/equality, recursion, base cases and the strict barrier. No architectural gap was found.

## Clarifications controlling the raw note

1. The support lemma is for a finite family of unit normals and a standard Gaussian on the given finite-dimensional Euclidean space. These hypotheses are explicit in INTERFACES.md but abbreviated in the standalone note.
2. Pair regression requires −1<Gij<1. “Nonantipodal” alone is insufficient if duplicate coordinates have not yet been excluded.
3. Strict PD descent requires at least two sites; FSC's universal derivative contract is scoped to n≥3. At n=1, S=κ=0 and there is no descent.
4. The threshold-C² theorem is local near t1 with t>0 and distinct scores. Do not generalize it to arbitrary positive threshold vectors.

For the last boundary, let the scores be $(Z_1,Z_2,(Z_1+Z_2)/\sqrt2)$ and the threshold vector $(1,1,\sqrt2)$. Increasing the third threshold removes no constraint; decreasing it by ε removes a corner triangle of mass $\phi(1)^2\varepsilon^2+o(\varepsilon^2)$. No second-order Peano expansion exists there. At equal positive thresholds, the projected-boundary tie cannot occur.

Nonsimple intersections are not coincident hyperplanes. Low-rank residuals may be Dirac laws. A distinct rank-one score family has at most two sites; its antipodal CDF is smooth near a positive common threshold. At zero threshold or duplicate scores, the corner obstruction is real and excluded only from the internal analytic interface.

## Necessary proofs, not assumptions to hide

- Canonical Gaussian product laws and Fubini, with residual/pin joint Gaussianity.
- The neighborhood, not merely pointwise partial derivatives, in support C¹.
- Sequential pin mean and covariance equal the explicit pair law. Its density factor is exactly the manuscript's bivariate density.
- Global quadratic remainder bound derived from boundedness and local Peano expansion; domination by C(1+‖Y‖²).
- Universal singular normalized-addition derivative, not merely the triangle's trace algebra.
- General row-maximal pin positivity before PD exclusion; ordinary Gram realization before threshold expansion.
- Actual-support/facet compatibility, unbounded dilation, full padded energy, and all-correlation joint CDF continuity.

The original CDF-continuity and compactness obligations remain. The full relative covariance differential, q-continuity in covariance, envelope differentiation and Prékopa equality theory do not.

## Provenance and diagnostic replay

Raw consultation archive SHA-256: 26002f27abd9286cea628ef80a6a6e61fda64708aa1c9526cfdcdd2adcde8f34; 51,082 bytes, 22 safe members and 21 internal hash records. Five standalone notes match their archive members. All 12 export records, both supplied input hashes and 63 inspection-archive hash records verify; the prompt matches exactly. Six new attachments downloaded; two metadata failures concern already verified input files. No important recovery is required.

The coordinator read all three returned Python scripts, replayed all 12 synthetic audit-parser tests and the exact symbolic diagnostics successfully. These do not evaluate the Gaussian derivative or establish Lean compatibility. The supplied Lean probes were uncompiled by Pro. Current local compiler evidence is recorded separately in BOOTSTRAP_VERIFICATION.json.
