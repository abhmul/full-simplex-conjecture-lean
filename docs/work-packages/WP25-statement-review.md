# Independent public-statement review

Owner: analytic_preflight, exclusively assigned checks/release/IndependentStatements.lean and this report by the integration lead after WP19 acceptance. The lead retains FSC/Audit.lean, the overall release report, full builds, clean-checkout reproduction and Git. This is an independent mathematical statement gate, not publication authorization.

The worker reread PUBLIC_CONTRACT.md and ENVIRONMENT_AND_ACCEPTANCE.md and inspected the exact pinned definitions. WeakSimplex.IsCorrelation is transparently Matrix.PosSemidef together with unit diagonal. IsWeakSimplexCov is a different, stronger predicate and is not the public hypothesis. FSC.cdf is exactly the toReal of the actual multivariateGaussian zero-mean lower-orthant measure. lowerOrthant is the literal set of vectors whose every coordinate is at most the threshold. The chosen Gaussian law is defined for singular PSD matrices; no ambient density is required by the event definition.

FSC.simplex is the pinned regularSimplexGram. Its pinned definition already uses real subtraction in the denominator, and simplex_eq_scaled_matrix proves the exact displayed matrix (1/(n-1))•(n•I-J) under n >= 2. simplex_apply proves diagonal one and off-diagonal -1/(n-1). The independent source expands J into the literal constant-one matrix and the coordinate/event types into EuclideanSpace over Fin n, avoiding any reliance on the names alone.

## Accepted expanded statements

After the final public root was installed, IndependentStatements.lean imports only FSC. It compiles theorem consumers with separate G.PosSemidef and unit-diagonal hypotheses, the explicit EuclideanSpace ℝ (Fin n) sample type, the literal simplex matrix (1/(n-1))•(n•I-Matrix.of(fun _ _ => 1)), and actual multivariateGaussian event measures. The real denominator subtraction is visible in every expanded statement.

| Public endpoint | Independently checked domain and conclusion |
| --- | --- |
| cdf_simplex_le; lowerOrthant_simplex_le | Every n >= 2, every PSD correlation G, every real t; simplex lower-orthant probability <= G probability. |
| cdf_eq_simplex_iff | Every n >= 2 and every PSD correlation at one fixed t > 0; equality of actual probabilities iff G equals the explicit simplex matrix. |
| cdf_simplex_lt | Same positive-threshold domain and G unequal to the simplex; simplex probability is strictly smaller. |
| coordinateMax_tail_le_simplex | Every real t; G's upper-tail probability <= the simplex upper-tail probability. |
| coordinateMax_tail_lt_simplex; coordinateMax_tail_eq_simplex_iff | Positive t gives strict inequality for every nonsimplex correlation and equality iff simplex. |

The tail consumers further replace the finite-maximum notation with the literal event {x | ∃ i, t < x i}. tail_event_expanded proves this event identity from the maximum/orthant dictionary. This checks both the strict > convention and the reversed order. The equality consumer works with equality of the original ENNReal measures, not merely a named real CDF.

No final endpoint has a distinctness, full-rank, balance, honest-simplex, normalized-WSC, minimizer, lower-size induction, support, Peano, covariance differentiability, certificate, or auxiliary-instance hypothesis. The n=2 branch is included. The comparison includes duplicate scores, antipodes, every PSD rank and nonpositive thresholds. The equality endpoints require precisely positive threshold; the existing nonpositive_equality_without_simplex adverse theorem in checks/wp21/Adverse.lean witnesses why that condition is essential.

## Independent source review

The worker read final Comparison.lean, Equality.lean, Main.lean and the actual event/maximum definitions. Comparison closes strong induction using only lower-size comparison and the strict compact barrier. At the barrier minimum, actual Gaussian continuity admits every correlation, duplicate exclusion pays the threshold derivative hypothesis, and the proved WP19 minimum slope pays the slope condition. The nonpositive branch is explicit. Equality first turns a positive contact into an actual global shape minimum using the now-proved comparison, then applies ordinary threshold contact differentiation and the proved minimum rigidity. It does not assume lower-size uniqueness. The measure and tail wrappers preserve the finite-probability event dictionaries and the correct order.

The expanded statements and final source are independently accepted. This review does not substitute for the lead's full warning-clean builds, fresh release audit or artifact-free clean-checkout reproduction.

## Fresh evidence and source identity

The importing audit command was specialized-Python scripts/audit_axioms.py checks/release/IndependentStatements.lean with each of the seven public endpoints and six expanded comparison/equality/strict/tail endpoints required, saving checks/release/independent-statements-axioms.jsonl. It exited 0 for 17 declarations after the file was reduced to import FSC only. The receipt includes exact printed public and expanded types plus each transitive axiom report; every report is a subset of propext, Classical.choice and Quot.sound.

Live checks confirm Lean 4.31.0 (commit 68218e876d2a38b1985b8590fff244a83c321783), WSC a204c53cae45652d12524132dbb9a2e0ffe8cf78 and mathlib fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. The audit was run on the resumed candidate based on c5132e4e28f112d703757c531b310d3d22861371 with the lead's final source additions. The lead's release receipts bind the committed candidate revision to the same source; the independently reviewed source hashes are:

| Source | SHA-256 |
| --- | --- |
| FSC/Comparison.lean | e0c57aa40de997e4a7dd9d49bb884837423982e1e5c51563dbfcbeee9a222731 |
| FSC/Equality.lean | b9359b1a8630148cc14e3913bcad313a0ed33564112355361edb038eabff81df |
| FSC/Main.lean | 8cc5d0d0a53e7027b25a3e48a40167314a7e322b1a40c63d4668b2adfc9a9c20 |
| FSC.lean | 2914a43b2ff05422c6befe89b15e1d530be54be76c1cfd3e8554d8c8023df55d |
| checks/release/IndependentStatements.lean | c9fddfcfb4c61fe18403eea2da85ec349a0a878be524e421558573bc5521df4d |

Compiler evidence: a literal two-argument function on the right of matrix subtraction was inferred as a Pi function even with binder/type annotations. Matrix.of supplies the explicit matrix representation without changing entries or introducing a hypothesis. Printing the entire simplex-entry proof produced unnecessary tactic proof terms; named theorem checks print the complete types while the predicate and CDF definitions are explicitly printed. Interim direct Equality/Main imports were removed before the accepted public-root audit.

## Exact pair-law frontier negative control

The lead additionally assigned checks/release/PairFrontierAdverse.lean exclusively to this worker after both independent reviewers identified the remaining raw PROBES coverage item. The actual triangle pairLaw at pins (0,1) and threshold t > 0 is the proved Dirac law at (t,t,t/5). pairMean_01_mem_full_frontier proves this point lies on the frontier of the full three-coordinate lower orthant: it belongs to the orthant, and arbitrarily small increases of the first pinned coordinate leave it. pairLaw_full_frontier_mass_one therefore proves that this actual pair law gives the full frontier mass one, and pairLaw_full_frontier_not_null disproves the erroneous frontier-null statement. This validates the requirement to omit the two pinned coordinates from pairSuccess.

The specialized-Python audit of checks/release/PairFrontierAdverse.lean explicitly required both final mass-one/non-null endpoints and saved checks/release/pair-frontier-axioms.jsonl. It exited 0 for all four declarations, with only the permitted standard axioms. Initial warning-error iterations rejected unnecessary tactic sequencing and a ring call after norm_num had closed its goal; the final source contains no placeholder and the importing audit was freshly rerun. This concrete negative control complements the already-accepted singular pair probabilities 1/0/1 and the generic deterministic-frontier test.
