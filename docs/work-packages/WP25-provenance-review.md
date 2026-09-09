# WP25 independent provenance and adverse coverage review

Owner: `/root/wp00_algebra`, assigned by the integration lead before edits. Exclusive owned paths are this file and `checks/release/provenance.json`. All other source is read-only. No commits, dependency changes, new-work licensing or publication actions are authorized for this review.

Status: reviewed. Scope is actual pinned source/license verification, original-input versus current-file hash comparison, and the documented PROBES adverse coverage map. This review did not rerun the test suite; the lead owns fresh release and clean-checkout execution. Machine-readable findings and exact hashes are in `checks/release/provenance.json`.

## Original inputs and current files

The review read every record in `docs/SOURCE_MANIFEST.json`, hashed each current file, and independently fetched the corresponding original Git blob from bootstrap commit `449f42623d7442b27bff20df165bb9829196b67c` using `git show`. All 17 original Git objects match the historical manifest's byte length and SHA256. The manifest itself has SHA256 `03f274d5c01eb5156b7cc7e423a3e5520384246a390ee4b8dadb7cea09535f19`.

Fifteen current files remain byte-identical to those original inputs. The only two evolved files are the deliberately implemented probes:

| File | Original SHA256 | Current SHA256 | Change evidence |
|---|---|---|---|
| `FSCProbes/Algebra.lean` | `c4bdee0472599e00779722c08f99519a83669bfd2e49cc238f9435bb7b178cfb` | `cf59ed3f4c77765a040f120d7dc32694a6ddf1e7238db267b01221a424690704` | Narrow source-supported imports and warning-clean proof syntax; WP00 algebra evidence. |
| `FSCProbes/Imports.lean` | `5a55001f4804e133cd608b1c47a0ee828978e6b2c631bed6df902aa35f359f24` | `571f9c69995c5ec887d7083300fd901c1fdc76da7323090f8ce0b45493c001fc` | Exact compiled public API consumers added; WP00 import evidence. |

All three supplied scripts (`audit_axioms.py`, `symbolic_checks.py`, `test_audit_axioms.py`) are still byte-identical to their manifest records. In particular, the audit parser did not change to accommodate failures. All original mathematical source manuscripts and Pro-return documents are unchanged. Historical statements such as the manifest's initial absence of adapted WSC source describe bootstrap provenance; the later two narrow adaptations are explicitly inventoried below. The original manifest was not rewritten to pretend that implemented probes were original inputs.

## Dependency pins and licensed source slices

At review HEAD `c5132e4e28f112d703757c531b310d3d22861371`, all ten dependency Git HEADs match the resolved `lake-manifest.json` revisions and every dependency has an empty tracked-change status. The principal pins are WSC `a204c53cae45652d12524132dbb9a2e0ffe8cf78`, mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, and `leanprover/lean4:v4.31.0`; actual `lake env lean --version` reports Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`. The JSON records all ten expected/actual revision pairs, not only the two direct dependencies.

Nine selected upstream source/license files were individually hashed and compared byte-for-byte with their pinned Git blobs: WSC `LICENSE`, `Gaussian/DensityRatio.lean`, `LogConcavity/Prekopa.lean`, and StatLean's `LICENSE`, `PiGaussian.lean`, `PiWithDensity.lean`, `WithDensityMap.lean`; mathlib `LICENSE` and `Analysis/Calculus/FDeriv/Partial.lean`. Every selected file matches. Their exact current SHA256 values are recorded in the JSON.

`FSC/Gaussian/StandardDensity.lean` explicitly identifies the narrow density slice from pinned WSC, its original source lines, the renamed declarations and indexing changes. Its comment contains the complete pinned MIT license and copyright notice byte-for-byte. The imported pinned StatLean files retain their Apache-2.0 provenance notices, upstream commit and selected original paths; their original license remains in the pinned dependency. Source review confirms the adaptation does not include the unused private covariance-density machinery.

`FSC/Analysis/FinitePartialDerivatives.lean` identifies the nonpublic variable-slice lemma in pinned mathlib, preserves the A Tucker copyright/authorship and Apache-2.0 attribution, documents its renaming, and explicitly limits the notice's scope to that adapted lemma. After only normalizing the declaration name and the notation `Function.uncurry f'` versus `↿f'`, the complete adapted lemma text equals the pinned upstream lemma. This is an adapted proof body, not a call to an unavailable declaration by a generated private name.

Source scan found no `_private.` reference in production. The actual support-convexity proof imports and calls the pinned public `WeakSimplex.isLogConcave_lintegral_right` from the existing Prekopa foundation; it does not re-prove or assume Prekopa. There is no root new-work LICENSE/COPYING file and no configured root Git remote. This review added no license, remote, publication, source/dependency edit or trust-boundary change.

## Documented adverse coverage

This table maps the actual requirements in unchanged `docs/pro-return/PROBES.md` to inspected source consumers. It records source coverage; the root's fresh release runner supplies final compiler/axiom execution receipts.

| Adverse or required analytic consumer | Existing permanent/check consumer |
|---|---|
| Actual source/API probes and allowed/rejected Lean-output audit calibration | `FSCProbes/Algebra.lean`, `FSCProbes/Imports.lean`, `checks/fixtures/AuditAllowed.lean`, `AuditRejected.lean`; WP00 calibration card. |
| Singular triangle actual score map, all three pair Dirac laws, successes 1/0/1, exact q values including q02=0 | `FSCProbes/SingularTriangle.lean` and its 29-endpoint audit; theorems `pairLaw_01/02/12`, `q_01/02/12`. |
| Actual single-pin law, unbounded redundant support, weaker derivative zero and support C1 | Same triangle module: `singleLaw_0`, `singlePinMass_0_eq_capMass`, redundant slice/support theorems and `redundant_support_C1`. |
| Actual normalized PSD-addition derivative −(2/5)q12 and rank increase 2→3 | `FSCProbes/TriangleVariation.lean`: actual scalar-noise law, event and averaging identity, derivative sign and `normalizedAdd_rank_increases`; universal theorem reapplied in `UniversalAnalyticAdverses.lean`. |
| Joint residual/pin Gaussian factorization, fixed pin support, arbitrary measurable-test Fubini | `FSC/Gaussian/PairLaw.lean`, `checks/wp04/LawAudit.lean`, `checks/wp04/Adverse.lean`; the full-index triangle Dirac laws exercise singular residuals. |
| Full-index pair law's orthant frontier is not null | Newly closed `checks/release/PairFrontierAdverse.lean`: actual triangle law assigns mass one to the full frontier at positive equal pins. |
| Five planar directions, actual support C1, projected inequalities y≤t, y≤t/2, −y≤t, redundant derivative zero | `checks/wp05-support/Adverse.lean`; actual five-score law, vector Peano/variation in `FSCProbes/UniversalAnalyticAdverses.lean`, physical padded components in `checks/wp16/Adverse.lean`. |
| Equal-support reference is nondifferentiable, yet the tangent applies at the actual supports | `checks/wp06/Adverse.lean` and `checks/wp19/Adverse.lean`, with actual nondifferentiability from the triangle cap. |
| Vector-domain threshold C2, Peano2 and exact canonical-q Hessian | `FSCProbes/ThresholdExpansionAudit.lean` and actual five-score Peano/variation consumers. |
| Bounded-function second-moment averaging, including rank-zero noise and no fourth-moment/density/global-C2 premise | `FSC/Analysis/NoiseAveraging.lean`, its expanded audit, and `checks/wp08/Adverse.lean`; inspected quadratic majorant and second-moment-only theorem signature. |
| Square-strip second moment 2H−2tφ(t), unused Gaussian direction H, strict normalized energy | `checks/wp11/Adverse.lean` and the actual padded-facet bridge in `checks/wp16/Adverse.lean`. |
| Unbounded redundant halfline dilation and energy | `checks/wp11/Adverse.lean`: `hasDerivAt_redundant_cap_dilation`, `redundant_halfLine_energy`. |
| Empty occupied scalar component falsifies the relaxed theorem | `checks/wp14/Adverse.lean`: exact supplied u=e=(1/2,0), omega=(1/2,1/2), M=6/5 counterexample. |
| Signed negative row losses and equality rigidity without universal q positivity | `checks/wp15/Adverse.lean`; actual q02=0 in the triangle retains the nonpositive-edge control. |
| Strict compact barrier, both endpoint exclusions, fixed-shape stationarity, equality only after comparison | Inspected `FSC/Threshold/LinearBarrier.lean` proof, `checks/WP20Audit.lean`, actual `Comparison.lean`/`Equality.lean` consumers. |
| Additional public-contract boundary controls | `checks/wp21/Adverse.lean` proves nonsimplex equality at every nonpositive threshold; `checks/wp23/Adverse.lean` covers positive strictness for full-rank, duplicate/antipodal and square configurations; WP24 covers the max-tail direction. |

The only explicit coverage gap found was the full-index pair-law frontier counterexample. The lead assigned the analytic worker a disjoint exact consumer during this review. Its proof uses the actual triangle pair Dirac law with mean `(t,t,t/5)` and proves full-frontier membership by arbitrarily small outward first-coordinate perturbations. `FSCChecks.PairFrontier.pairLaw_full_frontier_mass_one` and `_not_null` are now compiled; the analyst reported fresh required-endpoint audit success for all four declarations using only the permitted three axioms, saved as `checks/release/pair-frontier-axioms.jsonl`. This reviewer independently read and accepted the exact source, without rerunning it. No remaining missing PROBES category was identified.

One runner caution was sent to the lead: the early WP14 adverse file prints an unqualified theorem name inside its namespace, unlike the fully qualified later audit files. Any pretty-name mismatch must be caught and corrected by the fresh fail-closed audit run, not waived. This is an evidence-format check, not a mathematical gap.

## Verification scope

Commands used were read-only `git show`, `git rev-parse`, dependency `git status --porcelain --untracked-files=no`, exact source reads/searches, SHA256 computation with the prescribed Python environment, and `lake env lean --version`. The Python environment README was read first. No test/build suite was rerun by this review. The original research repository and WSC checkout outside the pinned dependency were not accessed or modified. The two owned review artifacts are ready for root integration; clean-checkout, final source snapshot and fresh release execution remain separate gates.
