# Implementation log

## 2026-09-08: implementation lead appointed

The user appointed `/root` as sole integration and Git owner and authorized an unbudgeted implementation goal. Initial checkout: `449f42623d7442b27bff20df165bb9829196b67c`, clean. Verified Lean 4.31.0 (`68218e876d2a38b1985b8590fff244a83c321783`), WSC `a204c53cae45652d12524132dbb9a2e0ffe8cf78`, and mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. No Lean LSP tool is exposed; use actual compiler diagnostics. No global configuration changes.

Ownership before edits: root owns shared definitions, package graph/cards, state, integration roots, audit scripts and fixtures. Worker `wp00_imports` owns `FSCProbes/Imports.lean` and its separate evidence note. Worker `wp00_algebra` owns `FSCProbes/Algebra.lean` and its separate evidence note. Worker `analytic_preflight` owns only `docs/work-packages/WP10-preflight-evidence.md` for read-only analytic preparation. Workers do not commit. Root integrates serially.

WP00 is in progress: source/API consumers and actual Lean JSON audit calibration. WP01 definitions are being prepared against the reviewed support/noise convention. No FSC mathematical acceptance is claimed.

## First foundation milestone

WP00 real compiler probes/audit calibration and WP01 coupled definitions are integrated. The full WP14 scalar comparison/equality and WP20 compact barrier/contact derivative have compiled, been independently source-reviewed and freshly audited using only the permitted ordinary axioms. `lake build --wfail` now builds a nonempty production root (3091 total jobs, mostly cached), with explicit accepted foundation/generic imports. No FSC comparison/equality or covariance derivative endpoint is present. The root must continue with WP02/03/04/05/07/08/09 and downstream geometry; this is a local milestone, not the goal's stop rule.

Tooling: user explicitly authorized additional Lean debugging tools. Root installed leanclient 0.13.2 in the ignored checkout-local .lake directory and tested live goals/diagnostics. See LEAN_TOOLING.md. No pins/global configuration changed.

New ownership: wp00_algebra completed WP14 and now owns WP02 affine and ordinary Gram files/card/checks; wp00_imports completed import probes and now owns WP08 noise averaging file/card/checks; analytic_preflight owns SingularTriangle.lean, SingularTriangleAudit.lean, WP10 card and checks/wp10. Root owns the compact barrier and its audit, in addition to shared integration. Triangle subcases have genuine Gaussian laws, pair probabilities and unbounded redundant cap derivatives; full second-order/normalized-addition derivative acceptance remains open.

## Actual laws and analytic adapters milestone

Root independently reviewed the full WP02 affine/sum/ordinary Gram implementations, WP03 one-pin disintegration and degeneracy controls, WP08 dominated finite-second-moment averaging, product partial-to-Frechet/C2 and vector C2-to-Peano bridges. Actual importing consumers and fresh required-endpoint audits pass. The preserved WP03 stale-target audit failed on a missing declaration after a source/build race; stable source was rebuilt and the importing consumer and fresh audit rerun successfully. This is why upstream Lake target installation is part of acceptance.

The singular triangle's actual score law, deterministic pair laws, canonical q values and redundant cap derivatives were independently reviewed. Its separate threshold module now proves local C2 and full vector Peano through an exact event decomposition, actual Gaussian Fubini and scalar FTC. The rank-increasing normalized-addition derivative is the next critical consumer. Global measurable/bounded thresholdCDF wrappers have no PSD/rank/distinctness hypotheses and are installed for noise averaging.

Current ownership: wp00_algebra owns WP04 PairLaw.lean and PairWeights.lean; wp00_imports owns finite-Pi calculus and its evidence; analytic_preflight owns triangle threshold/variation files and audit evidence; root owns WP11 StandardDensity.lean, Dilation.lean and Padding.lean plus integration files. The generic calculus splits are routine dependency refinements supported by actual public API visibility and importing consumers. No final FSC theorem or clean-checkout release acceptance is claimed.

## Singular derivative, row positivity and ambient energy milestone

The early singular triangle certificate is complete, independently source-reviewed and freshly audited. Its derivative is the actual normalizedAdd Gaussian cdf derivative with the canonical coefficient −(2/5)q₁₂; rank, feasibility and strict sign are proved. The universal pair law/weights and general row-maximal positivity are integrated before PD exclusion. Finite-input partial derivative assembly is reviewed, with actual zero-dimensional and mixed 3-coordinate consumers.

WP11 closes the unbounded dilation derivative, strict energy positivity and exact Euclidean padding. Independent worker review checked density provenance/normalization, volume scaling, the derived integrable majorant and full ambient energy. Fresh source audit covers 18 endpoints; adverse audit covers 8 including the padded square strip and unbounded redundant halfline. The failed intermediate composition audit is preserved separately, with no acceptance claimed for its generated error axioms.

The production and permanent probe roots build with warnings as errors. Current work is actual support C1 (wp00_imports), normalized-addition law/explicit-Peano derivative infrastructure (analytic_preflight), all-correlation CDF continuity/compactness (wp00_algebra), and support convexity/tangent (root). WP06 reuses WP11's checked density bridge; WP13 currently reuses WP04 correlation bounds. These dependency corrections preserve the mathematical contracts. Final comparison, equality and clean-checkout acceptance remain open.
