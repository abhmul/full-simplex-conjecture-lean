# Governing FSC implementation architecture

Reviewed 2026-09-08. External sources allowed; legacy material selected. This document controls implementation where raw consultation wording differs. The source manuscript remains an independent proof and fallback; no source is silently rewritten.

## Mathematical route

Use finite selected covariance directions, actual-support quadratic comparison, padded Gaussian energy, the componentwise scalar theorem, and a compact strict linear barrier. The support/noise variant supplies precisely the required feasible right derivative:
$$
G_s=D_s(G+sL)D_s,\quad L\succeq0,\qquad
\partial_{s+}F_{G_s}(t)\big|_{s=0}=\tfrac12\operatorname{tr}(S_GL).
$$
It follows from local second-order threshold expansion at a fixed covariance and averaging bounded functions over independent centered finite-second-moment noise. The normalization drift cancels the diagonal threshold-Hessian term. Read [the full derivation](pro-return/SUPPORT_NOISE_VARIATION.md) and [its reviewed audit](MATHEMATICAL_REVIEW.md).

This replaces positive-definite covariance density differentiation, covariance continuity of pair weights, antipodal regularization estimates and the integrated relative-differential passage. It does not remove canonical regression, support C¹ neighborhoods, exact weight compatibility, unbounded dilation or all-correlation CDF continuity. It does not prove a covariance Hessian or reverse Gaussian smoothing.

## Non-negotiable interface seams

One integration owner freezes the pair residual law, the remaining-coordinate event, q, stress, row quantities and facet normalization together. The full-index residual is a PSD linear image, including rank zero; do not choose a conditional-distribution version at a null pin.

Separate ordinary n-dimensional Gram realization from the later singular (n−1)-dimensional padded realization. Threshold calculus can use the ordinary realization. General row-maximal pair positivity must precede PD exclusion; it cannot depend on a facet construction that already assumes singularity. The graph in WORK_PACKAGES.md enforces this order.

At a positive common threshold and distinct unit normals, original and singly projected actual boundary hyperplanes do not coincide. Apply the finite standard-Gaussian support-C¹ lemma twice. Redundant inequalities and nonsimple intersections are allowed. Antipodal constraints are locally automatic in the pin, not removed from the original event.

The same q must occur in covariance variation, support differentiation and dilation. The equal-support reference may have ties; differentiate only at the actual support. Its lower-size comparison uses repeated existing inequalities to fill the list, not additional independent coordinates. Energy uses dimension n−2 including unused Gaussian directions.

PD exclusion uses L=G−δJ PSD and tr(SG)=0, giving a negative feasible derivative. Remaining finite tests use z_i=e_i−(k_i/κ)1 frozen at the base. They need neither a full PSD stress theorem nor GS=0. The scalar theorem retains strict component positivity. The compact barrier uses [0,T], with D(0)=0, and comparison precedes equality.

## Early evidence and alternative routes

Start compiler/API checks and the singular triangle derivative integration early, alongside an independent scalar/averaging/barrier branch. Passing rational identities alone does not pay the analytic seam. The triangle must exercise the actual law, redundant unbounded support, deterministic pair residual and rank-increasing derivative. Then prove the universal interface.

If a precise statement or representation fails, retain the counterexample/minimal reproducer and investigate the smallest repair. The original regularized Plackett argument in teaching-manuscript Chapter 4 is the fallback. Do not develop two full analytic engines preemptively. A namespace mismatch or ordinary cast problem is not an architectural obstruction.

The reciprocal/log choice is internal to the quadratic support-tangent contract. The geometric/entropy/envelope proof is an explanatory companion, not another required formalization project.

## Execution and evidence

Read docs/WORK_PACKAGES.md and claim a ready card. Task boundaries follow mathematical interfaces and may be refined when actual compiler evidence warrants it. Proposed declaration names are not automatically real APIs. Preserve graph and file ownership as they evolve.

Stage labels: planned; interface-frozen; in-progress; kernel-checked-local; reviewed; integrated; blocked. Infrastructure/spike packages have explicit non-theorem deliverables. Conditional assemblies remain labelled conditional and outside the release root. A package card must record the exact theorem type, imports, commands, axiom result and remaining consumers before acceptance.

The lead may use read-only critics and disjoint-file workers. No fixed staffing or duration is prescribed. The public contract and trust policy do not change merely because a proof is inconvenient. Keep the old WSC checkout and the separate research repository untouched.
