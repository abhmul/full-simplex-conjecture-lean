# Full simplex conjecture: Lean formalization

Status: initialized implementation handoff, not a Lean proof of FSC. The human teaching proof and a separately reviewed support/noise variant are supplied in docs/sources and docs/pro-return. No public theorem has been formalized in this repository yet.

Start with [the implementation prompt](IMPLEMENTATION_PROMPT.md), [the architecture](docs/ARCHITECTURE.md), [the work-package graph](docs/WORK_PACKAGES.md), and [current state](docs/STATE.md). Use the project-local lean-work-package skill for a selected package.

The target is all-rank, all-real-threshold Gaussian-simplex stochastic domination for every correlation matrix, plus equality at a fixed positive threshold exactly at the simplex. The precise public statement is in docs/PUBLIC_CONTRACT.md. Existing WSC normalization assumptions must not leak into it.

This is a new local repository with no remote. The old WSC checkout is read-only. Exact WSC and mathlib revisions are in lakefile.toml; inspect the resolved manifest and actual package commits as part of WP00. Cache-assisted probes are not a clean-clone release certificate.

The lead owns integration and Git. Workers own disjoint files and return reviewed changes; they do not commit. The research coordinator owns the separate research repository and reviews mathematical contract changes, not routine Lean implementation.

Publication, public hosting and licensing of new work remain operator decisions. Existing dependency licenses are preserved; this scaffold does not relicense them or grant publication authority.
