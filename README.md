# Full simplex conjecture: Lean formalization

The exact full simplex comparison and positive-threshold equality theorem are implemented in Lean. The public root is `import FSC`; final clean-checkout acceptance is in progress. The supplied teaching proof and reviewed support/noise route are preserved in docs/sources and docs/pro-return.

Start with [the implementation prompt](IMPLEMENTATION_PROMPT.md), [the architecture](docs/ARCHITECTURE.md), [the work-package graph](docs/WORK_PACKAGES.md), and [current state](docs/STATE.md). Use the project-local lean-work-package skill for a selected package.

`FSC.cdf_simplex_le` covers every n≥2, every PSD correlation matrix and every real threshold. `FSC.cdf_eq_simplex_iff` characterizes equality at any fixed positive threshold; `FSC.cdf_simplex_lt` gives strictness. `FSC.lowerOrthant_simplex_le` and the `FSC.coordinateMax_tail_*` theorems express the actual Gaussian event and maximum probabilities. See [the exact public contract](docs/PUBLIC_CONTRACT.md).

This is a local repository with no remote. The old WSC checkout is read-only. Exact WSC and mathlib revisions are in lakefile.toml and lake-manifest.json. Run `lake build FSC FSCProbes --wfail`; the complete acceptance runner is scripts/verify_release.py. Current gate status and evidence are in [STATE.md](docs/STATE.md).

The lead owns integration and Git. Workers own disjoint files and return reviewed changes; they do not commit. The research coordinator owns the separate research repository and reviews mathematical contract changes, not routine Lean implementation.

Publication, public hosting and licensing of new work remain operator decisions. Existing dependency licenses are preserved; this scaffold does not relicense them or grant publication authority.
