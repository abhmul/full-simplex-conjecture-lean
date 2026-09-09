# Building and auditing FSC

Run the commands below in a POSIX shell from the repository root unless a command changes directory. The recorded clean reconstruction used Linux. You need Git, [elan](https://github.com/leanprover/elan) with `lake` and `lean` on `PATH`, and Python 3.10 or newer for the audit scripts. Those scripts use only Python's standard library; no Python packages or agent-specific environment are required. Run Python without `-O` or `PYTHONOPTIMIZE`.

The repository selects Lean 4.31.0 through [lean-toolchain](../lean-toolchain). The exact WSC, mathlib and transitive revisions are recorded in [lakefile.toml](../lakefile.toml) and [lake-manifest.json](../lake-manifest.json). Keep these files unchanged when reproducing a result.

## Ordinary build

```sh
git clone https://github.com/abhmul/full-simplex-conjecture-lean.git
cd full-simplex-conjecture-lean
elan toolchain install leanprover/lean4:v4.31.0
lake env lean --version
lake exe cache get
lake build FSC FSCProbes --wfail
lake env lean -DwarningAsError=true FSC.lean
```

Lake obtains dependency sources at the committed manifest revisions. `lake exe cache get` downloads mathlib's compiled cache to speed up the ordinary build. The explicit build checks both the public library and the regression probes with warnings treated as errors; the last command separately compiles the public import root. Consumers use `import FSC`. A plain `lake build` builds the default `FSC` target.

Do not run `lake update` as a routine setup step: the committed manifest already fixes the dependency versions. Network access is needed to obtain the toolchain, dependency sources and optional cache.

## Fresh audits in an existing checkout

After the ordinary setup, run the maintained acceptance suite with a new evidence directory:

```sh
fsc_audit_dir=$(mktemp -d "${TMPDIR:-/tmp}/fsc-audit.XXXXXX")
python3 scripts/verify_release.py --evidence "$fsc_audit_dir/evidence"
```

The runner checks pins, builds both libraries, separately compiles the public root, runs fresh transitive axiom audits and independent expanded-statement checks, and exercises the required regressions and audit-parser calibrations. It records commands, exits, hashes and final status in `verification.json`. The two deliberately invalid calibration cases must be rejected; the runner checks their failure reasons.

This mode can reuse existing build products. Fresh axiom output from an existing checkout and artifact-free source reconstruction are separate checks. Use a different evidence directory for each run; the runner refuses to overwrite one.

## Artifact-free source reconstruction

Start from the committed revision you want to check, with a clean root and clean dependency source checkouts under `.lake/packages`. The ordinary setup above populates those dependencies. Alternatively, `lake env lean --version` materializes dependency sources from the existing manifest without building FSC. The preparation script expects those source repositories to exist; it does not bootstrap them itself.

From that prepared repository, run:

```sh
git status --short
fsc_repro_dir=$(mktemp -d "${TMPDIR:-/tmp}/fsc-source.XXXXXX")
python3 scripts/prepare_clean_checkout.py --destination "$fsc_repro_dir/checkout"
cd "$fsc_repro_dir/checkout"
python3 scripts/verify_release.py --require-clean --evidence "$fsc_repro_dir/evidence"
```

The root status must be empty. Both the clone destination and evidence directory must be absent before their respective scripts create them. Keep the evidence directory outside the new checkout, and do not invoke Lake in the new checkout before starting the runner.

Preparation creates independent Git source clones of the selected root commit and every pinned dependency, checks out their exact revisions, and rejects shared object alternates or inherited `.lake` directories. It copies no working-tree build products. The runner then requires a clean source tree and zero compiled artifacts before its first Lake invocation. It disables downloaded and local artifact caches, disables mathlib's cache-on-update hook, clears inherited Lean search paths and uses two Lean runtime threads. The installed, pinned Lean toolchain remains the compiler; it is not rebuilt.

This procedure rebuilds the imported dependency closure from source and can take substantially longer than the ordinary build. Existing caches in the preparation checkout do not affect the new source-only clones. Preparation evidence is written to `$fsc_repro_dir/checkout-preparation.json`; build and audit logs are under `$fsc_repro_dir/evidence`. Accept a run only after the script exits successfully and its final `verification.json` reports `passed: true` in artifact-free reconstruction mode.

See [RELEASE_AUDIT.md](RELEASE_AUDIT.md) for the recorded acceptance, exact certified source revision and retained evidence. The preprint is in preparation; the historical teaching and review notes are implementation inputs, not a released preprint.
