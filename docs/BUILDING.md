# Building and checking the formalization

Run the commands below in a POSIX shell from the repository root unless a command changes directory. The recorded rebuild from scratch used Linux. You need Git, [elan](https://github.com/leanprover/elan) with `lake` and `lean` on `PATH`, and Python 3.10 or newer for the verification scripts. Those scripts use only Python's standard library, so they need no third-party packages and no special Python environment. Run Python without `-O` or `PYTHONOPTIMIZE`. These options remove Python assertions, which the scripts use for their checks, so the scripts refuse to run under them.

The file [lean-toolchain](../lean-toolchain) selects Lean 4.31.0. The exact revisions of the [WSC formalization](https://github.com/abhmul/weak-simplex-conjecture-lean), mathlib, and every transitive dependency are recorded in [lakefile.toml](../lakefile.toml) and [lake-manifest.json](../lake-manifest.json). Keep these files unchanged when reproducing a result.

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

Lake fetches the dependency sources at the revisions in the committed manifest. The command `lake exe cache get` downloads compiled mathlib files, which speeds up the ordinary build. The command `lake build FSC FSCProbes --wfail` builds both the library `FSC` and the regression probes `FSCProbes`, with warnings treated as errors. The last command compiles the top-level file `FSC.lean` separately. Projects that use the formalization write `import FSC`. A plain `lake build` builds the default target, `FSC`.

Do not run `lake update` as a routine setup step: the committed manifest already fixes the dependency versions. You need network access to obtain the toolchain, the dependency sources, and the optional mathlib cache.

## Verification suite in an existing checkout

After the ordinary build, run the verification suite with a new evidence directory:

```sh
fsc_audit_dir=$(mktemp -d "${TMPDIR:-/tmp}/fsc-audit.XXXXXX")
python3 scripts/verify_release.py --evidence "$fsc_audit_dir/evidence"
```

The suite checks the dependency pins, builds both libraries, and compiles the top-level file `FSC.lean` separately. It then makes fresh reports of the axioms, including indirect dependencies, used by the required declarations, by the restated theorems in [IndependentStatements.lean](../checks/release/IndependentStatements.lean), and by the required regression tests. Finally, it runs the tests and calibration cases of the axiom checker. It records the commands, their exit codes, file hashes, and the final status in `verification.json`. Two calibration cases are invalid on purpose and must be rejected, and the suite checks the reason for each rejection.

In this mode the suite can reuse existing build products. Fresh axiom reports from an existing checkout are therefore a separate check from the [rebuild from scratch](#rebuilding-from-scratch). Use a different evidence directory for each run, because the suite refuses to overwrite an existing one.

## Rebuilding from scratch

A rebuild from scratch compiles FSC and every dependency it imports from source, in a new checkout that starts with no compiled files. Its receipt records the mode `artifact-free-source-reconstruction`.

Start from a checkout of the committed revision you want to check. Its working tree and the dependency source checkouts under `.lake/packages` must all be clean. The ordinary build above fetches those dependencies. Alternatively, `lake env lean --version` fetches the dependency sources listed in the existing manifest without building FSC. The preparation script needs these source repositories to exist already; it does not fetch them itself.

From that checkout, run:

```sh
git status --short
fsc_repro_dir=$(mktemp -d "${TMPDIR:-/tmp}/fsc-source.XXXXXX")
python3 scripts/prepare_clean_checkout.py --destination "$fsc_repro_dir/checkout"
cd "$fsc_repro_dir/checkout"
python3 scripts/verify_release.py --require-clean --evidence "$fsc_repro_dir/evidence"
```

The command `git status --short` must print nothing. The clone destination and the evidence directory must not exist before the scripts create them. Keep the evidence directory outside the new checkout. Do not run Lake in the new checkout before starting the suite.

The preparation script clones the selected commit and every pinned dependency into independent Git repositories and checks out their exact revisions. It rejects a clone that shares Git objects through alternates or that inherits a `.lake` directory. It copies no build products from the working tree. The suite then requires a clean source tree and zero compiled files before it first runs Lake. It disables Lake's downloaded and local artifact caches, disables mathlib's cache-on-update hook, clears inherited Lean search paths, and runs Lean with two threads. The compiler is the installed Lean toolchain at the pinned version; the procedure does not rebuild it.

Since the procedure rebuilds every imported dependency from source, it can take substantially longer than the ordinary build. Existing caches in the checkout you prepared from do not affect the new source-only clones. The preparation script writes its record to `$fsc_repro_dir/checkout-preparation.json`, and the suite writes its build and audit logs under `$fsc_repro_dir/evidence`. Accept a run only after the suite exits successfully and its final `verification.json` reports `passed: true` in the mode `artifact-free-source-reconstruction`.

The [verification report](RELEASE_AUDIT.md) records the accepted run, the exact certified commit, and the retained evidence. The accompanying paper is [arXiv:2609.28452](https://arxiv.org/abs/2609.28452). The historical teaching and review notes are inputs to the implementation, not the paper.
