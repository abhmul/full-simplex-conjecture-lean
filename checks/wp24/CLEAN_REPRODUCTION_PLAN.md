# Independent source-build acceptance preparation

This is a read-only environment review and concrete command proposal by `/root/wp00_imports`, requested by the integration lead while WP24 awaits the final comparison/equality. No clean checkout or full source rebuild has been executed here. The integration lead owns execution and records the final committed revision and receipts under WP25.

## Verified command interfaces and controls

Actual pinned `lake --help` reports global `--no-cache`: build packages locally without downloading build caches. Actual `lake build --help` reports that a build does not update dependencies. Pinned mathlib `lakefile.lean:143` implements `post_update`; its `MATHLIB_NO_CACHE_ON_UPDATE=1` check suppresses the `lake exe cache get` hook. Both controls should apply during clean reproduction. Do not run `lake update` to refresh a manifest that already pins every dependency, and do not copy any `.lake` directory or local compiled artifacts.

The installed Lake source revealed an additional local-cache distinction: `Lake/Config/Env.lean:35–47` documents `noCache` as disabling downloads, while `Lake/Build/Module.lean:995` can still restore cached outputs when `Package.isArtifactCacheReadable` is true (its default). The clean process must therefore also set `LAKE_ARTIFACT_CACHE=false`, `LAKE_CACHE_DIR=` and `LAKE_NO_CACHE=true`. `Lake/Config/Env.lean:176–177` parses these controls, and `Lake/Config/Monad.lean:193` implements the artifact readability option. Clear inherited `LEAN_PATH` and `LEAN_SRC_PATH` for that process so another checkout cannot supply imported modules. Their actual current values were absent, but clean reproduction should establish this explicitly. These are process-local controls, not global configuration edits.

The verified executable output was Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`, and Lake 5.0.0-src+68218e8. Root and pinned WSC `lean-toolchain` both say `leanprover/lean4:v4.31.0`. The root manifest pins WSC `a204c53cae45652d12524132dbb9a2e0ffe8cf78` and mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; WSC's own committed manifest resolves its `v4.31.0` input to this same exact mathlib commit. Verify these again in the fresh checkout, including every transitive manifest entry, rather than relying on this checkpoint.

## Source-only start and build proposal

Run after the final source, manifests, audit files and required-endpoint list have been committed. A detached worktree preserves the repository's no-remote state and does not reuse ignored build products. Keep evidence outside the checkout so checking source cleanliness remains meaningful.

```sh
set -euo pipefail
fsc_accept_revision=$(git rev-parse HEAD)
test -z "$(git status --porcelain)"
fsc_accept_dir=$(mktemp -d /tmp/fsc-accept.XXXXXXXX)
git worktree add --detach "$fsc_accept_dir/checkout" "$fsc_accept_revision"
mkdir "$fsc_accept_dir/evidence"
cd "$fsc_accept_dir/checkout"
test ! -e .lake
git rev-parse HEAD > "$fsc_accept_dir/evidence/revision.txt"
git ls-files '*.olean' '*.ilean' '*.trace' '.lake/*' > "$fsc_accept_dir/evidence/tracked-artifacts.txt"
test ! -s "$fsc_accept_dir/evidence/tracked-artifacts.txt"
sha256sum lean-toolchain lakefile.toml lake-manifest.json > "$fsc_accept_dir/evidence/pin-files.before.sha256"
lake --version > "$fsc_accept_dir/evidence/lake-version.txt"
unset LEAN_PATH LEAN_SRC_PATH
export LAKE_NO_CACHE=true LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR= MATHLIB_NO_CACHE_ON_UPDATE=1
env LEAN_NUM_THREADS=2 lake --no-cache env lean --version > "$fsc_accept_dir/evidence/lean-version.txt"
env LEAN_NUM_THREADS=2 lake --no-cache build FSC FSCProbes --wfail > "$fsc_accept_dir/evidence/full-build.log" 2>&1
env LEAN_NUM_THREADS=2 lake --no-cache env lean --json -DwarningAsError=true FSC.lean > "$fsc_accept_dir/evidence/public-root.jsonl" 2> "$fsc_accept_dir/evidence/public-root.stderr"
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
sha256sum lean-toolchain lakefile.toml lake-manifest.json > "$fsc_accept_dir/evidence/pin-files.after.sha256"
cmp "$fsc_accept_dir/evidence/pin-files.before.sha256" "$fsc_accept_dir/evidence/pin-files.after.sha256"
```

The lead should record actual process exit codes as structured evidence, including failed commands if any. The commands above use `set -e`, so a failed gate cannot silently advance. Verify package source HEADs and cleanliness immediately after resolution and again after building. Match each entry in `lake-manifest.json.packages` against its actual `.lake/packages` checkout (`name` may have Lean guillemet quoting, e.g. `«weak-simplex-conjecture-lean»`). Check the exact root and WSC toolchain and WSC-to-mathlib manifest agreement. There are ten root manifest entries, including all transitive revisions; branch-valued `inputRev` fields do not override exact resolved `rev`.

## Measured Lake concurrency control

The lead requested a bounded concurrency setting for a machine with 16 logical processors and 16 GiB RAM. No Lake `-j` option appears in the actual CLI. The installed runtime binary contains the `LEAN_NUM_THREADS` environment key; its runtime C++ implementation is absent from the installed source bundle. An actual minimal Lake project in `checks/wp24/concurrency/` therefore tested the setting instead of assuming it controls external compiler jobs. Four independent modules import only `Init`; each records monotonic start/end times around a 500 ms `IO.sleep`, then the aggregate module imports them. This is an execution probe, never an imported mathematical proof or acceptance endpoint.

Both full mini-builds returned exit 0 with `--wfail` and all cache controls disabled. `LEAN_NUM_THREADS=1` produced intervals `[1554864,1555365]`, `[1555781,1556281]`, `[1556636,1557136]`, `[1557430,1557931]`, with maximum overlap one. After cleaning only that probe's build outputs, `LEAN_NUM_THREADS=2` produced `[1607357,1607857]`, `[1607359,1607859]`, and twice `[1608150,1608650]`, with maximum overlap two. Raw logs are `checks/wp24/concurrency-one-thread.log` and `checks/wp24/concurrency-two-threads.log`. The probe does not estimate final theorem build time or peak memory.

The proposed root build uses process-local `LEAN_NUM_THREADS=2`, with observed memory monitored by the lead. `LEAN_NUM_THREADS=1` is a tested serial fallback if actual module memory pressure requires it. These settings do not alter mathematical options, source files, pins or global configuration. The first probe elaboration failed because its initial `#eval do` inferred `BaseIO` from the clock operation and then rejected `IO.println : IO Unit`; explicitly annotating `#eval show IO Unit from do` repaired the execution-only probe. No environment setting was accepted solely from that failed attempt.

The source/license review should cover the two presently documented narrow adaptations: `FSC/Gaussian/StandardDensity.lean` preserves the complete pinned WSC MIT notice and records the exact private source slices; `FSC/Analysis/FinitePartialDerivatives.lean` preserves A Tucker's copyright/Apache attribution and exact mathlib source/pin for the variable-slice helper. Other new work has not been assigned a license. The actual pinned WSC `HEAD:LICENSE` was read and matches its recorded MIT notice. Existing imported StatLean provenance remains within the pinned WSC dependency. Verify these receipts in the final source revision rather than treating this inventory as final acceptance.

## Fresh audit and expanded statement gates

Run `scripts/audit_axioms.py FSC/Audit.lean` with every explicitly required final endpoint, saving the fresh JSON under the evidence directory. Its subprocess runs `lake env lean --json -DwarningAsError=true`; after the above full build this consumes only the freshly rebuilt imported artifacts. The required set must at least include the closed comparison, equality, strictness, lower-orthant measure, maximum-event dictionary and maximum-tail endpoints. Add the release-critical analytic/scalar endpoints selected by WP25. Run positive/negative audit calibration fixtures and `scripts/test_audit_axioms.py` afresh as separate gates; the negative fixture's nonzero exit is expected and must be checked explicitly.

Compile an importing expanded-statement consumer with literal `Matrix.PosSemidef G ∧ ∀ i, G i i = 1`, literal `multivariateGaussian` event measures, and the displayed simplex matrix. This independently checks no `DistinctScores`, positive threshold for comparison, rank assumption, hidden certificate or normalized WSC predicate leaked through aliases. Check equality and strictness at exactly positive threshold. The maximum-tail comparison must be `Pr_G(t < max) ≤ Pr_simplex(t < max)`; its strict and equality wrappers have the corresponding fixed-positive-threshold statements. Print/unfold `cdf`, `simplex`, `WeakSimplex.IsCorrelation` and `WeakSimplex.coordinateMax`, and review the actual theorem types alongside the importing consumers.

## Known source-build seam, not an observed failure

Pinned mathlib `lakefile.lean:13` passes `errorOnBuild` to its ProofWidgets dependency. Pinned ProofWidgets `lakefile.lean:54–86` constructs the `widgetJsAll` target, and lines 67–68 throw that configured error when the JavaScript output trace is absent or stale. Its source build commands, in `widget/`, are `npm clean-install` followed by `npm run build`; the library's `needs` includes `widgetJsAll`. This is a potential clean no-cache build failure, not a compiler failure observed by this worker.

Further actual `git ls-files` inspection established that this pinned ProofWidgets commit already tracks `widget/js/*.js` and `widget/js/lake.trace`. A fresh source checkout therefore contains those exact source-pinned assets and their trace; no asset download or Lean-cache reuse should be necessary when the committed trace matches. The error path above remains relevant only if an actual clean build finds that trace stale or missing. Do not preemptively rebuild or fetch assets.

If it occurs, preserve the exact failing Lake target/output. Inspect the pinned package lock, source asset paths and target configuration; do not silently fetch Lean caches or relax the trust policy. A direct package-local `env MATHLIB_NO_CACHE_ON_UPDATE=1 lake --no-cache build widgetJsAll` may omit the downstream-only `errorOnBuild` configuration, but this is a proposed source-asset remedy, not yet executed or verified. A successful remedy must build from the pinned sources/lock without changing any tracked package file and must retain separate logs. Only then rerun the unchanged root source-build gate. No new dependency, global configuration or publication action is part of this plan.
