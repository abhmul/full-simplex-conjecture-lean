#!/usr/bin/env python3
"""Rebuild and audit the exact local FSC release. Evidence is never a proof oracle.

Use the documented agent-python interpreter. For final reproduction, run in a
fresh source-only checkout with --require-clean and an external evidence path.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
REQUIRED = [
    'FSC.cdf_simplex_le', 'FSC.cdf_eq_simplex_iff', 'FSC.cdf_simplex_lt',
    'FSC.lowerOrthant_simplex_le', 'FSC.coordinateMax_tail_le_simplex',
    'FSC.coordinateMax_tail_lt_simplex', 'FSC.coordinateMax_tail_eq_simplex_iff',
    'FSC.cdf_eq_measure', 'FSC.simplex_eq_scaled_matrix',
    'FSC.cdf_eq_probability_coordinateMax_le',
    'FSC.hasDerivWithinAt_normalizedAdd', 'FSC.peano2_thresholdCDF',
    'FSC.thresholdHessian_apply', 'FSC.capEnergy_padded_eq',
    'FSC.componentwise_compare', 'FSC.componentwise_equality',
]
PIN_FILES = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
REGRESSIONS = {
    'FSCProbes/Audit.lean': ['FSCProbes.triangleGramPSD'],
    'FSCProbes/FeasibleVariationAudit.lean': ['FSC.cdf_normalizedAdd_eq_noiseAverage'],
    'FSCProbes/SingularTriangleAudit.lean': ['FSCProbes.SingularTriangle.pairSuccess_02',
        'FSCProbes.SingularTriangle.not_differentiableAt_tied_support'],
    'FSCProbes/ThresholdExpansionAudit.lean': ['FSC.hasDerivWithinAt_normalizedAdd'],
    'FSCProbes/TriangleThresholdAudit.lean': ['FSCProbes.TriangleThreshold.peano2_thresholdCDF'],
    'FSCProbes/TriangleVariationAudit.lean': ['FSCProbes.TriangleVariation.hasDerivWithinAt_normalizedAdd',
        'FSCProbes.TriangleVariation.normalizedAdd_derivative_neg',
        'FSCProbes.TriangleVariation.normalizedAdd_rank_increases'],
    'FSCProbes/UniversalAnalyticAdversesAudit.lean': [
        'FSCProbes.UniversalAnalyticAdverses.fiveGram_actual_variation',
        'FSCProbes.UniversalAnalyticAdverses.fiveGram_actual_peano',
        'FSCProbes.UniversalAnalyticAdverses.triangle_universal_derivative'],
    'checks/wp02/Adverse.lean': ['FSCChecks.affine_zero_covariance'],
    'checks/wp03/Adverse.lean': ['FSCChecks.duplicateSingleLaw', 'FSCChecks.antipodalSingleLaw'],
    'checks/wp04/Adverse.lean': ['FSCChecks.fullPairSuccess'],
    'checks/wp05-support/Adverse.lean': ['FSCChecks.WP05Support.projected_weaker_derivative_zero',
        'FSCChecks.WP05Support.empty_ambient_C1', 'FSCChecks.WP05Support.unbounded_redundant_C1'],
    'checks/wp05/Consumer.lean': ['FSCChecks.WP05.mixed_product_C2'],
    'checks/wp05/FiniteConsumer.lean': ['FSCChecks.WP05.empty_input_C2',
        'FSCChecks.WP05.three_coordinate_C2'],
    'checks/wp06/Adverse.lean': ['FSCChecks.WP06.tied_reference_tangent'],
    'checks/wp07/VectorConsumer.lean': ['FSCChecks.WP07.mixed_quadratic_peano'],
    'checks/wp08/Adverse.lean': ['FSCChecks.WP08.dirac_zero_noise'],
    'checks/wp11/Adverse.lean': ['FSCChecks.WP11.square_strip_energy',
        'FSCChecks.WP11.redundant_halfLine_energy'],
    'checks/wp12/Adverse.lean': ['FSCChecks.WP12.rank_one_padded_law'],
    'checks/wp13/Adverse.lean': ['FSCChecks.cdf_duplicate_limit'],
    'checks/wp14/Adverse.lean': ['FSCChecks.emptyComponentCounterexample'],
    'checks/wp15/Adverse.lean': ['FSCChecks.WP15.negative_signed_row'],
    'checks/wp16/Adverse.lean': ['FSCChecks.WP16.square_actual_padding',
        'FSCChecks.WP16.planar_padded_components'],
    'checks/wp17/Adverse.lean': ['FSCProbes.SimplexRecursion.triangle_pin_actual_antipodal'],
    'checks/wp18/Adverse.lean': ['FSCProbes.MinimizerExclusions.replacement_actual_iid_cdf'],
    'checks/wp19/Adverse.lean': ['FSCChecks.SlopeRigidity.redundant_tied_reference_tangent'],
    'checks/wp21/Adverse.lean': ['FSCChecks.nonpositive_equality_without_simplex'],
    'checks/wp22/ComparisonAudit.lean': ['FSC.ReleaseComparisonChecks.allOnes_compare'],
    'checks/wp23/Adverse.lean': ['FSCChecks.WP23.signedGram_strict', 'FSCChecks.WP23.squareGram_strict'],
    'checks/wp24/Adverse.lean': ['FSCChecks.WP24.simplex_nonpositive_tail'],
    'checks/release/PairFrontierAdverse.lean': ['FSCChecks.PairFrontier.pairLaw_full_frontier_mass_one',
        'FSCChecks.PairFrontier.pairLaw_full_frontier_not_null'],
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(path: Path, *args: str) -> str:
    return subprocess.check_output(['git', '-C', str(path), *args], text=True).strip()


def verify_pins() -> list[dict]:
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.31.0'
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    receipts = []
    for package in manifest['packages']:
        name = package['name'].strip('«»')
        path = ROOT / manifest['packagesDir'] / name
        actual = git(path, 'rev-parse', 'HEAD')
        status = git(path, 'status', '--porcelain', '--untracked-files=normal')
        assert actual == package['rev'], (name, actual, package['rev'])
        assert not status, (name, status)
        receipts.append({'name': name, 'expected': package['rev'], 'actual': actual,
                         'source_status': status})
    versions = {r['name']: r['actual'] for r in receipts}
    assert versions['mathlib'] == 'fabf563a7c95a166b8d7b6efca11c8b4dc9d911f'
    assert versions['weak-simplex-conjecture-lean'] == 'a204c53cae45652d12524132dbb9a2e0ffe8cf78'
    wsc = ROOT / manifest['packagesDir'] / 'weak-simplex-conjecture-lean'
    assert (wsc / 'lean-toolchain').read_bytes() == (ROOT / 'lean-toolchain').read_bytes()
    wm = json.loads((wsc / 'lake-manifest.json').read_text())
    assert next(p['rev'] for p in wm['packages'] if p['name'] == 'mathlib') == versions['mathlib']
    return receipts


def main() -> int:
    if sys.flags.optimize:
        raise RuntimeError('Acceptance requires Python assertions enabled; remove -O/PYTHONOPTIMIZE.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--require-clean', action='store_true')
    args = parser.parse_args()
    os.chdir(ROOT)
    initial_status = git(ROOT, 'status', '--porcelain', '--untracked-files=normal')
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env.update(LEAN_NUM_THREADS='2', LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='false',
               LAKE_CACHE_DIR='', MATHLIB_NO_CACHE_ON_UPDATE='1')
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    report = {'schema_version': 1, 'revision': git(ROOT, 'rev-parse', 'HEAD'),
              'tree': git(ROOT, 'rev-parse', 'HEAD^{tree}'), 'cwd': str(ROOT),
              'initial_source_status': initial_status, 'passed': False,
              'require_clean': args.require_clean,
              'mode': 'artifact-free-source-reconstruction' if args.require_clean else 'current-checkout',
              'environment_controls': {k: env[k] for k in [
                  'LEAN_NUM_THREADS', 'LAKE_NO_CACHE', 'LAKE_ARTIFACT_CACHE',
                  'LAKE_CACHE_DIR', 'MATHLIB_NO_CACHE_ON_UPDATE']},
              'required_endpoints': REQUIRED, 'required_regressions': REGRESSIONS, 'commands': []}

    def save() -> None:
        (evidence / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')

    def run(label: str, command: list[str], expected: int = 0) -> str:
        logfile = evidence / f'{label}.log'
        started = time.monotonic()
        with logfile.open('w') as log:
            proc = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, env=env)
        receipt = {'label': label, 'command': command, 'exit': proc.returncode,
                   'expected_exit': expected, 'elapsed_seconds': time.monotonic() - started,
                   'log': logfile.name, 'sha256': digest(logfile)}
        report['commands'].append(receipt)
        save()
        print(f'{label}: exit {proc.returncode}', flush=True)
        if proc.returncode != expected:
            raise RuntimeError(f'{label}: expected {expected}, got {proc.returncode}; see {logfile}')
        return logfile.read_text()

    def audit(source: str, label: str, required: list[str] | None = None,
              expected: int = 0) -> str:
        command = [sys.executable, 'scripts/audit_axioms.py', source,
                   '--save-json', str(evidence / f'{label}.jsonl')]
        for name in required or []:
            command += ['--required', name]
        return run(label, command, expected)

    try:
        if args.require_clean:
            if initial_status:
                raise RuntimeError(f'Source checkout is dirty before acceptance: {initial_status}')
            if evidence.is_relative_to(ROOT):
                raise RuntimeError('Clean-checkout evidence must be outside the checkout.')
            artifacts = sorted(str(p.relative_to(ROOT)) for p in ROOT.rglob('*')
                if p.is_file() and ('.olean' in p.name or p.suffix in
                    {'.ilean', '.ir', '.o', '.so', '.a', '.ltar'}))
            report['startup_compiled_artifacts'] = artifacts
            if artifacts:
                raise RuntimeError(f'Compiled artifacts present before reconstruction: {artifacts[:20]}')
        report['pin_files_before'] = {p: digest(ROOT / p) for p in PIN_FILES}
        report['pins_before'] = verify_pins()
        sources = sorted([ROOT / 'FSC.lean', ROOT / 'FSCProbes.lean',
                          *ROOT.glob('FSC/**/*.lean'), *ROOT.glob('FSCProbes/**/*.lean')])
        report['lean_source_sha256'] = {str(p.relative_to(ROOT)): digest(p) for p in sources}
        prohibited = re.compile(r'(^\s*(?:private\s+)?axiom\b|\b(?:sorry|admit|native_decide)\b|_private\.)', re.M)
        bad = [str(p.relative_to(ROOT)) for p in sources if prohibited.search(p.read_text())]
        assert not bad, ('Production/probe placeholder or private-name scan', bad)
        lean_version = run('lean-version', ['lake', '--no-cache', 'env', 'lean', '--version'])
        assert '4.31.0' in lean_version and '68218e876d2a38b1985b8590fff244a83c321783' in lean_version
        run('lake-version', ['lake', '--version'])
        run('full-build', ['lake', '--no-cache', 'build', 'FSC', 'FSCProbes', '--wfail'])
        run('public-root', ['lake', '--no-cache', 'env', 'lean', '-DwarningAsError=true', 'FSC.lean'])
        audit('FSC/Audit.lean', 'public-axioms', REQUIRED)
        audit('checks/release/IndependentStatements.lean', 'independent-statements',
              [f'FSCChecks.IndependentStatements.{name}' for name in [
                  'comparison_expanded', 'equality_expanded', 'strict_comparison_expanded',
                  'tail_comparison_expanded', 'strict_tail_comparison_expanded',
                  'tail_equality_expanded']])
        audits = sorted({*ROOT.glob('FSCProbes/*Audit.lean'), *ROOT.glob('checks/wp*/Adverse.lean'),
                         *(ROOT / path for path in REGRESSIONS)})
        for source in audits:
            relative = str(source.relative_to(ROOT))
            audit(relative, 'regression-' + relative.replace('/', '-').removesuffix('.lean'),
                  REGRESSIONS.get(relative))
        run('audit-parser-tests', [sys.executable, 'scripts/test_audit_axioms.py'])
        audit('checks/fixtures/AuditAllowed.lean', 'calibration-allowed',
              ['FSCFixture.rfl_nat', 'FSCFixture.excluded_middle'])
        negative = audit('checks/fixtures/AuditRejected.lean', 'calibration-rejected',
                         ['FSCFixture.rejected'], expected=1)
        assert 'Nonstandard axioms for FSCFixture.rejected' in negative
        missing = audit('checks/fixtures/AuditAllowed.lean', 'calibration-missing',
                        ['FSCFixture.intentionally_missing'], expected=1)
        assert 'Required declaration missing from audit source' in missing
        report['pins_after'] = verify_pins()
        report['pin_files_after'] = {p: digest(ROOT / p) for p in PIN_FILES}
        assert report['pin_files_before'] == report['pin_files_after']
        assert git(ROOT, 'rev-parse', 'HEAD') == report['revision']
        assert git(ROOT, 'rev-parse', 'HEAD^{tree}') == report['tree']
        assert {str(p.relative_to(ROOT)): digest(p) for p in sources} == report['lean_source_sha256']
        report['final_source_status'] = git(ROOT, 'status', '--porcelain', '--untracked-files=normal')
        if args.require_clean:
            assert not report['final_source_status'], report['final_source_status']
        report['passed'] = True
        save()
        print('All release gates passed.', flush=True)
        return 0
    except Exception as exc:
        report['error'] = str(exc)
        save()
        raise


if __name__ == '__main__':
    raise SystemExit(main())
