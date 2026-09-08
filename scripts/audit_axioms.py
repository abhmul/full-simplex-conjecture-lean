#!/usr/bin/env python3
"""Fail-closed Lean JSON axiom-report checker.

Original consultation utility, not copied WSC source. Preserves WSC's useful
source-position and coverage checks, adds empty-axiom reports and accepts any
subset of the three ordinary axioms. Python tests are not a Lean trust audit.
Run from the actual pinned Lean project root, not the inspection archive.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Iterable

ALLOWED = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
COMMAND = re.compile(r"^[ \t]*#print[ \t]+axioms[ \t]+([A-Za-z0-9_'.]+)[ \t]*$", re.M)
REPORT = re.compile(r"\A'(.+)'\s+depends on axioms:\s*\[([^]]*)\]\Z", re.S)
EMPTY = re.compile(r"\A'(.+)'\s+does not depend on any axioms\Z")

def validate(source: str, output: str, audit_file: Path,
             required: Iterable[str] = ()) -> list[str]:
    errors: list[str] = []
    pairs = [(m.group(1), source.count('\n', 0, m.start()) + 1)
             for m in COMMAND.finditer(source)]
    names = [name for name, _ in pairs]
    expected = dict(pairs)
    if not pairs:
        errors.append('No audit declarations found.')
    if len(expected) != len(pairs):
        errors.append('Duplicate audit commands.')
    for name in set(required) - set(names):
        errors.append(f'Required declaration missing from audit source: {name}')
    seen: set[str] = set()
    for lineno, raw in enumerate(output.splitlines(), 1):
        if not raw.strip():
            continue
        try:
            diag = json.loads(raw)
        except json.JSONDecodeError:
            errors.append(f'Non-JSON output on line {lineno}.')
            continue
        if not isinstance(diag, dict):
            errors.append(f'Non-object diagnostic on line {lineno}.')
            continue
        if diag.get('severity') in {'error', 'warning'}:
            errors.append(f"Compiler {diag['severity']} on output line {lineno}.")
        text = diag.get('data')
        if not isinstance(text, str):
            continue
        full, empty = REPORT.fullmatch(text), EMPTY.fullmatch(text)
        if full is None and empty is None:
            continue
        name = full.group(1) if full is not None else empty.group(1)
        axs = ([a.strip() for a in full.group(2).split(',') if a.strip()]
               if full is not None else [])
        if name in seen:
            errors.append(f'Duplicate report: {name}')
        seen.add(name)
        if name not in expected:
            errors.append(f'Unexpected report: {name}')
            continue
        if diag.get('severity') != 'information':
            errors.append(f'Non-information axiom report: {name}')
        pos = diag.get('pos')
        if not isinstance(pos, dict) or pos.get('line') != expected[name] or pos.get('column') != 0:
            errors.append(f'Wrong source position: {name}')
        fname = diag.get('fileName')
        if not isinstance(fname, str) or Path(fname).resolve() != audit_file.resolve():
            errors.append(f'Wrong source file: {name}')
        if len(axs) != len(set(axs)):
            errors.append(f'Duplicate axiom token: {name}')
        unexpected = set(axs) - ALLOWED
        if unexpected:
            errors.append(f'Nonstandard axioms for {name}: {sorted(unexpected)}')
    for name in set(names) - seen:
        errors.append(f'Missing report: {name}')
    return errors

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('audit_file', type=Path)
    ap.add_argument('--required', action='append', default=[],
                    help='Repeat for every release-critical theorem.')
    ap.add_argument('--save-json', type=Path)
    args = ap.parse_args()
    try:
        source = args.audit_file.read_text(encoding='utf-8')
        run = subprocess.run(['lake', 'env', 'lean', '--json',
                              '-DwarningAsError=true', str(args.audit_file.resolve())],
                             capture_output=True, text=True, check=False)
    except (OSError, UnicodeError) as exc:
        print(f'No audit completed: {exc}', file=sys.stderr)
        return 2
    if args.save_json:
        args.save_json.write_text(run.stdout, encoding='utf-8')
    sys.stderr.write(run.stderr)
    if run.returncode != 0:
        sys.stdout.write(run.stdout)
        return run.returncode
    errors = validate(source, run.stdout, args.audit_file, args.required)
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'Fresh axiom audit passed for {len(list(COMMAND.finditer(source)))} declarations.')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
