#!/usr/bin/env python3
"""Create independent source-only Git clones for FSC's clean reconstruction.

Never copies working-tree build products. Run only after committing the candidate.
The destination must not exist. No original source repository is modified.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess

from verify_release import ROOT, git, verify_pins


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', required=True, type=Path)
    args = parser.parse_args()
    dest = args.destination.resolve()
    if dest.exists():
        raise RuntimeError('Destination must not exist.')
    if git(ROOT, 'status', '--porcelain', '--untracked-files=normal'):
        raise RuntimeError('Commit the source candidate before reconstruction.')
    # verify_pins uses assertions, so refuse optimized execution explicitly.
    import sys
    if sys.flags.optimize:
        raise RuntimeError('Remove -O/PYTHONOPTIMIZE before acceptance.')
    verify_pins()
    revision = git(ROOT, 'rev-parse', 'HEAD')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    report = {'root_revision': revision, 'destination': str(dest), 'passed': False, 'clones': []}
    dest.parent.mkdir(parents=True, exist_ok=True)
    record = dest.parent / (dest.name + '-preparation.json')
    if record.exists():
        raise RuntimeError(f'Preparation evidence already exists: {record}')

    def save() -> None:
        record.write_text(json.dumps(report, indent=2) + '\n')

    def clone(source: Path, target: Path, rev: str, url: str | None = None) -> None:
        entry = {'source': str(source), 'target': str(target), 'expected_revision': rev,
                 'commands': [], 'passed': False}
        report['clones'].append(entry)
        save()
        commands = [
            ['git', 'clone', '--no-hardlinks', '--no-checkout', str(source), str(target)],
            ['git', '-C', str(target), 'checkout', '--detach', rev],
        ]
        if url is not None:
            commands.append(['git', '-C', str(target), 'remote', 'set-url', 'origin', url])
        for command in commands:
            proc = subprocess.run(command, text=True, capture_output=True)
            entry['commands'].append({'command': command, 'exit': proc.returncode,
                                      'stdout': proc.stdout, 'stderr': proc.stderr})
            save()
            if proc.returncode:
                raise RuntimeError(f'Clone command failed: {command}')
        entry['actual_revision'] = git(target, 'rev-parse', 'HEAD')
        entry['source_status'] = git(target, 'status', '--porcelain', '--untracked-files=normal')
        entry['origin'] = git(target, 'remote', 'get-url', 'origin')
        entry['has_alternates'] = (target / '.git/objects/info/alternates').exists()
        if entry['actual_revision'] != rev or entry['source_status'] or entry['has_alternates']:
            raise RuntimeError(f'Clone source verification failed: {target}')
        if (target / '.lake').exists():
            raise RuntimeError(f'Unexpected build directory copied: {target}')
        entry['passed'] = True
        save()
        print(f'Source clone verified: {target.name} {rev}', flush=True)

    try:
        clone(ROOT, dest, revision)
        for package in manifest['packages']:
            if package['type'] != 'git' or package['subDir'] is not None:
                raise RuntimeError('Unreviewed package source layout.')
            name = package['name'].strip('«»')
            clone(ROOT / manifest['packagesDir'] / name,
                  dest / manifest['packagesDir'] / name, package['rev'], package['url'])
        report['passed'] = True
        save()
        return 0
    except Exception as exc:
        report['error'] = str(exc)
        save()
        raise


if __name__ == '__main__':
    raise SystemExit(main())
