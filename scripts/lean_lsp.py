#!/usr/bin/env python3
"""Read-only Lean LSP goals, hover and diagnostics using the local leanclient install."""
from __future__ import annotations

import argparse
import dataclasses
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / '.lake/lean-tooling/python'))


def main() -> None:
    import leanclient

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('file', help='Path relative to the repository root')
    parser.add_argument('--line', type=int, help='One-based source line')
    parser.add_argument('--column', type=int, default=1, help='One-based source column')
    parser.add_argument('--hover', action='store_true')
    args = parser.parse_args()
    client = leanclient.LeanLSPClient(str(ROOT), prevent_cache_get=True)
    try:
        diagnostic_result = client.get_diagnostics(args.file)
        result = {'diagnostics': dataclasses.asdict(diagnostic_result)
                  if dataclasses.is_dataclass(diagnostic_result) else diagnostic_result}
        if args.line is not None:
            result['goal'] = client.get_goal(args.file, args.line - 1, args.column - 1)
            if args.hover:
                result['hover'] = client.get_hover(args.file, args.line - 1, args.column - 1)
        print(json.dumps(result, ensure_ascii=False, indent=2))
    finally:
        client.close()


if __name__ == '__main__':
    main()
