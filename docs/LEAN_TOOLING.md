# Local Lean debugging

This page records the local development setup. Building and checking the formalization do not need it; see [BUILDING.md](BUILDING.md).

The checkout uses pinned Lean 4.31.0 through `lake`. The user authorized additional debugging tooling on 2026-09-08. `leanclient==0.13.2` is installed only in the Git-ignored directory `.lake/lean-tooling/python`, with dependencies anyio 4.15.1, idna 3.19, orjson 3.12.0, psutil 7.2.2, tqdm 4.70.0, typing-extensions 4.16.0, and watchfiles 1.2.0. It is a development tool, outside the dependency graph of the proof.

Read the agent Python README before invoking Python. Then query a position in a file with

```bash
/home/abhmul/.local/share/agent-python/.venv/bin/python scripts/lean_lsp.py FSC/Definitions.lean --line 42 --column 3
```

Line and column are one-based. Add `--hover` for a declaration's type. The helper reports diagnostics and the current goal, then closes the server. It does not write source files. Authors still use `apply_patch`, and acceptance still uses fresh compiler builds and axiom audits.

To reinstall the client, run

```bash
uv pip install --python /home/abhmul/.local/share/agent-python/.venv/bin/python --target .lake/lean-tooling/python leanclient==0.13.2
```

The installation modifies no global agent configuration and no Lean pin of the project. The client documentation is at https://github.com/oOo0oOo/leanclient. Token savings and productivity compared with other tooling have not been measured.
