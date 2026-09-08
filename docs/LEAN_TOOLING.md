# Local Lean debugging

The checkout uses pinned Lean 4.31.0 through `lake`. The user authorized additional debugging tooling on 2026-09-08. `leanclient==0.13.2` is installed only in the ignored `.lake/lean-tooling/python` directory, with dependencies anyio 4.15.1, idna 3.19, orjson 3.12.0, psutil 7.2.2, tqdm 4.70.0, typing-extensions 4.16.0 and watchfiles 1.2.0. It is a development tool, outside the proof dependency graph.

Read the agent Python README before invoking Python. Then query a file using `/home/abhmul/.local/share/agent-python/.venv/bin/python scripts/lean_lsp.py FSC/Definitions.lean --line 42 --column 3`. Line and column are one-based; add `--hover` for a declaration's type. The helper reports diagnostics and the current goal and closes the server afterward. It does not write source files. Authors still use `apply_patch`; acceptance still uses fresh compiler builds and audits.

Reinstallation: `uv pip install --python /home/abhmul/.local/share/agent-python/.venv/bin/python --target .lake/lean-tooling/python leanclient==0.13.2`. No global agent configuration or project Lean pin is modified. The client documentation is https://github.com/oOo0oOo/leanclient. No claim about token savings or comparative productivity has been measured.
