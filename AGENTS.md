# FSC Lean project instructions

This is an implementation repository, separate from the research coordinator. Read docs/STATE.md, docs/ARCHITECTURE.md, docs/PUBLIC_CONTRACT.md and the selected card in docs/work-packages before proof work. Use .agents/skills/lean-work-package/SKILL.md. Read only the relevant mathematical source sections, not the entire research archive by default.

The appointed implementation lead is the sole integration/Git owner here. Workers may use disjoint files or separate worktrees; record ownership before edits. Workers return patches and evidence and do not commit. The lead may commit coherent local milestones. Do not edit the old WSC checkout or the research repository. Send mathematical contract issues and compact milestone reports to the research coordinator.

Keep Lean, mathlib and WSC pinned. Search exact local declarations and callers before re-proving infrastructure. Prefer Lean LSP for goals, diagnostics and search when available; record its absence, and use actual compiler diagnostics for safe source/API work. Do not claim an unavailable tool ran. No global configuration changes are authorized.

Preserve the all-correlation/all-threshold public comparison and positive-threshold equality contract. Distinctness and positive threshold are internal derivative hypotheses only. A mathematical gap, added public assumption, changed trust boundary or materially different dependency needs coordinator/operator review. Routine helper restructuring and dependency corrections are allowed with recorded evidence and unchanged mathematical contracts.

Production must contain no placeholders or custom axioms. Only a subset of propext, Classical.choice and Quot.sound is allowed in the final transitive axiom closure. Do not use native-computation axioms or hide unresolved analysis in instances. Keep explicitly parameterized conditional results outside FSC.lean. Check statements as well as axioms; a clean axiom report can certify the wrong statement.

Compile incrementally; install upstream Lake targets before compiling consumers. At milestones build with warnings as errors, compile the release root separately, run fresh transitive audits and review exact statements. The final release additionally requires artifact-free clean-checkout reproduction with all pins verified. Cached probes and an empty bootstrap root are not FSC certificates.

Keep source licenses/provenance. Existing WSC is a pinned dependency, not permission to import private declarations by generated names. Adapt a narrow source slice only with provenance, preserved notices and a fresh audit. No public remote, release or new-work license is authorized; operator decides those separately.

Continue useful in-scope work, including other independent packages when one interface is blocked. Stop for completion or a genuine authority/mathematical dependency boundary, with exact failed goals and minimal reproductions. No arbitrary time, token, pass or package-count limit is imposed. Do not interpret a local lemma completion as the whole project's stop rule.

Use apply_patch for authored files. Preserve LaTeX bytes through String.raw when using JavaScript wrappers; do not hard-wrap Markdown prose. Before Python, read /home/abhmul/Documents/vaults/agent-vault/agent-python/README.md and use its specialized environment. Keep task notes and measured costs; do not invent elapsed time or model-productivity comparisons.
