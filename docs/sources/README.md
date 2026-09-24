# Mathematical sources

This directory holds the mathematical sources that the proof requires. Each file is byte-identical to its original, as recorded in [../SOURCE_MANIFEST.json](../SOURCE_MANIFEST.json). The full 2,206-line [TEACHING_MANUSCRIPT.md](TEACHING_MANUSCRIPT.md) is the self-contained mathematical proof. It is not the short navigation file of the same name in the research repository.

- [TEACHING_MANUSCRIPT.md](TEACHING_MANUSCRIPT.md): both complete proofs and the analytic prerequisites they share.
- [CORE_PROOF.md](CORE_PROOF.md): a compact version of the proof, using finitely many covariance directions. Its derivation of the covariance derivative by regularization is the fallback, which the formalization replaced with the reviewed support/noise variant of [SUPPORT_NOISE_VARIATION.md](../pro-return/SUPPORT_NOISE_VARIATION.md).
- [COMPONENTWISE_COMPARISON.md](COMPONENTWISE_COMPARISON.md): section 1 is the scalar theorem used by the main proof. The later generalizations and outside references are supplementary.
- [FRESH_ANALYTIC_AUDIT.md](FRESH_ANALYTIC_AUDIT.md): the fresh audit linked to the core proof, especially sections 4 and 5 on calculus at singular covariances.
- [CONTINUING_ANALYTIC_AUDIT.md](CONTINUING_ANALYTIC_AUDIT.md): the continuing audit linked to the core proof, especially on how the support derivatives (in the offsets of the constraints) and the energy identity fit together.

The original CORE_PROOF.md and COMPONENTWISE_COMPARISON.md keep their hyperlinks, which follow the layout of the research repository. Those links record provenance. They do not point to missing assumptions that the proof requires. The full teaching manuscript supplies the prerequisites the proof uses, and the two analytic audits the proof relies on are included here. Links to historical ingestion notes, optional methods, and numerical checks are not among the sources the proof requires. If you need an original, locate it through [../SOURCE_MANIFEST.json](../SOURCE_MANIFEST.json). Do not infer that a reference was supplied or formally verified merely because its name occurs.

The preferred variant in [ARCHITECTURE.md](../ARCHITECTURE.md) and the clarifications in [MATHEMATICAL_REVIEW.md](../MATHEMATICAL_REVIEW.md) govern the implementation, and [pro-return/SUPPORT_NOISE_VARIATION.md](../pro-return/SUPPORT_NOISE_VARIATION.md) contains the complete derivation of the support/noise variant. Preserve the original proof, both for its own explanatory value and as the location of the fallback.
