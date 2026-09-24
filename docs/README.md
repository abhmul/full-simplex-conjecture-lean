# Documentation guide

The formalization accompanies the paper [arXiv:2609.28452](https://arxiv.org/abs/2609.28452). This directory contains the mathematical inputs the formalization was built from, the records of its implementation, and the evidence of its verification.

## Reading and using the formalization

- [Repository README](../README.md): the theorem, the public declarations, build instructions, and the [relation to the paper](../README.md#relation-to-the-paper).
- [Public contract](PUBLIC_CONTRACT.md): the exact quantifiers, the equality condition, the link to Gaussian probabilities, and the trust policy (the allowed axioms and what counts as acceptance).
- [Building and checking](BUILDING.md): ordinary builds, the verification suite, and the rebuild from scratch.
- [Verification report](RELEASE_AUDIT.md): the certified commit, the commands run, the independent reviews, and the retained evidence.
- [Architecture](ARCHITECTURE.md): the route of the formal proof and its main interfaces.
- [Provenance](../PROVENANCE.md): dependencies, adapted source, attribution, and licenses.

## Mathematical inputs

[sources/](sources/README.md) preserves the supplied teaching manuscript of the proof and the analytic notes. [pro-return/SUPPORT_NOISE_VARIATION.md](pro-return/SUPPORT_NOISE_VARIATION.md) derives the derivative along added noise that the formalization uses, from a second-order expansion in the thresholds at a fixed covariance and an average over the noise. The development records call this derivation the support/noise variant. [MATHEMATICAL_REVIEW.md](MATHEMATICAL_REVIEW.md) records its review, with the corrections and the scope reviewed. These are development documents, not the paper.

## Development history

[STATE.md](STATE.md) records the state after all work packages were integrated. [WORK_PACKAGES.md](WORK_PACKAGES.md), its [machine-readable graph](WORK_PACKAGES.json), and the [package cards](work-packages/) preserve the interfaces, ownership, compiler experiments, failures, and acceptance evidence. [IMPLEMENTATION_LOG.md](IMPLEMENTATION_LOG.md) and [RESUME.md](RESUME.md) keep earlier milestones and the checkpoint saved when work paused for travel on 2026-09-08.

The implementation and its review were AI-assisted. Historical coordinator prompts, local paths, and agent ownership labels document that process. Older statements such as “pending,” “conditional,” and “no remote” describe the stage at which they were recorded. The current public statements and the final verification report determine the completed scope. Original logs and source manifests are kept unchanged, so their hashes can still be verified.
