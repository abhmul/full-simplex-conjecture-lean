# Documentation guide

The accompanying preprint is in preparation. This directory contains the formalization's mathematical inputs, implementation records, and verification evidence.

## Reading and using the formalization

- [Repository README](../README.md): mathematical statement, public declarations, and quick start.
- [Public contract](PUBLIC_CONTRACT.md): exact quantifiers, equality condition, probability interpretation, and trust policy.
- [Building and reproduction](BUILDING.md): ordinary builds, audits, and artifact-free source reconstruction.
- [Acceptance report](RELEASE_AUDIT.md): certified revision, commands, independent reviews, and retained evidence.
- [Architecture](ARCHITECTURE.md): the support/noise proof route and its main interfaces.
- [Provenance](../PROVENANCE.md): dependencies, adapted source, attribution, and licenses.

## Mathematical inputs

[sources/](sources/README.md) preserves the supplied teaching proof and analytic notes. [pro-return/SUPPORT_NOISE_VARIATION.md](pro-return/SUPPORT_NOISE_VARIATION.md) develops the support/noise variation used by the formalization; [MATHEMATICAL_REVIEW.md](MATHEMATICAL_REVIEW.md) records corrections and its reviewed scope. These are development documents, not the forthcoming preprint.

## Implementation history

[STATE.md](STATE.md) records the integrated state. [WORK_PACKAGES.md](WORK_PACKAGES.md), its [machine-readable graph](WORK_PACKAGES.json), and [package cards](work-packages/) preserve interfaces, ownership, compiler experiments, failures, and acceptance evidence. [IMPLEMENTATION_LOG.md](IMPLEMENTATION_LOG.md) and [RESUME.md](RESUME.md) retain earlier milestones and the travel checkpoint.

The development used AI-assisted implementation and review. Historical coordinator prompts, local paths, and agent ownership labels document that process. Old “pending,” “conditional,” and “no remote” statements describe their recorded stage; the current public statements and final acceptance report determine the completed scope. Original logs and source manifests are preserved unchanged so their hashes remain verifiable.
