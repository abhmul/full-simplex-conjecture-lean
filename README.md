# Full Simplex Conjecture in Lean

[![Lean CI](https://github.com/abhmul/full-simplex-conjecture-lean/actions/workflows/lean_action_ci.yml/badge.svg?branch=main)](https://github.com/abhmul/full-simplex-conjecture-lean/actions/workflows/lean_action_ci.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2609.28452-b31b1b.svg)](https://arxiv.org/abs/2609.28452)

This repository contains the Lean 4 formalization of the main theorem of

> Abhijeet Mulgund, [*Stochastic Domination of Gaussian Maxima by the Regular Simplex*](https://arxiv.org/abs/2609.28452), arXiv:2609.28452, 2026.

Among centered Gaussian vectors with unit variances, the one whose correlations all equal $-1/(n-1)$ (the regular simplex) has the stochastically largest maximum coordinate. At each fixed $t>0$, no other correlation matrix attains the largest value of $\mathbb{P}[\max_iX_i>t]$. The formalization proves this theorem, Theorem 1.1 of the paper, and Lean's kernel checks the proof. [Relation to the paper](#relation-to-the-paper) says precisely what is certified and what is not.

The formalization is complete and has passed every check in the [verification report](docs/RELEASE_AUDIT.md). It builds on [mathlib](https://github.com/leanprover-community/mathlib4) and on the [formalization](https://github.com/abhmul/weak-simplex-conjecture-lean) of the preceding paper on the Weak Simplex Conjecture (WSC), arXiv:2607.14087. It is pinned to Lean 4.31.0.

## Main theorem

Let $n\ge2$, let $G$ be a real $n\times n$ positive-semidefinite matrix with unit diagonal (a correlation matrix), and put

$$
\Delta_n=\frac{nI-J}{n-1},
\qquad
F_G(t)=\mathbb{P}_{X\sim\mathcal{N}(0,G)}[X_i\le t\text{ for every }i],
$$

where $J$ is the all-ones matrix. Then for every real threshold $t$,

$$
F_{\Delta_n}(t)\le F_G(t).
$$

For each fixed $t>0$,

$$
F_G(t)=F_{\Delta_n}(t)
\quad\Longleftrightarrow\quad
G=\Delta_n.
$$

Equivalently, the regular simplex maximizes the upper tail of the maximum coordinate:

$$
\mathbb{P}_{X\sim\mathcal{N}(0,G)}[\max_i X_i>t]
\le
\mathbb{P}_{Y\sim\mathcal{N}(0,\Delta_n)}[\max_i Y_i>t].
$$

This is Theorem 1.1 of the paper, which writes $\mathcal{E}_n$ for the set of $n\times n$ correlation matrices and $D_n(t)$ for $F_{\Delta_n}(t)$.

The comparison covers singular matrices, repeated coordinates ($g_{ij}=1$), antipodal coordinates ($g_{ij}=-1$), and nonpositive thresholds. For $t>0$ both inequalities are strict whenever $G\ne\Delta_n$. For $n\ge3$, equality at a nonpositive threshold does *not* identify the simplex: $F_{\Delta_n}(t)=0$ for $t\le0$, and [a formal counterexample](checks/wp21/Adverse.lean) shows that $G=vv^\top$ with $v=(1,-1,1)$ also has $F_G(t)=0$ for every $t\le0$. Every comparison uses the *same* threshold $t$ for all coordinates.

## Relation to the paper

The paper's Appendix D states that the formal statements are exactly its equations (1.4) and (1.5). Theorem, equation, and section numbers here are those of the first arXiv version.

### What is certified

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1, (1.4): $F_G(t)\ge D_n(t)$ for every integer $n\ge2$, every $G\in\mathcal{E}_n$, and every $t\in\mathbb{R}$ | `FSC.cdf_simplex_le` |
| Theorem 1.1, (1.5): for each fixed $t>0$, $F_G(t)=D_n(t)$ if and only if $G=\Delta_n$ | `FSC.cdf_eq_simplex_iff` |
| $M_G\le_{\mathrm{st}}M_{\Delta_n}$, stated after Theorem 1.1 | `FSC.coordinateMax_tail_le_simplex` (in upper-tail form) |

The remaining declarations in the [table below](#using-the-library) (the strict inequality, the comparison of Gaussian measures, and the strict and equality forms for the maximum) follow from these and are certified in the same way. The paper's objects correspond to the Lean ones as follows:

| Paper | Lean | Meaning in Lean |
| --- | --- | --- |
| $G\in\mathcal{E}_n$ | `G : FSC.Mat n` with `WeakSimplex.IsCorrelation G` | `G.PosSemidef ∧ ∀ i, G i i = 1`, where mathlib's `Matrix.PosSemidef` includes symmetry |
| $F_G(t)$ | `FSC.cdf G t` | the probability that mathlib's centered Gaussian `multivariateGaussian 0 G` gives the lower orthant `WeakSimplex.lowerOrthant t` (the points whose coordinates are all at most `t`), as a real number; `FSC.cdf_eq_measure` states `ENNReal.ofReal (FSC.cdf G t) = multivariateGaussian 0 G (WeakSimplex.lowerOrthant t)` |
| $\Delta_n=(nI-J)/(n-1)$ | `FSC.simplex n` | entries `1` on the diagonal and `-1 / ((n : ℝ) - 1)` off it, with real subtraction (`FSC.simplex_apply`; `FSC.simplex_eq_scaled_matrix` gives the matrix form) |
| $D_n(t)$ | `FSC.cdf (FSC.simplex n) t` | as for $F_G(t)$ |
| $M_G=\max_i X^G_i$ | `WeakSimplex.coordinateMax` | the largest coordinate |

Lean's kernel checks the proofs of all these declarations. The proofs use no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`, the standard axioms of Lean and mathlib. In particular, there is no `sorry` and no axiom added by this project. So the result rests on Lean's kernel, these three axioms, and the definitions that the statements unfold to: those in [Definitions.lean](FSC/Definitions.lean), in the WSC formalization, and in mathlib at the pinned revisions. The main theorems have no hypotheses beyond those displayed above: every analytic fact the proof needs is proved here or in these dependencies.

The proofs were certified at commit `1915b3485c8d61e531374261e7844010b7538eb9`. No later commit changes a Lean source or build pin: `git diff --stat 1915b34 HEAD -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain` prints nothing. Later commits change only documentation, license texts, citation metadata, the CI configuration, verification evidence, and the verification suite. At acceptance, a [SHA-256 comparison](checks/release/source-equivalence.json) of the Lean sources, the pins, and the axiom checker recorded the same fact.

### What is not certified

- **That the statements mean what the paper says.** Lean checks the formal statements, not their reading. Their agreement with Theorem 1.1 rests on the dictionary above, which you can check against [Definitions.lean](FSC/Definitions.lean), and on the [independent statement review](docs/work-packages/WP25-statement-review.md). The review's [check file](checks/release/IndependentStatements.lean) restates the theorems with the Gaussian measures and hypotheses written out.
- **The rest of the paper.** The certified contract is Theorem 1.1 and its maximum-tail form. The other results of the paper are proved only in the paper, for example Corollary 1.2 and Appendix A (the circumscribed-simplex form of the theorem and its equivalence with (1.4)), the applications in Section 6, and Appendices B and C.
- **The proof written in the paper.** The kernel checks the formal proof, not the paper's. The formal proof was completed on September 8, 2026, from an earlier manuscript (preserved in [docs/](docs/README.md)), before the paper reached its posted form. It shares the paper's strategy: induction on $n$, a matrix minimizing $G\mapsto F_G(t)$ over the compact set $\mathcal{E}_n$, and the derivative of $F_G(t)$ along added Gaussian noise (the paper's Proposition 4.1). However, it does not follow the paper step by step. For example, at a minimizer it uses this derivative only in finitely many directions, whereas the paper proves the full first-order conditions of its Proposition 4.2. The paper's proofs do not rely on the formalization (as the paper's AI disclosure states), and the kernel check does not rely on the paper's text. The two proofs are not independent in origin, though: both descend from the proof obtained on September 7, 2026 (the paper's Appendix D), and the paper's proof of Proposition 4.1, by averaging over the added noise, was found for the formalization.

## Using the library

The public import is `FSC`. These examples use the actual signatures of the main theorems:

```lean
import FSC

example {n : ℕ} (hn : 2 ≤ n) (G : FSC.Mat n)
    (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    FSC.cdf (FSC.simplex n) t ≤ FSC.cdf G t :=
  FSC.cdf_simplex_le hn G hG t

example {n : ℕ} (hn : 2 ≤ n) (G : FSC.Mat n)
    (hG : WeakSimplex.IsCorrelation G) (t : ℝ) (ht : 0 < t) :
    FSC.cdf G t = FSC.cdf (FSC.simplex n) t ↔ G = FSC.simplex n :=
  FSC.cdf_eq_simplex_iff hn G hG t ht
```

The [dictionary above](#what-is-certified) gives the meaning of `WeakSimplex.IsCorrelation`, `FSC.cdf`, and `FSC.simplex`.

| Result | Declaration in namespace `FSC` | Source |
| --- | --- | --- |
| The comparison for every correlation matrix and every threshold | `cdf_simplex_le` | [Comparison.lean](FSC/Comparison.lean) |
| Equality at a fixed $t>0$ exactly when $G=\Delta_n$ | `cdf_eq_simplex_iff` | [Equality.lean](FSC/Equality.lean) |
| Strict inequality at $t>0$ when $G\ne\Delta_n$ | `cdf_simplex_lt` | [Equality.lean](FSC/Equality.lean) |
| The comparison for the Gaussian measures of the lower orthant | `lowerOrthant_simplex_le` | [Main.lean](FSC/Main.lean) |
| The upper tail of the maximum: comparison, strictness, and equality | `coordinateMax_tail_le_simplex`, `coordinateMax_tail_lt_simplex`, `coordinateMax_tail_eq_simplex_iff` | [Main.lean](FSC/Main.lean) |

[PUBLIC_CONTRACT.md](docs/PUBLIC_CONTRACT.md) states the exact contract the formalization was built to meet.

## Building and checking

Install Lean through [elan](https://lean-lang.org/install/), then run:

```bash
git clone https://github.com/abhmul/full-simplex-conjecture-lean.git
cd full-simplex-conjecture-lean
lake exe cache get
lake build FSC FSCProbes --wfail
```

The cache download is optional; it fetches compiled mathlib files. The repository pins Lean **4.31.0**, mathlib, the [WSC formalization](https://github.com/abhmul/weak-simplex-conjecture-lean), and every transitive Lake dependency. Keep the committed manifest.

With Python 3.10 or newer, run the complete verification suite from a checkout whose dependencies have been fetched:

```bash
python3 scripts/verify_release.py --evidence "$(mktemp -d)/evidence"
```

The suite first checks the Lean version and the dependency pins, and it scans the Lean sources for `sorry`, `admit`, `native_decide`, and `axiom`. It builds `FSC` and `FSCProbes` with warnings treated as errors and compiles the top-level file `FSC.lean` separately. It then checks the axioms used by every required declaration, by the restated theorems, and by the regression tests. It also confirms that the axiom checker accepts a valid report and rejects invalid ones. Finally, it checks that the sources and pins did not change during the run. It needs no third-party Python packages.

The [verification report](docs/RELEASE_AUDIT.md) records 282 axiom checks and a complete rebuild of the pinned sources from scratch, with no cached build products. Continuous integration reruns the verification suite on every push to `main` and on every pull request; the rebuild from scratch was done at the certified commit. [BUILDING.md](docs/BUILDING.md) gives the prerequisites, incremental checks, and instructions for repeating the rebuild from scratch.

## Navigating the repository

[ARCHITECTURE.md](docs/ARCHITECTURE.md) describes the route of the formal proof and its Lean interfaces.

| Location | Contents |
| --- | --- |
| [FSC/](FSC/) | The formalization. The main theorems are in `Comparison.lean`, `Equality.lean`, and `Main.lean`. The subdirectories include Gaussian laws, conditioning on coordinates, and the derivative along added noise (`Gaussian/`); Gaussian measures of polyhedra as functions of their offsets (`Support/`); calculus and averaging over noise (`Analysis/`); minimizers (`Minimizers/`); the scalar inequalities used at a minimizer (`Scalar/`); the simplex recurrence (`Simplex/`); and the final argument over thresholds (`Threshold/`). |
| [FSCProbes/](FSCProbes/) | Regression tests of internal interfaces on concrete singular and degenerate matrices |
| [checks/](checks/README.md) | Statement and axiom checks, regression tests, and the recorded verification evidence |
| [docs/](docs/README.md) | The architecture of the formal proof, source provenance, the verification report, and the development history |
| [scripts/](scripts/) | The verification suite, the axiom checker, and the rebuild from scratch |

The manuscript and review notes under `docs/` are the inputs the formalization was built from, **not the paper**. Historical experiments and failed checks are kept as they were recorded.

## Citation and contributions

If you use this formalization, please cite the paper. If you rely on the formal proof itself, please also cite this repository and the commit you used. [CITATION.cff](CITATION.cff) contains both citations.

```bibtex
@misc{mulgund2026regular,
  title         = {Stochastic Domination of Gaussian Maxima by the Regular Simplex},
  author        = {Abhijeet Mulgund},
  year          = {2026},
  eprint        = {2609.28452},
  archivePrefix = {arXiv},
  primaryClass  = {math.PR},
  doi           = {10.48550/arXiv.2609.28452},
  url           = {https://arxiv.org/abs/2609.28452}
}
```

Corrections, reproducibility reports, and improvements are welcome through [GitHub issues](https://github.com/abhmul/full-simplex-conjecture-lean/issues) and pull requests. [CONTRIBUTING.md](CONTRIBUTING.md) states the theorem contract and the checks a change must pass.

## Provenance and licensing

The formalization uses mathlib and the pinned WSC formalization, including the StatLean components that WSC credits. Two short pieces are adapted, one from WSC and one from mathlib, and keep their upstream notices. [PROVENANCE.md](PROVENANCE.md) records their sources and licenses.

No license has yet been chosen for the new material in this repository. Third-party material keeps its upstream license.
