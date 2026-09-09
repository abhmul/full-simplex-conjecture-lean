# Full Simplex Conjecture in Lean

[![Lean CI](https://github.com/abhmul/full-simplex-conjecture-lean/actions/workflows/lean_action_ci.yml/badge.svg?branch=main)](https://github.com/abhmul/full-simplex-conjecture-lean/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of the full simplex comparison for Gaussian maxima, including strictness and the characterization of equality at each positive threshold.

The formalization is complete and has passed the [documented verification gates](docs/RELEASE_AUDIT.md). The accompanying preprint by Abhijeet Mulgund is **in preparation**.

## Main theorem

Let $n \ge 2$, let $G$ be any real $n \times n$ positive-semidefinite matrix with diagonal entries equal to one, and define

$$
\Delta_n = \frac{nI-J}{n-1},
\qquad
F_G(t) = \mathbb{P}_{X \sim \mathcal{N}(0,G)}
  [X_i \le t \text{ for every } i],
$$

where $J$ is the all-ones matrix. Then, for every real threshold $t$,

$$
F_{\Delta_n}(t) \le F_G(t).
$$

At **any fixed positive threshold** $t > 0$,

$$
F_G(t) = F_{\Delta_n}(t)
\quad\Longleftrightarrow\quad
G = \Delta_n.
$$

Equivalently, the regular simplex maximizes the upper tail of the coordinate maximum:

$$
\mathbb{P}_{X \sim \mathcal{N}(0,G)}[\max_i X_i > t]
\le
\mathbb{P}_{Y \sim \mathcal{N}(0,\Delta_n)}[\max_i Y_i > t].
$$

The comparison includes singular matrices, repeated coordinates, antipodal coordinates, and nonpositive thresholds. For $t>0$, both comparisons are strict whenever $G \ne \Delta_n$. Equality at a nonpositive threshold does not characterize the simplex; [a formal counterexample](checks/wp21/Adverse.lean) records this boundary. All comparisons use a common scalar threshold.

## Using the library

The public import is `FSC`. These examples use the actual public theorem signatures:

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

`WeakSimplex.IsCorrelation` means positive semidefinite with unit diagonal. [`FSC.cdf`](FSC/Definitions.lean) is the real-valued probability of the actual Gaussian lower-orthant event; `cdf_eq_measure` proves its measure-valued bridge.

| Result | Declaration in namespace `FSC` | Source |
| --- | --- | --- |
| All-correlation, all-threshold comparison | `cdf_simplex_le` | [Comparison.lean](FSC/Comparison.lean) |
| Equality at a positive threshold iff simplex | `cdf_eq_simplex_iff` | [Equality.lean](FSC/Equality.lean) |
| Strict comparison away from the simplex | `cdf_simplex_lt` | [Equality.lean](FSC/Equality.lean) |
| Comparison of Gaussian event measures | `lowerOrthant_simplex_le` | [Main.lean](FSC/Main.lean) |
| Maximum-tail comparison, strictness, and equality | `coordinateMax_tail_le_simplex`, `coordinateMax_tail_lt_simplex`, `coordinateMax_tail_eq_simplex_iff` | [Main.lean](FSC/Main.lean) |

See the [exact public contract](docs/PUBLIC_CONTRACT.md) and [independent expanded-statement consumers](checks/release/IndependentStatements.lean).

## Building and checking

Install Lean through [elan](https://lean-lang.org/install/), then run:

```bash
git clone https://github.com/abhmul/full-simplex-conjecture-lean.git
cd full-simplex-conjecture-lean
lake exe cache get
lake build FSC FSCProbes --wfail
```

The cache download is optional. The repository pins Lean **4.31.0**, mathlib, the [WSC foundations](https://github.com/abhmul/weak-simplex-conjecture-lean), and all transitive Lake dependencies. Keep the committed manifest.

With Python 3.10 or newer, run the complete verification suite from a checkout whose dependencies have been fetched:

```bash
python3 scripts/verify_release.py --evidence "$(mktemp -d)/evidence"
```

This checks the full build, the public root separately, required transitive axiom reports, expanded statements, regression cases, and the audit parser's acceptance and rejection controls. It requires no third-party Python packages.

The permitted axiom closure is any subset of `propext`, `Classical.choice`, and `Quot.sound`. The final theorems discharge all project-specific analytic inputs. The [acceptance report](docs/RELEASE_AUDIT.md) records 282 mathematical axiom reports and a successful artifact-free reconstruction of the pinned sources. CI reruns the maintained verification suite; historical source-reconstruction evidence identifies its exact certified revision.

See [BUILDING.md](docs/BUILDING.md) for prerequisites, incremental checks, and reproduction from source without compiled artifacts.

## Navigating the proof

The proof uses Gaussian pinning and support differentiation to obtain a right derivative under normalized positive-semidefinite covariance addition. Gaussian energy identities and a scalar comparison constrain minimizers; a compact threshold barrier proves comparison, followed by equality.

| Location | Contents |
| --- | --- |
| [FSC/](FSC/) | Production formalization, including Gaussian laws, support calculus, energy, scalar comparison, and minimizer arguments |
| [FSCProbes/](FSCProbes/) | Compiled API consumers and singular or degenerate regression configurations |
| [checks/](checks/README.md) | Statement and axiom audits, regression tests, and retained verification evidence |
| [docs/](docs/README.md) | Proof architecture, source provenance, acceptance reports, and development history |
| [scripts/](scripts/) | Build, axiom-audit, and clean-reconstruction tools |

The teaching manuscript and review notes under `docs/` are preserved implementation inputs, **not the forthcoming preprint**. Historical experiments and failed checks are retained with their original scope.

## Citation and contributions

Until the preprint is available, cite this repository and the commit used. [CITATION.cff](CITATION.cff) provides software citation metadata.

Corrections, reproducibility reports, and improvements are welcome through [GitHub issues](https://github.com/abhmul/full-simplex-conjecture-lean/issues) and pull requests. See [CONTRIBUTING.md](CONTRIBUTING.md) for the theorem contract and verification requirements.

## Provenance and licensing

This development uses mathlib and the pinned WSC public foundations, including their attributed StatLean components. Two narrowly adapted proof slices retain their upstream notices. [PROVENANCE.md](PROVENANCE.md) records their sources and license scope.

A license for newly authored FSC material has not yet been selected. Existing third-party material retains its stated upstream license.
