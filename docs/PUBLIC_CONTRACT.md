# Certification contract

This is the contract the formalization was built to meet. It is Theorem 1.1, equations (1.4) and (1.5), of the paper [arXiv:2609.28452](https://arxiv.org/abs/2609.28452). The [README](../README.md#relation-to-the-paper) relates the formal statements to the paper.

Status: the mathematical contract is preserved, and every public theorem and every final acceptance check has passed. The [verification report](RELEASE_AUDIT.md) records the evidence: the exact identity of the certified source, the independent statement review, and the rebuild from scratch.

For every integer $n\ge2$, every real positive-semidefinite correlation matrix $G$, and every real $t$, put

$$
\Delta_n=\frac{nI-J}{n-1},\qquad
F_G(t)=\Pr_{X\sim N(0,G)}(X_i\le t\text{ for every }i),
$$

where $J$ is the all-ones matrix. Certify

$$
F_{\Delta_n}(t)\le F_G(t).
$$

Separately, for every fixed $t>0$, certify

$$
F_G(t)=F_{\Delta_n}(t)\quad\Longleftrightarrow\quad G=\Delta_n.
$$

State the hypothesis on $G$ with the existing transparent predicate `WeakSimplex.IsCorrelation`, not with `IsWeakSimplexCov`, which also requires $G-J/n\succeq0$. A real-valued CDF in a public statement must come with a proof relating it to the Gaussian measure of the event. Prove that `WeakSimplex.regularSimplexGram` is the displayed $\Delta_n$ for $n\ge2$, and audit whether $n-1$ is natural-number or real subtraction. Also make public the strict inequality at positive thresholds and the corollary for the upper tail of the maximum coordinate, and check the direction of that tail inequality.

The comparison covers every rank of $G$, repeated coordinates ($g_{ij}=1$), antipodal coordinates ($g_{ij}=-1$), and nonpositive thresholds. The equality statement covers every correlation matrix at a positive threshold, with no genericity hypothesis. Certifying only one of the following does not meet the contract:

- the normalized Weak Simplex Conjecture (WSC) theorem;
- a comparison of moment generating functions;
- the statement for balanced matrices, for honest simplices, or for full-rank matrices;
- a statement conditional on an analytic certificate.

[pro-return/INTERFACES.md](pro-return/INTERFACES.md) proposes public names and schematic types. They are design inputs, not declarations that Lean has elaborated. The lead may settle syntax and representation as long as this mathematical contract is preserved exactly. Any substantive change requires review. Before acceptance, inspect the fully printed types independently, with every predicate alias unfolded.

The proofs may use any subset of the axioms `propext`, `Classical.choice`, and `Quot.sound`, and no other axiom. A proof of a different or conditional statement does not meet the contract, even if it uses only these axioms. The final source, the dependency revisions, the command exit codes, and a fresh axiom report must all identify the same revision.
