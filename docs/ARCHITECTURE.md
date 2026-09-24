# Architecture of the formal proof

The formal proof of Theorem 1.1 follows the strategy of the paper [arXiv:2609.28452](https://arxiv.org/abs/2609.28452): induction on $n$, a correlation matrix minimizing $G\mapsto F_G(t)$ over the compact set $\mathcal E_n$, and the one-sided derivative along added Gaussian noise (the paper's Proposition 4.1). At a minimizer, however, the paper proves $S\succeq0$ and $SG=0$ (Proposition 4.2), while the formal proof tests only finitely many covariance directions. Theorem, equation, and section numbers are those of the paper's first arXiv version.

This architecture governed the implementation. It was reviewed on 2026-09-08. Where it differed from the wording of the raw consultation notes in [pro-return/](pro-return/), it took precedence. The source manuscript in [sources/](sources/README.md) remains an independent proof and the fallback route, and no source is silently rewritten. The last three sections state rules that were written for the implementers.

## Notation and terms

Let $G$ be a correlation matrix, let $X\sim\mathcal N(0,G)$, and put

$$
f_G(x)=\mathbb P[X_i\le x_i\text{ for every }i]\qquad(x\in\mathbb R^n),
$$

so that $F_G(t)=f_G(t\mathbf 1)$. Fix $t>0$ and suppose that no two coordinates coincide ($g_{ij}<1$ for $i\ne j$, the paper's (3.1)). The conditional masses of the paper's (1.9) and the pair weights of its (3.6) are

$$
H_i=\mathbb P[X_j\le t\ (j\ne i)\mid X_i=t],
\qquad
q_{ij}=\varphi_2(t,t;g_{ij})\,\mathbb P[X_\ell\le t\ (\ell\ne i,j)\mid X_i=X_j=t]
\quad(-1 < g_{ij}<1),
$$

where $\varphi_2(\cdot,\cdot;c)$ is the standard bivariate Gaussian density with correlation $c$. We set $q_{ij}=0$ if $g_{ij}=-1$, and $q_{ii}=0$. The paper's matrix of pair weights (4.2) is

$$
S_{ij}=q_{ij}\ (i\ne j),\qquad S_{ii}=-\sum_{j\ne i}g_{ij}q_{ij}.
$$

The source manuscript calls $S$ a stress matrix, and Lean defines it as `FSC.stress`. The row quantities are those of the paper's (4.4),

$$
k_i=\sum_{j\ne i}(1-g_{ij})q_{ij}=(S\mathbf 1)_i,
\qquad
C_i=\sum_{j\ne i}\sqrt{1-g_{ij}^2}\,q_{ij},
\qquad
\kappa=\sum_ik_i,
$$

defined in Lean as `FSC.rowK`, `FSC.rowC`, and `FSC.kappa`. The pair weight $q_{ij}$ is `FSC.q`.

As in the source manuscript, which borrows the term from convex geometry, the offset $b_j$ of an inequality $\langle w_j,y\rangle\le b_j$ is called its support number. Lean names such as `FSC.supportGradient` use "support" in this sense. For each $i$, the paper's (3.3) defines a polyhedral region $Q_i(b)$ with unit normals $w_{ij}$ and support numbers $b=(b_j)_j$, and $h_i(b)$ denotes its standard Gaussian mass. At the actual support numbers

$$
\beta_{ij}=\frac{t(1-g_{ij})}{\sqrt{1-g_{ij}^2}}\qquad(-1 < g_{ij}<1),
$$

the region describes the event that $X_j\le t$ for every $j\ne i$, given $X_i=t$, so $H_i=h_i(\beta_i)$. The proof also evaluates $h_i$ at the equal support numbers $\rho_n(t)\mathbf 1$, where $\rho_n(t)=t\sqrt{n/(n-2)}$.

## The formal route

The formal proof combines five parts.

1. Finitely many selected covariance directions $L$ at a minimizer, in place of the paper's conclusions $S\succeq0$ and $SG=0$ (see [Tests at a minimizer](#tests-at-a-minimizer) and [FSC/Minimizers/](../FSC/Minimizers/)).
2. A quadratic comparison at the actual support numbers: the reciprocal tangent inequality (5.2) between $\beta_i$ and $\rho_n(t)\mathbf 1$ ([QuadraticTangent.lean](../FSC/Support/QuadraticTangent.lean)).
3. Padded Gaussian energy: the second moment $\int_{Q_i}|y|^2\,d\gamma_{n-2}(y)$ in the dilation identity (5.3), computed in dimension $n-2$ after padding by unused Gaussian directions, where $\gamma_{n-2}$ is the standard Gaussian measure on $\mathbb R^{n-2}$ ([Dilation.lean](../FSC/Support/Dilation.lean) and [Compatibility.lean](../FSC/Facet/Compatibility.lean)).
4. The componentwise scalar theorem, the paper's Lemma 5.2 ([Componentwise.lean](../FSC/Scalar/Componentwise.lean)).
5. A compact strict linear barrier, the tilted minimization in the paper's proof of Theorem 1.1 from Proposition 2.2 ([LinearBarrier.lean](../FSC/Threshold/LinearBarrier.lean)).

### The derivative along the noise path

The support/noise variant supplies exactly the one-sided derivative that the proof needs. Its name records its two ingredients: derivatives in the support numbers, and averaging over added noise. For $L\succeq0$ and $s\ge0$, the noise path of the paper's (4.1) stays in $\mathcal E_n$, and

$$
G_s=R_s(G+sL)R_s,\quad L\succeq0,\qquad
\partial_{s+}F_{G_s}(t)\big|_{s=0}=\tfrac12\operatorname{tr}(S_GL).
$$

Here $R_s=\operatorname{diag}\bigl((1+sL_{ii})^{-1/2}\bigr)$, as in the paper, and $S_G$ is the matrix $S$ at $G$. The formula holds for every correlation matrix $G$ with $g_{ij}<1$ for $i\ne j$, every $L\succeq0$, and every $t>0$ (`FSC.hasDerivWithinAt_normalizedAdd` in [ThresholdExpansion.lean](../FSC/Gaussian/ThresholdExpansion.lean)).

Conditioning on the noise $Y\sim\mathcal N(0,L)$ moves the threshold vector instead of the covariance:

$$
F_{G_s}(t)=\mathbb E\,f_G\bigl(t\mathbf 1+v(s)-\sqrt s\,Y\bigr),
\qquad
v_i(s)=t\bigl(\sqrt{1+sL_{ii}}-1\bigr).
$$

So the formula follows from a local second-order expansion of $f_G$ in the threshold vector at $t\mathbf 1$, at the fixed covariance $G$ (`FSC.peano2_thresholdCDF`), and from averaging bounded functions over independent centered noise with finite second moment ([NoiseAveraging.lean](../FSC/Analysis/NoiseAveraging.lean)). These give

$$
\frac{d}{ds}F_{G_s}(t)\Big|_{s=0^+}
=\frac12\Bigl[\sum_i tL_{ii}\varphi(t)H_i+\sum_{i,j}L_{ij}\,\partial_{ij}f_G(t\mathbf 1)\Bigr].
$$

The first sum comes from the normalization drift $v(s)$. It cancels the contribution of the terms $-t\varphi(t)H_i$ in the diagonal entries of the threshold Hessian,

$$
\partial_{ii}f_G(t\mathbf 1)=-t\varphi(t)H_i-\sum_{j\ne i}g_{ij}q_{ij},
$$

and the remaining terms, with $\partial_{ij}f_G(t\mathbf 1)=q_{ij}$ for $i\ne j$, add up to $\tfrac12\operatorname{tr}(S_GL)$. The paper proves Proposition 4.1 by the same conditioning on the noise. [SUPPORT_NOISE_VARIATION.md](pro-return/SUPPORT_NOISE_VARIATION.md) gives the full derivation, and [MATHEMATICAL_REVIEW.md](MATHEMATICAL_REVIEW.md) records its reviewed audit.

### What the variant replaces

This route replaces four ingredients of the derivative argument in the source manuscript:

- differentiation of the Gaussian density in a positive-definite covariance;
- continuity of the pair weights in the covariance;
- the regularization estimates at antipodal pairs;
- the integrated passage to the relative differential, the expansion $F_{\widehat G}(t)-F_G(t)=\sum_{i < j}q_{ij}(\widehat g_{ij}-g_{ij})+o(\lVert\widehat G-G\rVert)$ as $\widehat G\to G$ within $\mathcal E_n$ (the manuscript's (4.6)).

It does not remove:

- canonical regression, the explicit one- and two-coordinate conditional laws of [Conditional laws](#conditional-laws);
- support $C^1$ neighborhoods: by the paper's Lemma 3.1, the Gaussian mass of a polyhedral region is $C^1$ in its support numbers on a whole neighborhood, not only differentiable at one point;
- exact weight compatibility, the identities (3.9) and (5.1), which express the support-number derivatives of $h_i$ at $\beta_i$ through the same $q_{ij}$;
- unbounded dilation, the dilation identity (5.3) for regions $Q_i$ that may be unbounded;
- all-correlation CDF continuity, the joint continuity of $(G,t)\mapsto F_G(t)$ on all correlation matrices, including singular ones and those with repeated coordinates.

It does not prove a covariance Hessian (a second derivative of $G\mapsto F_G(t)$), and it does not reverse Gaussian smoothing.

## Interface rules (2026-09-08)

The implementation had to respect the following rules at the interfaces between parts of the proof.

### Conditional laws

Pinning coordinate $i$ at a value $r$ means conditioning on $X_i=r$, and a pair pin conditions on $X_i=r$ and $X_j=s$. These events have probability zero, so the formal proof defines each conditional law explicitly by Gaussian regression, for every real pin value. This is the canonical regression. The single-pin law is

$$
\mathcal N\bigl(r\,G_{\cdot i},\;G-G_{\cdot i}G_{\cdot i}^\top\bigr),
$$

where $G_{\cdot i}$ is the $i$th column of $G$ (`FSC.singleLaw`). The pair law (`FSC.pairLaw`) is a Gaussian law whose covariance $PGP^\top$ is that of the residual $PX$, for an explicit linear map $P$. Both laws live on all $n$ original coordinates (full-index residuals), and the pinned coordinates are deterministic under them. The remaining-coordinate events (`FSC.singleEvent` and `FSC.pairEvent`) exclude the pinned coordinates.

A single integration owner fixed the pair residual law, the remaining-coordinate event, $q$, the stress matrix $S$, the row quantities, and the facet normalization together. [WP01](work-packages/WP01.md) records the frozen definitions. The full-index residual is a linear image of $X$, so its covariance is positive semidefinite, including when it has rank zero. No version of a conditional distribution is chosen at a null pin: a regular conditional distribution is determined only for almost every pin value, so it cannot be evaluated at the fixed value $t$.

### Two Gram realizations

A Gram realization of $G$ is a list of unit vectors $v_1,\dots,v_n$ with $\langle v_i,v_j\rangle=g_{ij}$. Then $X_i=\langle v_i,Z\rangle$ for a standard Gaussian vector $Z$, and $X\le t\mathbf 1$ exactly when $Z$ lies in the polyhedron $K_t$ of points $y$ with $\langle v_i,y\rangle\le t$ for every $i$.

The proof keeps two realizations separate. The ordinary realization lies in $\mathbb R^n$, is built from the square root $G^{1/2}$ (`FSC.gramVectors`), and exists for every correlation matrix. The threshold calculus of the paper's Section 3 can use it. The padded realization lies in $\mathbb R^{n-1}$ and exists when $G$ is singular (`FSC.exists_padded_unit_gram`). When $\operatorname{rank}G < n-1$, the unused directions of $\mathbb R^{n-1}$ are the padding of the paper's Section 5.1. In the padded realization, each space $v_i^\perp$ has dimension $n-2$.

Following the source manuscript, facet $i$ is the part of $K_t$ in the hyperplane $\langle v_i,y\rangle=t$. Translated by $-tv_i$, it is the conditional region $Q_i(\beta_i)$ in $v_i^\perp$. The facet construction builds these regions in the padded realization (`FSC.paddedFacetNormal`), so it needs $G$ to be singular.

The paper's Lemma 3.3 (for each $i$, every index $j\ne i$ maximizing $g_{ij}$ has $-1 < g_{ij}<1$ and $q_{ij}>0$) must be proved without assuming that $G$ is singular (`FSC.q_pos_of_row_max`). It must precede the exclusion of positive-definite minimizers, which uses $\kappa>0$, so it cannot depend on the facet construction. The dependency graph in [WORK_PACKAGES.md](WORK_PACKAGES.md) enforces this order.

### Boundary hyperplanes

At a common threshold $t>0$, with distinct unit normals ($g_{ij}<1$ for $i\ne j$), no two of the original boundary hyperplanes $\langle v_i,y\rangle=t$ coincide. After a single pin, no two of the projected hyperplanes $\langle w_{ij},y\rangle=\beta_{ij}$ coincide either. So the proof applies the support $C^1$ lemma for finitely many unit normals and a standard Gaussian (the paper's Lemma 3.1) twice: once to the original normals and once to the projected ones. The lemma allows redundant inequalities and nonsimple intersections, and it excludes only coincident hyperplanes.

An antipodal constraint is automatic near the pin. If $g_{ij}=-1$, then given $X_i=x_i$ the constraint $X_j\le x_j$ reads $-x_i\le x_j$, which holds strictly for $x$ near $t\mathbf 1$. Such a constraint is omitted from the pinned region $Q_i$, but it is not removed from the original event.

### Pair weights and conditional regions

The same $q_{ij}$ must occur in the covariance derivative, in the support-number derivatives $\partial_jh_i(\beta_i)=\sqrt{1-g_{ij}^2}\,q_{ij}/\varphi(t)$ of the paper's (3.9), and in the split $H_i=u_i+e_i$ of (5.4), which comes from the dilation identity (5.3).

The proof compares $H_i$ with $h_i(\rho_n(t)\mathbf 1)$, the equal-support reference. At equal support numbers two projected hyperplanes may coincide, so $h_i$ is differentiated only at the actual support numbers $\beta_i$. The tangent inequality (5.2),

$$
\frac{h(b)^2}{h(c)}-h(b)\ge\nabla h(b)\cdot(b-c),
$$

for support numbers $b$ and $c$ with positive entries, assumes that no two hyperplanes coincide at $b$ and makes no such assumption at $c$ (`FSC.quadratic_support_tangent`).

The induction hypothesis bounds the equal-support reference below by $D_{n-1}(\rho_n(t))$. To apply it, the at most $n-1$ constraints of $Q_i$ are filled out to exactly $n-1$ by repeating existing inequalities, not by adding independent coordinates (the paper's Section 5.5, and `FSC.reference_floor_of_comparison` in Lean).

The energy $\int_{Q_i}|y|^2\,d\gamma_{n-2}(y)$ (`FSC.capEnergy`) is computed in dimension $n-2$, including the unused Gaussian directions. Each unused direction adds $H_i$ to it (the paper's footnote 2).

### Tests at a minimizer

Fix $n\ge3$, $t>0$, and a correlation matrix $G$ minimizing $\Gamma\mapsto F_\Gamma(t)$ over $\mathcal E_n$. The paper's Proposition 5.1 assumes only three consequences of minimality: distinct coordinates, $\operatorname{rank}G\le n-1$, and $\eta_i=S_{ii}-k_i^2/\kappa\ge0$ (the paper's (4.5)). Distinct coordinates follow, as in the paper, by replacing a repeated coordinate with an independent one (`FSC.distinctScores_of_cdf_minimum`). The other two follow from the one-sided derivative in finitely many directions $L$, each of which is nonnegative by minimality.

Positive-definite minimizers are excluded with $L=G-\delta J$. If $G$ were positive definite, then $G-\delta J\succeq0$ for some $\delta>0$. Since $\operatorname{tr}(SG)=0$ and $\operatorname{tr}(SJ)=\mathbf 1^\top S\mathbf 1=\kappa>0$, the derivative in this direction would be

$$
\tfrac12\operatorname{tr}\bigl(S(G-\delta J)\bigr)=-\tfrac12\delta\kappa<0,
$$

contradicting minimality (`FSC.not_posDef_of_cdf_minimum`).

The remaining finite tests use $L=z_iz_i^\top$ with $z_i=e_i-(k_i/\kappa)\mathbf 1$, where $e_i$ is the $i$th coordinate vector. The weight $k_i/\kappa$ is frozen at the base matrix $G$: it is computed at $G$ and held fixed along the path $G_s$. Since $\operatorname{tr}(Sz_iz_i^\top)=z_i^\top Sz_i=S_{ii}-k_i^2/\kappa$, minimality gives $\eta_i\ge0$ (`FSC.finite_row_test_bound`). These tests need neither a full positive-semidefinite stress theorem ($S\succeq0$) nor $GS=0$.

### Scalar theorem and barrier

The scalar theorem (the paper's Lemma 5.2, formalized as `FSC.componentwise_compare` and `FSC.componentwise_equality`) keeps its hypothesis that every component $u_i$ and $e_i$ is strictly positive.

The comparison uses the paper's linear tilt. If $F_{G_0}(t_0) < D_n(t_0)$, then for a suitable $\varepsilon>0$ the function $\Psi(G,t)=F_G(t)-D_n(t)+\varepsilon t$ has a negative minimum over a compact set. At a minimizing point $(G_*,t_*)$, the derivative bound $F_{G_*}'(t_*)\ge D_n'(t_*)$ contradicts $\partial_t\Psi(G_*,t_*)=0$. The paper minimizes over $\mathcal E_n\times[t_1,t_2]$ with $t_1>0$. The compact barrier of the formal proof uses $\mathcal E_n\times[0,T]$, with $D(0)=0$ for $D=D_n$. Thus $\Psi(G,0)=F_G(0)\ge0$, and the negative minimum is not attained at $t=0$ (`FSC.compact_slope_comparison`). Comparison precedes equality: the equality theorem `FSC.cdf_eq_simplex_iff` is proved from the comparison `FSC.cdf_simplex_le`.

## Early evidence and the fallback route (rules of 2026-09-08)

The rules asked for early evidence. Compiler and API checks, and the derivative integration for the singular triangle, were to start early, alongside an independent branch for the scalar theorem, the noise averaging, and the barrier. The singular triangle is a rank-two $3\times3$ correlation matrix given in [PROBES.md](pro-return/PROBES.md). Passing rational identities alone does not discharge the analytic interface. The triangle test had to exercise the actual Gaussian law, redundant support numbers on an unbounded region, a deterministic pair residual (with covariance zero), and a derivative along a path whose rank increases. The universal interface was to be proved after it.

If a precise statement or representation failed, the rule was to keep the counterexample or a minimal reproducer and to investigate the smallest repair. The fallback is the original regularized Plackett argument in Chapter 4 of the [teaching manuscript](sources/TEACHING_MANUSCRIPT.md): the density calculation for positive-definite covariances (its Section 4.1), extended to singular covariances by regularization (its Section 4.4). Two full analytic derivative arguments were not to be developed preemptively. A namespace mismatch or an ordinary type-cast problem is not an architectural obstruction.

The choice between the reciprocal $1/h$ and $\log h$ in proving the tangent inequality (5.2) is internal to that interface: the other parts of the proof use only the inequality. The geometric route of the teaching manuscript (its Chapters 10 and 11: positive-semidefinite stress, a logarithmic comparison that keeps entropy losses, and the minimum-envelope ending) is an explanatory companion, not another required formalization project.

## Execution rules (2026-09-08)

The work was divided into packages, all 28 of which are now integrated. [WORK_PACKAGES.md](WORK_PACKAGES.md) lists them with their dependency graph, and [work-packages/](work-packages/) holds a card for each. An implementer was to read WORK_PACKAGES.md and claim a ready card. Task boundaries were to follow the mathematical interfaces and could be refined when actual compiler evidence warranted it. Proposed declaration names are not automatically real APIs. The graph and the file ownership were to be preserved as they evolved.

The stage labels are `planned`, `interface-frozen`, `in-progress`, `kernel-checked-local`, `reviewed`, `integrated`, and `blocked`. Infrastructure and spike (exploratory probe) packages have explicit deliverables that are not theorems. A conditional assembly (a theorem that takes an unproved analytic input as an explicit hypothesis) remains labeled conditional and outside the release root `FSC.lean`. Before acceptance, a package card had to record the exact theorem type, the imports, the commands, the axiom result, and the remaining consumers.

The lead could use read-only critics and workers on disjoint files. No fixed staffing or duration was prescribed. The [public contract](PUBLIC_CONTRACT.md) and the trust policy do not change merely because a proof is inconvenient. The old WSC checkout and the separate research repository were to be left untouched.
