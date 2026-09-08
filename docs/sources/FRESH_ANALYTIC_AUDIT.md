# Audit of the all-dimensional Gaussian-maximum pressure/energy proof

**Review date:** September 7, 2026  
**Verdict:** Correct at the stated scope. The comparison and the fixed-positive-threshold equality theorem follow from the supplied argument. The reconstruction below supplies the analytic details at the singular-covariance and nonsimple-support interfaces. No additional Gaussian comparison theorem is needed.

This is an analytic proof review, not a formal verification. Exact algebra replays are recorded separately and are not evidence for the analytic lemmas.

## 1. Exact conclusions

Let
\[
\mathcal E_n=\{G\in\mathbb R^{n\times n}:G=G^T\succeq0,
\ \operatorname{diag}G=\mathbf1\},\qquad
\Delta_n=\frac{nI-J}{n-1}.
\]
For \(G\in\mathcal E_n\), write
\[
F_G(t)=\Pr_{X\sim N(0,G)}(X_i\le t\text{ for all }i),
\qquad D_n(t)=F_{\Delta_n}(t).
\]
The following two statements are proved separately below.

**Comparison theorem.** For every integer \(n\ge2\), every \(G\in\mathcal E_n\), and every real \(t\),
\[
F_G(t)\ge D_n(t).
\]

**Equality theorem.** For every integer \(n\ge2\) and every fixed finite \(t>0\),
\[
F_G(t)=D_n(t)\quad\Longleftrightarrow\quad G=\Delta_n.
\]
No balance assumption, rank restriction, tilt optimization, or restriction to simplicial intrinsic caps is imposed. No uniqueness statement is asserted at zero or at negative thresholds.

All caps below are finite intersections of closed halfspaces, hence Borel sets. The intrinsic Gaussian has a positive smooth density on its row span. Gaussian conditional distributions at a prescribed pair of scores mean the canonical Gaussian conditional law, defined by its conditional mean and covariance, rather than an arbitrary version on a null conditioning event.

## 2. Elementary consistency and adverse tests

For reference, at distinct coordinates and \(t>0\), the submitted coefficients and stress are
\[
q_{ij}=\phi_2(t,t;g_{ij})
 \Pr(X_\ell\le t\ (\ell\ne i,j)\mid X_i=X_j=t)
\quad(-1<g_{ij}<1),
\]
\[
q_{ij}=0\quad(g_{ij}=-1),\qquad
S_{ij}=q_{ij}\ (i\ne j),\qquad
S_{ii}=-\sum_{j\ne i}g_{ij}q_{ij}.
\]
The following tests are actual Gaussian configurations unless explicitly labeled scalar data.

### 2.1 Two sites, duplicates, and rank one

For two standard-normal marginals and \(t>0\), inclusion-exclusion gives
\[
F_G(t)=2\Phi(t)-1+
 \Pr(X_1>t,X_2>t)\ge2\Phi(t)-1.
\]
The antipodal pair \((Z,-Z)\) attains equality. For \(-1<g<1\), the bivariate density is positive on the open upper quadrant, so the intersection term is positive. For \(g=1\), it is \(1-\Phi(t)>0\). This verifies both the base comparison and its equality case.

If a coordinate is duplicated, keep one copy and replace another by
\(\cos\varepsilon\,X_i+\sin\varepsilon\,Z\), with \(Z\) independent standard normal. Conditional on every old successful sample, the added noisy constraint has a strictly positive failure probability. The new event is contained in the old event because a retained copy still enforces the original constraint. At positive thresholds the old event has positive probability. Thus this is a strict, arbitrarily small feasible descent.

A rank-one unit-row configuration has only the two possible rows \(v\) and \(-v\). For \(n\ge3\), it therefore has a duplicate and cannot be a full-elliptope local minimum. This disposes of zero-dimensional tangent bodies before the pressure/energy argument is used.

### 2.2 Antipodal normals and the square

Take normals \(e_1,e_2,-e_1,-e_2\). The cap is \([-t,t]^2\). Opposite pairs have \(q=0\); the four orthogonal adjacent pairs have the common coefficient
\(q=\phi(t)^2>0\). In cyclic order,
\[
S/q=
\begin{pmatrix}
0&1&0&1\\
1&0&1&0\\
0&1&0&1\\
1&0&1&0
\end{pmatrix}.
\]
Its spectrum is \(2,0,0,-2\). In particular,
\[
z=(1,-1,1,-1)^T,\qquad z^TSz=-8q<0.
\]
The full-elliptope lift supplies a descent. Thus this lower-rank, antipodal configuration is correctly excluded from the positive-stress class, rather than incorrectly excluded from the theorem's competitor class.

For the six normals \(\pm e_1,\pm e_2,\pm e_3\), the intrinsic cap is a cube. A nonopposite pair has coefficient
\[
q=\phi(t)^2[2\Phi(t)-1]>0.
\]
After division by this factor, the stress is the adjacency matrix of the complete tripartite graph with parts of size two. Its eigenvalues are
\(4,-2,-2,0,0,0\). This is the actual Gaussian interpretation of the corresponding supplied matrix replay; the interpretation does not follow from the matrix script alone.

### 2.3 Repeated projected directions, with no tied actual supports

Use the five distinct unit normals
\[
v_0=(1,0),\quad v_1=(0,1),\quad v_2=(3/5,4/5),
\quad v_3=(-1,0),\quad v_4=(0,-1).
\]
Pin \(v_0\cdot x=t\). In the tangent coordinate \(y\), the constraints become
\[
y\le t,\qquad y\le t/2,\qquad -y\le t,
\]
with the antipodal constraint automatic. The actual tangent body is
\([-t,t/2]\).

The first two projected normals coincide, but their actual supports do not. The weaker constraint \(y\le t\) has support derivative zero; the active constraint \(y\le t/2\) has derivative \(\phi(t/2)\). Correspondingly, \(q_{01}=0\): pinning \(x=y=t\) violates the third original normal's constraint. The coarea factor for the active pair is
\(\sigma_{02}=4/5\), and
\[
q_{02}=\phi(t)\phi(t/2)/(4/5).
\]

At the equal-support reference, the two copies of the positive tangent normal really are tied, and the support-mass function need not be differentiable there. The submitted proof never differentiates at that reference. This distinction is essential and valid.

### 2.4 A genuinely nonsimple cap and zero nonantipodal ridge coefficients

Take the eight unit normals
\[
v_\epsilon=\epsilon/\sqrt3,\qquad \epsilon\in\{-1,1\}^3.
\]
Their cap is the octahedron
\[
|x_1|+|x_2|+|x_3|\le\sqrt3\,t.
\]
Four facets meet at each vertex, so this is a nonsimple intrinsic polytope.

Fix \(v=(1,1,1)/\sqrt3\). The three normals differing in one sign have correlation \(1/3\). Their projected unit normals \(w_1,w_2,w_3\) satisfy
\[
w_1+w_2+w_3=0,\qquad w_j\cdot w_k=-1/2\quad(j\ne k),
\]
and their supports are \(b=t/\sqrt2\). The three normals differing in two signs have projected normals \(-w_j\) and supports \(2b=\sqrt2\,t\). The last normal is antipodal and is omitted.

The first three constraints form a triangle. Each extra constraint
\(-w_j\cdot y\le2b\) is redundant and touches only a vertex, since
\(-w_j=w_k+w_\ell\). Its support derivative is zero. Thus the associated nonantipodal pair has \(q=0\), although every physical facet is genuine.

This explicitly refutes the stronger assertion that every nonantipodal pair has a positive ridge coefficient. That assertion is not needed and is not made by the load-bearing argument. What is needed is at least one positive ridge coefficient per row.

The positive coefficients are the common \(q>0\) on Hamming-distance-one pairs. Each stress diagonal is \(-q\), so the canonical stress is not positive semidefinite. Its spectrum divided by \(q\) is
\(2,0,0,0,-2,-2,-2,-4\). Nonsimplicity therefore does not introduce an unexamined minimizer in this example; more importantly, the support derivative itself remains valid at its redundant, vertex-touching constraints.

### 2.5 Extreme positive kernel weights are not automatically canonical stress weights

Consider the actual rank-two Gaussian triangle with
\[
v_0=(1,0),\qquad v_\pm=(-c,\pm\sqrt{1-c^2}),\qquad0<c<1.
\]
Its positive normalized geometric kernel is
\[
a^{\rm geom}=\left(\frac c{1+c},\frac1{2(1+c)},\frac1{2(1+c)}\right).
\]
The largest weight tends to \(1/2\) as \(c\uparrow1\). All three facets and all three pair ridges are genuine. Set
\[
q_A=q_{0,+}=q_{0,-}=\phi_2(t,t;-c),\qquad
q_B=q_{+,-}=\phi_2(t,t;2c^2-1).
\]
There is no conditional probability factor less than one: at each pair pin, the remaining score is strictly below \(t\). Directly,
\[
\frac{q_A}{q_B}=2c\exp\left[t^2\left(\frac1{2c^2}-\frac1{1-c}\right)\right].
\]
If the canonical stress were positive semidefinite, trace orthogonality and the one-dimensional kernel would imply
\(S=\lambda a^{\rm geom}(a^{\rm geom})^T\), with \(\lambda>0\). Its off-diagonal entries would force \(q_A/q_B=2c\). At \(t>0\), this requires
\[
1-c-2c^2=(1-2c)(1+c)=0,
\]
hence \(c=1/2\), the regular triangle.

For example, \(c=49/51\) realizes the extreme geometric weights
\((49/100,51/200,51/200)\), but it is not a positive-canonical-stress configuration. These are actual Gaussian normals, not a scalar feasibility claim. The calculation demonstrates precisely why an arbitrary positive kernel cannot replace \(a=S\mathbf1/(\mathbf1^TS\mathbf1)\).

### 2.6 The supplied total-remainder counterexample is valid scalar data

With \(n=3\), \(p_0=1/2\), take
\[
x=(3/5,1/512,1/512),\qquad
u^{\rm press}=(9/50,27/200,27/200).
\]
Here the letter \(u\), used below for pressure, equals \(u^{\rm press}\); these are not asserted Gaussian data. Then
\[
U=9/20,\quad a=(2/5,3/10,3/10),\quad
X=773/1280<3/2,\quad X-U=197/1280>0.
\]
Nevertheless each inequality
\(x_i\log(x_i/p_0)\ge u_i(3a_i-1)\) holds. Indeed,
\[
\log(6/5)\ge1/6,
\qquad \log2<3/4,
\]
follow by integrating \(1/x\), using its minimum on \([1,6/5]\) and its strict trapezoidal upper bound on \([1,2]\), respectively. Thus the left sides have lower bounds
\[
1/10,\quad-3/256,\quad-3/256,
\]
which exceed the right sides
\[
9/250,\quad-27/2000,\quad-27/2000.
\]
The stronger square-root bounds in the submission also hold, since
\(\sqrt{3/5}>2/3\) and \(\sqrt{6/5}>87/80\), as checked by rational squaring.

The individual remainders are
\[
21/50,\quad-1703/12800,\quad-1703/12800.
\]
Two are negative. Therefore positivity of their sum cannot substitute for the submitted componentwise energy identity. The actual identity in Section 8 below rules out exactly this defect.

## 3. Smallest rigorous dependency tree

The tree does not include historical acceptance labels, four-/five-site theorems, honest attainment, optimized translations, or an Ehrhard inequality.

| Node | Statement and dependence | Audit status |
|---|---|---|
| A | Positive cap mass; duplicate splitting; compactness and threshold Lipschitz bound | Proved, all ranks |
| B | Relative covariance derivative, including antipodal limits | Proved from the Gaussian density identity and conditional continuity |
| C | Actual-support differentiability; coarea factors; at least one positive ridge per row | Proved without simplicity or full intrinsic rank |
| D | Full-domain lift gives \(S\succeq0\); trace orthogonality gives a positive kernel and \(2\le r\le n-1\) | Proved from A–C |
| E | Row Cauchy–Schwarz bound and support log-concavity tangent | Proved; the required logarithmic integral theorem is reconstructed |
| F | Strict componentwise pressure/energy split | Proved using C–D and homothety |
| G | Weighted mass lemma; boundary derivative bound | Proved from E–F and elementary convexity |
| H | Envelope recursion, base two, and integration from zero | Proved from A, D, G; no lower-size equality premise |
| I | Boundary equality implies regularity; fixed-threshold equality follows | Proved separately from G and the comparison |

Schematically,
\[
(A,B,C)\longrightarrow D,\qquad
(C,D,E,F)\longrightarrow G,\qquad
(A,D,G)\longrightarrow H,\qquad
(G,H)\longrightarrow I.
\]
The argument establishing support differentiability also establishes the fixed-shape threshold derivative used in H and I. The two-site theorem does not use any of B–G, where \(n-2\) would vanish.

## 4. Relative covariance differentiation at singular matrices

### 4.1 Positive-definite derivative

If \(G\) is positive definite, put \(A=G^{-1}\) and let \(p_G\) denote its Gaussian density. Vary the symmetric pair of entries \(g_{ij},g_{ji}\) together. Direct differentiation gives
\[
\frac{\partial p_G(x)}{\partial g_{ij}}
=\big((Ax)_i(Ax)_j-A_{ij}\big)p_G(x)
=\partial_{x_i}\partial_{x_j}p_G(x).
\]
The factor is one, not one half, because a single correlation parameter changes both symmetric matrix entries.

On a compact positive-definite neighborhood, the derivative is dominated by a polynomial times an integrable Gaussian. Differentiation under the integral is therefore valid. Integrating the last expression over the lower orthant leaves
\[
\frac{\partial F_G(t)}{\partial g_{ij}}
=\int_{x_\ell\le t,\ \ell\ne i,j}p_G(t,t,x_{-ij})\,dx_{-ij}
=q_{ij}(G,t).
\]
The integrations at minus infinity have zero boundary terms.

### 4.2 The conditional-atom obstruction is absent

Fix distinct unit rows \(v_1,\ldots,v_n\) representing a possibly singular \(G\), and a pair with \(-1<g_{ij}<1\). The two pinned scores have invertible covariance. The conditional mean and covariance of the other scores depend continuously on \(G\).

A remaining conditional score can put an atom at its threshold only if its conditional variance is zero. This means
\[
v_\ell=\alpha v_i+\beta v_j.
\]
At the pin \(X_i=X_j=t\), its value is \((\alpha+\beta)t\). Since \(t>0\), equality with the threshold requires \(\alpha+\beta=1\). Unit length now yields
\[
1=\alpha^2+\beta^2+2\alpha\beta g_{ij}
 =1-2\alpha\beta(1-g_{ij}).
\]
Thus \(\alpha\beta=0\), and \(v_\ell\) is one of the two pinned rows. That is a duplicate, contrary to the hypothesis.

Every remaining marginal conditional boundary therefore has probability zero. The finite union of those boundaries has probability zero as well, even if the whole conditional law is singular. Gaussian weak convergence proves continuity of the conditional lower-orthant probability. A zero-dimensional conditional law is included: all its deterministic remaining coordinates are strictly on one side or the other of their thresholds.

### 4.3 Antipodal limits

For a nonantipodal pair,
\[
0\le q_{ij}\le
\frac{1}{2\pi\sqrt{1-g_{ij}^2}}
\exp\left(-\frac{t^2}{1+g_{ij}}\right).
\]
As \(g_{ij}\downarrow-1\), the exponential dominates the square-root singularity, so the upper bound tends to zero. The prescribed extension \(q_{ij}=0\) is therefore continuous. The same estimate is uniform when \(t\) ranges over a compact subset of \((0,\infty)\).

This does not assert continuity through repeated coordinates \(g_{ij}=1\), nor through an antipodal pair at \(t=0\). Neither assertion is needed.

### 4.4 Regularization and a relative Fréchet differential

For nearby distinct-coordinate \(G,H\in\mathcal E_n\), set
\[
G_\eta=(1-\eta)G+\eta I,
\qquad H_\eta=(1-\eta)H+\eta I.
\]
Both are positive definite for \(\eta>0\). Apply the derivative formula along their segment:
\[
F_{H_\eta}(t)-F_{G_\eta}(t)
=(1-\eta)\int_0^1\sum_{i<j}
 q_{ij}((1-s)G_\eta+sH_\eta,t)(H_{ij}-G_{ij})\,ds.
\]
Choose a compact neighborhood of \(G\) on which all off-diagonal entries are bounded away from one. The preceding continuity and antipodal estimate make \(q\) bounded and uniformly continuous there. Letting \(\eta\downarrow0\) gives
\[
F_H(t)-F_G(t)=\int_0^1\sum_{i<j}
 q_{ij}((1-s)G+sH,t)(H_{ij}-G_{ij})\,ds.
\]
The endpoint CDFs converge because every threshold boundary lies in a finite union of standard-normal marginal null sets. Finally, continuity of \(q\) at \(G\) implies
\[
\boxed{F_H(t)-F_G(t)=\sum_{i<j}q_{ij}(G,t)(H_{ij}-G_{ij})
+o(\|H-G\|).}
\]
This is a relative differential on the elliptope, across changes in rank. The proof does not approximate a rank-lifting variation by a fixed-rank tangent variation.

## 5. Support derivatives and strict rowwise ridge positivity

### 5.1 An elementary support-differentiability lemma

Let \(w_1,\ldots,w_m\) be unit vectors in \(\mathbb R^p\), and define
\[
h(b)=\Pr(w_j\cdot Y\le b_j\ \forall j),\qquad Y\sim N(0,I_p).
\]
Suppose at \(b=b^0\) no two boundary hyperplanes
\(w_j\cdot y=b_j^0\) coincide. Then \(h\) is differentiable at \(b^0\), with
\[
\partial_{b_j}h(b^0)
=\int_{\{w_j\cdot y=b_j^0,\ w_k\cdot y\le b_k^0\ (k\ne j)\}}
 \phi_p(y)\,d\mathcal H^{p-1}(y).
\]
The derivative can be zero for a redundant constraint, including one touching a lower-dimensional face.

Here is a direct proof, including a first-order remainder. If \(\|b-b^0\|_\infty\le\eta\), changes occur only in strips
\(|w_j\cdot Y-b_j^0|\le\eta\). For linearly independent \(w_j,w_k\), the probability of the intersection of two such strips is \(O(\eta^2)\), because the two-dimensional Gaussian density is bounded. For parallel normals, the corresponding strips are disjoint for all sufficiently small \(\eta\), by the noncoincidence hypothesis. Consequently the error in summing individual single-constraint changes, with all other constraints fixed at \(b^0\), is \(O(\eta^2)\).

For one changed support,
\[
h(b^0+s e_j)-h(b^0)
=\int_{b_j^0}^{b_j^0+s}\phi(z)
 \Pr(w_k\cdot Y\le b_k^0\ (k\ne j)\mid w_j\cdot Y=z)\,dz.
\]
The conditional probability is continuous at \(z=b_j^0\). Indeed, each conditional remaining score is either nondegenerate, or comes from a parallel normal; in the latter case its deterministic value is not its threshold, again by noncoincidence. Weak convergence then gives continuity through their finite union of boundaries. Thus the single-constraint change has the stated derivative plus \(o(|s|)\). Summing finitely many such changes proves differentiability with an \(o(\|b-b^0\|)\) remainder.

In dimension one the boundary measure is counting measure on points. The proof still applies: all distinct boundary hyperplanes are distinct points, and their sufficiently thin strips are disjoint.

### 5.2 Why the actual projected supports have no coincident hyperplanes

Let \(G=VV^T\) have distinct unit rows, intrinsic rank \(r\ge2\), and fix \(t>0\). For \(j\) nonantipodal to \(i\), write
\[
\sigma_{ij}=\sqrt{1-g_{ij}^2},\quad
w_{ij}=\frac{v_j-g_{ij}v_i}{\sigma_{ij}},\quad
\delta_{ij}=\frac{t(1-g_{ij})}{\sigma_{ij}}
=t\sqrt{\frac{1-g_{ij}}{1+g_{ij}}}>0.
\]
The tangent cap is
\[
P_i=\{y\in v_i^\perp:w_{ij}\cdot y\le\delta_{ij}\ \forall j\}.
\]
An antipodal original row imposes \(-t\le t\) at the pin and is omitted.

If two projected boundary hyperplanes coincide with the same direction, their unit normals and supports agree. The map
\(g\mapsto t\sqrt{(1-g)/(1+g)}\) is strictly decreasing on \((-1,1)\), so their \(g\)'s agree. Their original rows
\(g v_i+\sqrt{1-g^2}\,w\) then agree, a contradiction. With opposite projected directions, coincident hyperplanes would require opposite supports, which is impossible when both supports are positive.

Unequal parallel constraints are harmless: the weaker one is inactive locally. No simplicity hypothesis has entered this argument.

### 5.3 Coarea and the exact factors

Let
\[
R_{ij}=\{x:v_i\cdot x=v_j\cdot x=t,\ v_\ell\cdot x\le t\ \forall\ell\}.
\]
The Jacobian of \(x\mapsto(v_i\cdot x,v_j\cdot x)\) on the two-dimensional normal space is \(\sigma_{ij}\). Gaussian disintegration, or an orthonormal change of coordinates in that space, gives
\[
q_{ij}=\frac1{\sigma_{ij}}\int_{R_{ij}}\phi_r(x)\,d\mathcal H^{r-2}(x).
\]
On \(x=tv_i+y\),
\(\phi_r(x)=\phi(t)\phi_{r-1}(y)\). Applying the support lemma to the actual \(\delta_i\) yields
\[
\boxed{\partial_{b_j}h_i(\delta_i)=
\frac{\sigma_{ij}q_{ij}}{\phi(t)},\qquad
h_i(b)=\gamma_{r-1}\{y:w_{ij}\cdot y\le b_j\ \forall j\}.}
\]
A lower-dimensional intersection contributes zero to the displayed ridge integral, as required in the nonsimple octahedral example.

The same support lemma applied to the original unit normals, whose positive-support hyperplanes are distinct, proves differentiability of the fixed-shape threshold profile and
\[
\boxed{F_G'(t)=\phi(t)\sum_i H_i,\qquad H_i=\gamma_{r-1}(P_i).}
\]
This also follows by adding single-coordinate threshold strips. No full-rank covariance density is being assumed here.

### 5.4 At least one strictly positive ridge per row

At \(tv_i\), every other original constraint has strict slack
\(t-tg_{ij}>0\). Thus \(0\) is an interior point of \(P_i\). There is at least one nonparallel other row because \(r\ge2\), so \(P_i\) is a proper full-dimensional polyhedron in \(v_i^\perp\).

For an explicit strict-ridge argument, choose a tangent direction \(u\) for which some \(w_{ij}\cdot u>0\), avoiding all the finitely many first-hit tie equations
\[
(\delta_{ij}w_{ik}-\delta_{ik}w_{ij})\cdot u=0.
\]
None of these equations is identically zero: otherwise the two unit projected normals and positive supports would agree. A finite union of proper linear hyperplanes cannot cover the open set of candidate directions. Along the ray \(s u\), therefore, the first constraint reached is unique. At the hitting point all other constraints are strict. It supplies a relatively open \((r-2)\)-dimensional part of a ridge, with positive Gaussian surface integral. For \(r=2\), it supplies a single genuine endpoint, whose zero-dimensional Gaussian surface integral is also positive.

Consequently every row has some nonantipodal \(j\) with \(q_{ij}>0\). In particular,
\[
k_i:=\sum_{j\ne i}(1-g_{ij})q_{ij}>0,
\qquad C_i:=\sum_{j\ne i}\sigma_{ij}q_{ij}>0.
\]
The argument does not claim positivity for every pair.

## 6. Positive stress and row geometry at every full-domain minimum

### 6.1 The lift

Fix \(n\ge3\), \(t>0\), and a full-elliptope local minimum \(G\). Its rows are distinct by duplicate splitting, and \(r\ge2\).

For arbitrary \(z\in\mathbb R^n\), append the coordinate \(\varepsilon z_i\) to row \(i\), then normalize that row. The resulting feasible Gram matrix is
\[
G_\varepsilon=D_\varepsilon^{-1}(G+\varepsilon^2zz^T)D_\varepsilon^{-1},
\quad (D_\varepsilon)_{ii}=\sqrt{1+\varepsilon^2z_i^2}.
\]
For each off-diagonal entry,
\[
(G_\varepsilon)_{ij}-g_{ij}
=\varepsilon^2\left(z_i z_j-\frac{g_{ij}}2(z_i^2+z_j^2)\right)+O(\varepsilon^4).
\]
The relative covariance differential gives
\[
F_{G_\varepsilon}(t)-F_G(t)=\frac{\varepsilon^2}{2}z^TSz+o(\varepsilon^2).
\]
Local minimality for every \(z\) implies \(S\succeq0\). The new coordinate may increase rank; feasibility is precisely why the full elliptope is required.

### 6.2 Trace orthogonality and a strictly positive kernel

The definition of the diagonal gives the exact cancellation
\[
\operatorname{tr}(GS)=\sum_iS_{ii}+\sum_{i\ne j}g_{ij}q_{ij}=0.
\]
For positive-semidefinite \(G,S\),
\[
0=\operatorname{tr}(G^{1/2}SG^{1/2})
=\|S^{1/2}G^{1/2}\|_{\rm HS}^2,
\]
so \(GS=SG=0\).

Set
\[
\kappa=\sum_i k_i=\mathbf1^TS\mathbf1>0,\qquad
 a_i=k_i/\kappa.
\]
Then \(a_i>0\), \(\sum_i a_i=1\), and
\[
Ga=0,\qquad \sum_i a_i v_i=0.
\]
The latter follows because \(0=a^TGa=\|V^Ta\|^2\). Thus
\(2\le r\le n-1\).

The intrinsic cap \(K=\{x:v_i\cdot x\le t\ \forall i\}\) is bounded. Otherwise choose \(x_m\in K\) with \(\|x_m\|\to\infty\), and pass to a convergent subsequence of unit directions, with limit \(u\). Then \(v_i\cdot u\le0\) for every \(i\). Their positive weighted sum is zero, so every \(v_i\cdot u=0\), contradicting the spanning of the intrinsic space and \(\|u\|=1\).

Each \(P_i\) is consequently bounded, has positive dimension \(d_0=r-1\), and contains a neighborhood of zero. None of these assertions assumes \(G\mathbf1=0\); only the generally nonuniform positive kernel \(a\) has been obtained.

### 6.3 The row inequality, including extreme weights

Scalar Cauchy–Schwarz gives
\[
C_i^2
\le\left(\sum_{j\ne i}(1-g_{ij})q_{ij}\right)
   \left(\sum_{j\ne i}(1+g_{ij})q_{ij}\right)
=k_i(k_i-2S_{ii}).
\]
Positive-semidefinite Cauchy–Schwarz gives
\[
k_i^2=(e_i^TS\mathbf1)^2\le S_{ii}\kappa.
\]
Here \(e_i\) in this single display is the coordinate vector. Therefore, writing
\(A_i=C_i/k_i\),
\[
0<A_i\le\sqrt{1-2a_i},\qquad0<a_i<1/2.
\]
The strict upper bound on \(a_i\) follows from \(C_i>0\), not from an assumed bound on arbitrary kernel weights.

Set
\[
d=n-2,\qquad A_* =\sqrt{d/n},\qquad \rho=t/A_*.
\]
The square-root tangent inequality gives
\[
\frac{A_i}{A_*}
\le\sqrt{1-\frac{2(na_i-1)}d}
\le1-\frac{na_i-1}{d}.
\]
Its argument is strictly positive because \(a_i<1/2\). Thus
\[
\boxed{d(1-A_i/A_*)\ge na_i-1.}
\]
No step requires \(na_i-1\ge0\). In particular negative row deviations remain available for the componentwise mass lemma.

Everything in Sections 6.2–6.3 also holds for a distinct-coordinate \(G\) whose canonical stress is positive semidefinite, without assuming it is a local minimum.

## 7. Log-concavity foundation and the tangent sign

### 7.1 The logarithmic integral theorem at the actual required scope

The required statement is the following: for finite Gaussian-dominated log-concave functions \(f,g,h\) on \(\mathbb R^p\), if \(0<s<1\) and
\[
h((1-s)x+sy)\ge f(x)^{1-s}g(y)^s\quad\forall x,y,
\]
then
\[
\int h\ge(\int f)^{1-s}(\int g)^s.
\]
Gaussian restrictions to convex caps are in this class. Domination by a finite constant times the standard Gaussian ensures every fiber and marginal encountered below is finite and integrable. The proof need not establish the unrestricted measurable-function version of the logarithmic integral theorem.

In one dimension, suppose the integrals of \(f,g\) are positive; the zero-integral cases are immediate. Normalize them to probability densities, simultaneously dividing \(h\) by the corresponding product of masses. A finite log-concave density is positive and continuous on the interior of its positivity interval. The continuity follows from the elementary continuity of a finite concave function on an open interval, applied to \(\log f\): monotonicity of secant slopes bounds its one-sided slopes on every strictly interior compact subinterval.

Let \(T\) be the increasing inverse-CDF transport from \(f\) to \(g\). On the open positivity interval of \(f\), ordinary one-dimensional inverse differentiation gives
\[
T'(x)=f(x)/g(T(x))>0.
\]
The map \(z(x)=(1-s)x+sT(x)\) is a continuously differentiable increasing change of variables. Thus
\[
\begin{aligned}
\int h
&\ge\int f(x)^{1-s}g(T(x))^s[(1-s)+sT'(x)]\,dx\\
&\ge\int f(x)^{1-s}g(T(x))^s[T'(x)]^s\,dx
=\int f=1.
\end{aligned}
\]
The second inequality is weighted arithmetic-geometric mean, which follows from concavity of \(\log\). Endpoints have measure zero. Infinite intervals are handled by increasing compact subintervals and monotone convergence. Undoing the normalization proves the one-dimensional assertion.

For induction in dimension, integrate in the last coordinate. For each pair of base points whose fibers have positive mass, the one-dimensional result gives the interpolation inequality for the marginal functions. If either fiber has zero mass, the required inequality is trivial. Each marginal is log-concave, by applying that same one-dimensional theorem to two fibers of a single log-concave function. The marginal remains Gaussian-dominated. The induction hypothesis in one fewer dimension completes the proof.

This is a complete proof of the scope used below, including unbounded caps and zero fibers. It avoids any unproved smoothing assertion.

### 7.2 Application to support numbers

For fixed unit normals \(w_j\), let \(P(b)=\{y:w_j\cdot y\le b_j\ \forall j\}\). Then
\[
(1-s)P(b)+sP(c)\subseteq P((1-s)b+sc).
\]
Moreover,
\[
\phi_p((1-s)x+sy)\ge\phi_p(x)^{1-s}\phi_p(y)^s,
\]
because squared norm is convex. Apply the theorem to the Gaussian densities restricted to the three caps. It follows that
\[
h((1-s)b+sc)\ge h(b)^{1-s}h(c)^s.
\]
Thus \(\log h\) is concave on its positive-mass domain. The actual vector \(\delta_i\) lies in the interior of that domain, since all its components are positive.

Let \(p_0>0\) satisfy
\[
h_i(\rho\mathbf1)\ge p_0\quad\text{for every }i.
\]
A differentiable concave function lies below its affine tangent. Explicitly, applying concavity along the segment from \(\delta_i\) to \(\rho\mathbf1\) and letting the segment parameter decrease to zero gives
\[
\log p_0\le\log h_i(\rho\mathbf1)
\le\log H_i+\frac1{H_i}\sum_j
 \partial_{b_j}h_i(\delta_i)(\rho-\delta_{ij}).
\]
Using the coarea derivative, and not differentiating the reference, yields
\[
\boxed{H_i\log\frac{H_i}{p_0}
\ge\frac{tk_i-\rho C_i}{\phi(t)}
=\frac{tk_i}{\phi(t)}(1-A_i/A_*).}
\]
The tangent sign in the submission is correct. It is an upper tangent for a concave logarithm, rearranged into a lower bound on \(H_i\log(H_i/p_0)\).

## 8. The strictly positive componentwise energy remainder

Fix a row \(i\), retaining its actual tangent normals and supports. Since
\(h_i(s\delta_i)=\gamma_{d_0}(sP_i)\), a change of variables gives
\[
\gamma_{d_0}(sP_i)=\int_{P_i}s^{d_0}\phi_{d_0}(sy)\,dy.
\]
The intrinsic cap is bounded, so differentiating under the integral near \(s=1\) is immediate. The chain rule and the support derivative give
\[
\begin{aligned}
\frac{tk_i}{\phi(t)}
&=\sum_j\delta_{ij}\partial_{b_j}h_i(\delta_i)\\
&=d_0H_i-\int_{P_i}|y|^2\,d\gamma_{d_0}(y).
\end{aligned}
\]
Now define the scalar pressure and remainder by
\[
u_i=\frac{tk_i}{d\phi(t)},\qquad e_i=H_i-u_i,
\qquad d=n-2,\quad d_0=r-1.
\]
Here and below \(u_i\), not the coordinate vector from the Cauchy–Schwarz calculation, denotes pressure. Then
\[
\boxed{H_i=u_i+e_i,\qquad u_i>0,\qquad
 e_i=\frac{(d-d_0)H_i+\displaystyle\int_{P_i}|y|^2\,d\gamma_{d_0}(y)}d>0.}
\]
This is the submitted formula with all factors retained.

The strict signs have separate reasons. First, \(t,k_i,d,\phi(t)\) are positive. Second, \(d\ge d_0\ge1\), and \(P_i\) contains an open ball about zero, so its unnormalized energy integral is strictly positive. This proves \(e_i>0\) for every individual row. It is not an inference from positivity after summation.

The identity additionally proves \(u_i<H_i\). Near zero the energy can be arbitrarily small, but it is strictly positive at every fixed positive threshold. No uniform lower bound is used later.

Finally,
\[
\frac{u_i}{\sum_j u_j}=\frac{k_i}{\kappa}=a_i.
\]
Combining the row bound and the support tangent gives the exact hypotheses
\[
\boxed{H_i\log(H_i/p_0)\ge u_i(na_i-1),\qquad H_i=u_i+e_i,\quad u_i,e_i>0.}
\]
They involve the same canonical Gaussian coefficients on the same actual facets.

## 9. The finite-measure mass lemma and the boundary theorem

### 9.1 Weighted mass lemma, including equality

Let \(\omega_i>0\), \(\sum_i\omega_i=1\), and let
\(x_i=u_i+e_i\) with \(u_i,e_i>0\). Put
\[
X=\sum_i x_i,\quad U=\sum_i u_i,\quad E=\sum_i e_i,
\quad a_i=u_i/U,\quad \nu_i=e_i/E.
\]
Suppose \(M>0\) and
\[
x_i\log\frac{x_i}{M\omega_i}
\ge u_i\left(\frac{a_i}{\omega_i}-1\right)
\quad\text{for every }i.
\]
Then \(X\ge M\). If \(X=M\), then
\(a=\nu=\omega\) and \(x_i=M\omega_i\).

For completeness, convexity of \(z\log z\), whose second derivative is \(1/z>0\), applied to
\[
\frac{x_i}{X\omega_i}=
\frac UX\frac{a_i}{\omega_i}+\frac EX\frac{\nu_i}{\omega_i}
\]
gives
\[
x_i\log\frac{x_i}{X\omega_i}
\le u_i\log\frac{a_i}{\omega_i}
+e_i\log\frac{\nu_i}{\omega_i}.
\]
Subtract this upper bound from the assumed lower bound. For \(v_i=a_i/\omega_i\),
\[
x_i\log\frac XM
\ge u_i(v_i-1-\log v_i)-e_i\log\frac{\nu_i}{\omega_i}.
\]
The function \(v-1-\log v\) is nonnegative, and vanishes only at one; this follows by differentiating it. If \(X<M\), the inequality forces \(\nu_i>\omega_i\) for every \(i\), contradicting their equal sums. If \(X=M\), it first forces \(\nu_i\ge\omega_i\) for every \(i\), hence \(\nu=\omega\). It then forces \(v_i=1\) for every \(i\), since each \(u_i>0\). The asserted form of \(x\) follows.

The same pointwise proof works on a probability space: replace normalized reference weights by the reference probability measure and take strictly positive integrable pressure and remainder densities. If the total mass were smaller than \(M\), the normalized remainder density would exceed one almost everywhere, contradicting its integral. In the equality case the two normalized densities are one almost everywhere. No entropy integrability assumption beyond the pointwise finite expressions is required for this argument, because the logarithmic inequalities are not integrated.

### 9.2 Boundary theorem

Apply the lemma with
\[
x_i=H_i,\qquad\omega_i=1/n,\qquad M=np_0.
\]
It gives
\[
\boxed{F_G'(t)=\phi(t)\sum_iH_i\ge n\phi(t)p_0.}
\]
The only geometric hypothesis here, beyond distinct coordinates and \(n\ge3,t>0\), is that the canonical stress is positive semidefinite, together with the common reference lower bound \(h_i(\rho\mathbf1)\ge p_0\). Local minimality is one sufficient mechanism for that stress hypothesis.

This proves the submitted boundary theorem, including all intrinsic ranks admitted by the stress calculation. No sum-only energy relaxation or artificial positive stress has been inserted.

## 10. Compactness, the envelope, and induction through zero

### 10.1 Continuity, existence, and positive mass

The elliptope is closed and bounded: its entries satisfy \(|g_{ij}|\le1\) by positive semidefiniteness of the two-by-two principal submatrices. It is therefore compact.

If \(G_m\to G\), the Gaussian laws converge weakly, for example by their characteristic functions. The boundary of any fixed threshold orthant is contained in the finite union \(\{X_i=t\}\), each of which has zero probability because every marginal is \(N(0,1)\). Consequently \(F_{G_m}(t)\to F_G(t)\). Moving \(t\) as well gives joint continuity, either by the same boundary argument or by the uniform marginal increment bound below.

Define
\[
m_n(t)=\min_{G\in\mathcal E_n}F_G(t),\qquad t\ge0.
\]
The minimum is attained. At \(t>0\), use a square-root representation \(X=G^{1/2}Z\), \(Z\sim N(0,I_n)\). Every row of \(G^{1/2}\) has norm one. Thus \(\|Z\|<t\) implies \(X_i<t\) for all \(i\), uniformly in \(G\), and
\[
m_n(t)\ge\Pr(\|Z\|<t)>0.
\]
This positivity was also used in the duplicate-splitting descent.

### 10.2 Uniform threshold regularity

For \(s\ge t\),
\[
0\le F_G(s)-F_G(t)
\le\sum_i\Pr(t<X_i\le s)=n[\Phi(s)-\Phi(t)].
\]
Monotonicity gives the lower bound for \(m_n(s)-m_n(t)\). Using a minimizer at \(t\) gives the same upper bound:
\[
0\le m_n(s)-m_n(t)\le n[\Phi(s)-\Phi(t)].
\]
Hence \(m_n\) is Lipschitz, and in particular absolutely continuous on every compact interval, including intervals with left endpoint zero.

The regular scores sum to zero almost surely and have positive rank. Thus the event that all are nonpositive forces all to be zero and has probability zero. Therefore
\[
m_n(0)=D_n(0)=0.
\]
No covariance derivative or pressure normalization is used at zero.

### 10.3 The envelope derivative needs no differentiable minimizer selection

At almost every \(t>0\), \(m_n\) is differentiable. Fix any minimizing \(G\) at such a threshold. It has distinct rows, and the fixed-shape function \(F_G\) is differentiable there by Section 5. It touches \(m_n\) from above:
\[
F_G(s)-m_n(s)\ge0,\qquad F_G(t)-m_n(t)=0.
\]
Differentiating this scalar local minimum gives
\[
m_n'(t)=F_G'(t).
\]
This argument does not differentiate the optimizer, require it to be unique, or preserve its rank as the threshold varies.

### 10.4 The lower-size reference is a genuine correlation-matrix problem

For each facet there are at most \(n-1\) retained unit tangent normals. There is at least one, since \(r\ge2\). Duplicate any retained normal as necessary to obtain exactly \(n-1\) normals. Their standard-Gaussian scores have a correlation matrix in \(\mathcal E_{n-1}\), and duplicating constraints changes neither the event nor its probability. Thus
\[
h_i(\rho\mathbf1)\ge m_{n-1}(\rho)>0,
\qquad\rho=t\sqrt{\frac n{n-2}}.
\]
The reference can be singular, unbalanced, or have repeated projected normals. These are legitimate lower-size competitors. No derivative at that reference is involved.

The boundary theorem now gives the unconditional envelope recursion
\[
\boxed{m_n'(t)\ge n\phi(t)
 m_{n-1}\!\left(t\sqrt{\frac n{n-2}}\right)
\quad\text{for almost every }t>0.}
\]
There is no induction hypothesis in this recursion itself.

### 10.5 The exact regular recursion

Pin one score of \(N(0,\Delta_n)\) at \(t\). Each remaining conditional mean is \(-t/(n-1)\). The conditional variance and off-diagonal covariance are
\[
\frac{n(n-2)}{(n-1)^2},\qquad-\frac{n}{(n-1)^2},
\]
respectively. On standardizing, the conditional correlation is \(\Delta_{n-1}\), and the threshold is
\(t\sqrt{n/(n-2)}\). The fixed-shape derivative formula therefore gives
\[
\boxed{D_n'(t)=n\phi(t)
 D_{n-1}\!\left(t\sqrt{\frac n{n-2}}\right).}
\]
The two-site calculation in Section 2.1 gives \(m_2=D_2\) on \([0,\infty)\). If \(m_{n-1}=D_{n-1}\), the two recursions give \(m_n'\ge D_n'\) almost everywhere on \((0,\infty)\). Absolute continuity and the common value zero at the origin imply
\[
m_n(t)-D_n(t)=\int_0^t[m_n'(s)-D_n'(s)]\,ds\ge0.
\]
Feasibility of \(\Delta_n\) gives the reverse inequality for the minimum. Hence \(m_n=D_n\) for every \(n\ge2\) and \(t\ge0\).

For \(t<0\), \(D_n(t)=0\), since zero-sum scores cannot all be strictly negative. This completes the comparison for every real threshold and every correlation matrix, including duplicates and all singular competitors. The exclusions were only exclusions from positive-threshold minimizers.

## 11. Equality rigidity, proved separately

### 11.1 Boundary equality

Suppose the boundary theorem is an equality:
\[
\sum_i H_i=np_0.
\]
The mass lemma implies
\[
a_i=1/n,\qquad H_i=p_0\quad\forall i.
\]
The actual-support tangent and the row bound then yield
\[
0\ge\frac{tk_i}{\phi(t)}(1-A_i/A_*)\ge0,
\]
so \(A_i=A_*\) for every row.

Both Cauchy–Schwarz inequalities in Section 6.3 are now equalities. To see this without an implicit equality assumption, their chain reads
\[
C_i^2\le k_i(k_i-2S_{ii})\le k_i^2(1-2/n),
\]
and its two endpoints are equal because \(A_i^2=(n-2)/n\). Thus
\[
k_i=\kappa/n,\qquad S_{ii}=k_i^2/\kappa=\kappa/n^2.
\]
Equality in the positive-semidefinite Cauchy–Schwarz inequality is equality for the two ordinary Euclidean vectors \(S^{1/2}e_i\) and \(S^{1/2}\mathbf1\). Their inner product is \(\kappa/n\) and the latter has squared norm \(\kappa>0\), so
\[
S^{1/2}e_i=\frac1nS^{1/2}\mathbf1\quad\forall i.
\]
Taking pairwise inner products gives
\[
S=\frac{\kappa}{n^2}J.
\]
In particular every off-diagonal \(q_{ij}\) is now strictly positive. This is the point where positivity of every pair is legitimately deduced.

Equality in scalar rowwise Cauchy–Schwarz makes
\((1+g_{ij})/(1-g_{ij})\) constant as \(j\ne i\) varies. Its monotonicity in \(g_{ij}\) makes each row's off-diagonal correlations constant. Since \(Ga=0\) and \(a=\mathbf1/n\), we have \(G\mathbf1=0\). A row with constant off-diagonal value \(c_i\) consequently satisfies
\(1+(n-1)c_i=0\). Every such value is \(-1/(n-1)\), and
\[
G=\Delta_n.
\]
No lower-size equality theorem or classification of stationary points was used.

### 11.2 Fixed-positive-threshold equality

Assume \(n\ge3\), \(t_0>0\), and \(F_G(t_0)=D_n(t_0)\). The comparison theorem makes \(G\) a global elliptope minimizer at that threshold, so its rows are distinct and its canonical stress is positive semidefinite.

The same comparison, now for all nearby thresholds with this fixed \(G\), shows that
\(F_G(t)-D_n(t)\) has a minimum zero at \(t_0\). Both profiles are differentiable there, hence
\[
F_G'(t_0)=D_n'(t_0).
\]
Choose \(p_0=D_{n-1}(t_0\sqrt{n/(n-2)})\). The proved lower-size comparison makes this a valid reference lower bound. The regular derivative recursion shows that the displayed derivative equality is exactly equality in the boundary theorem. Section 11.1 forces \(G=\Delta_n\).

The converse is immediate. The case \(n=2\) was proved directly by the strictly positive upper-tail intersection in Section 2.1. This completes the equality theorem at exactly the claimed scope.

## 12. Independent assembly and a transparent energy reformulation

These observations are made after checking the original interfaces. Neither is an unpaid replacement lemma.

### 12.1 A second induction assembly, without an envelope derivative

Assume the comparison at size \(n-1\) and suppose that
\(F_G(t)-D_n(t)<0\) for some \(G,t\). The negative value must occur at \(t>0\). Uniformly in \(G\),
\[
F_G(t)-D_n(t)\ge-D_n(t)\longrightarrow0\quad(t\downarrow0),
\]
and the marginal union bound gives
\[
F_G(t)-D_n(t)\ge-n[1-\Phi(t)]\longrightarrow0\quad(t\to\infty).
\]
Fixing any one negative value, these bounds confine a lower joint global minimum to \(\mathcal E_n\times[\alpha,\beta]\) for some \(0<\alpha<\beta<\infty\), with strictly higher values at its threshold endpoints. Compactness and continuity give an attained negative minimum \((G_*,t_*)\) with \(t_*\) interior.

Its covariance is a full-elliptope minimum of \(F_G(t_*)\), and threshold stationarity gives \(F_{G_*}'(t_*)=D_n'(t_*)\). The lower-size theorem supplies the same \(p_0\) as above, so this is boundary equality. Boundary rigidity forces \(G_*=\Delta_n\), contradicting the negative value.

This verifies the alternative assembly in the submission. It uses the already proved boundary equality statement, but not the size-\(n\) comparison or any lower-size equality statement, so it is not circular.

### 12.2 The lower-rank correction is free Gaussian energy

Once \(r\le n-1\) has been proved, embed the intrinsic row span in \(\mathbb R^{n-1}\). Every ambient tangent space now has the common dimension \(d=n-2\), and its cap is the cylinder
\[
\widetilde P_i=P_i\times\mathbb R^{d-d_0}.
\]
Its Gaussian mass is still \(H_i\). Its energy is
\[
\int_{\widetilde P_i}|y|^2\,d\gamma_d(y)
=\int_{P_i}|y|^2\,d\gamma_{d_0}(y)+(d-d_0)H_i.
\]
Each free standard-normal coordinate contributes exactly \(H_i\); its second moment is one, by integrating \(-x\phi'(x)=x^2\phi(x)\) over the line.

Consequently the pressure/energy split can be written uniformly in rank as
\[
\boxed{H_i=\frac{tk_i}{d\phi(t)}+
\frac1d\int_{\widetilde P_i}|y|^2\,d\gamma_d(y).}
\]
The second term is strictly positive because \(d\ge1\) and the cylinder contains an open ball. Homothety is legitimate even though the cylinder is unbounded: for \(s\) in a fixed neighborhood of one, the derivative of \(s^d\phi_d(sy)\) is dominated by an integrable constant times \((1+|y|^2)e^{-c|y|^2}\).

This formulation explains the intrinsic formula's extra \((d-d_0)H_i\) term. It is not an approximation, a change of Gaussian law on the actual constrained directions, or a hidden rank assumption.

### 12.3 Exact retained-correction identity

Let \(P=\sum_iH_i\), \(U=\sum_i u_i\), \(E=\sum_i e_i\), and \(\nu_i=e_i/E\). Define
\[
R_i=1-A_i/A_*-(na_i-1)/d\ge0,
\]
\[
T_i=H_i\log(H_i/p_0)-\frac{tk_i}{\phi(t)}(1-A_i/A_*)\ge0,
\]
\[
J_i=u_i\log(na_i)+e_i\log(n\nu_i)-H_i\log(nH_i/P)\ge0.
\]
The last sign is the componentwise log-sum inequality. Expanding the logarithms gives
\[
J_i=H_i\,d_{\rm Ber}(u_i/H_i\Vert U/P).
\]
Direct subtraction yields
\[
\boxed{H_i\log\frac{P}{np_0}+e_i\log(n\nu_i)
=u_i[na_i-1-\log(na_i)]
+\frac{tk_i}{\phi(t)}R_i+T_i+J_i.}
\]
All four terms on the right are nonnegative. At least one index has \(\nu_i\le1/n\). For that index the second term on the left is nonpositive, forcing \(P\ge np_0\). This gives another transparent view of why the positive remainder must be retained row by row.

The row-deficit identities in the submission also check algebraically:
\[
k_i^2(1-2a_i)-C_i^2
=2k_i\left(S_{ii}-\frac{k_i^2}{\kappa}\right)
+\left[k_i(k_i-2S_{ii})-C_i^2\right].
\]
The square-root tangent gap follows by rationalizing the difference; its denominator is positive because \(a_i<1/2\). These are exact identities, not new comparison premises or a quantitative CDF stability theorem.

## 13. Review coverage and limits

The reconstruction checks every requested load-bearing interface: singular covariance differentiation; the new-coordinate lift; duplicate exclusion; strict per-row ridge positivity; positive canonical stress and kernel weights at arbitrary-rank minima; support derivatives at nonsimple caps and at redundant constraints; projected-parallel constraints; the direction of the log-concavity tangent; strictly positive componentwise homothety remainders; the weighted mass lemma and its equality case; envelope differentiation at changing or singular minimizers; integration through zero; and fixed-positive-threshold equality.

The detailed support lemma and the explicit Gaussian-dominated logarithmic integral proof expand abbreviated arguments. They do not change the theorem or add an unpaid hypothesis. No first invalid inference was found in the chain needed for the theorem.

The opening general statement of the logarithmic integral theorem in Appendix B is broader than the class proved by the appendix's transport discussion. The proof above verifies exactly the finite Gaussian-dominated log-concave class needed for support caps and its marginals. The full arbitrary-measurable-integrand theorem is not a dependency.

The historical comparisons in submitted Sections 9.2–10 are not dependencies of the main proof. Their source-specific claims about earlier optimized-facet witnesses and other research programs were not adopted as premises or independently certified here. The supplied total-remainder scalar counterexample, the exact Section 8 identities, and the canonical cube example were checked as stated above. No computational scan is used to certify an infinite family.

This audit makes no literature-priority, publication, or novelty judgment. It does not establish a fixed-rank-constrained or balanced-constrained analogue of lift positivity, an optimized-tilt theorem, a uniform quantitative stability modulus, or a classification of all stationary points. The proved positive-stress boundary theorem and the two exact main theorems are the conclusions.

## 14. Inspected sources and exact replay record

### 14.1 Source ledger

The standalone attachment was read completely first, including all appendices. The archive's inventory was then inspected, and its copy of the proof was compared byte for byte with the standalone attachment.

| Source | Actual inspection/use |
|---|---|
| `0012__ALL_DIMENSIONAL_FSC_PRESSURE_ENERGY_PROOF.md` | Complete text, Sections 1–11 and Appendices A–C; source of the submitted claims and reconstructed interfaces |
| ZIP member `fsc_pressure_energy_2026-09-07/ALL_DIMENSIONAL_FSC_PRESSURE_ENERGY_PROOF.md` | Byte identity checked against the standalone; not a separate mathematical authority |
| ZIP member `fsc_pressure_energy_2026-09-07/README.md` | Read completely for packet organization and replay scope |
| ZIP member `fsc_pressure_energy_2026-09-07/verify_algebra.py` | Read completely before execution; copied to a new audit working directory |
| ZIP member `fsc_pressure_energy_2026-09-07/exact_checks.json` | Read completely; used only as the supplied replay output for exact comparison |
| Older `inputs/`, `references/`, diagnostic scripts, and prior proof/audit labels | Not mathematical premises; their source arguments were unnecessary because the standalone appendices suffice |

External sources and other reviewers' verdicts were not used. No conclusion depends on prior conversation or account context. The proofs of the Gaussian density derivative, coarea factors, support differentiation, logarithmic integral inequality, homothety identity, and equality cases are given in this document rather than delegated to an unseen source.

The original attachments were not modified. The supplied script writes its result next to itself, so it was executed only after being copied to the separate `replay/` directory.

### 14.2 Exact identity and execution receipts

The standalone proof has 31,684 bytes and SHA-256

```text
9a99bbbd81a33a73ee2068cad4438c80594b5da09dd219d50f803d4e2001a5e0
```

It is byte-identical to the named proof inside the ZIP. The uploaded ZIP has SHA-256

```text
44a084154f6ae4fb4729373f7b2e2c0fb08eee00e2e6dc18af0947acf8c8750f
```

The supplied `verify_algebra.py` has SHA-256

```text
e6536ecef5410d060d0cc97158f7ad18d54c3f034f8f6ab5aaf7240f9bbbd810
```

It ran successfully with exit status zero. Its newly generated `exact_checks.json` was byte-identical to the packaged receipt, whose SHA-256 is

```text
52ed851133f22564488c9fcd6375db1495981deb41d2decedcd821b6adb7f6c1
```

The replay checks four symbolic identities, the trace/lift coefficient on finitely many rational arrays at sizes 3–9, the cube stress spectrum, and rational bounds for the scalar counterexample. The generic rational arrays in that script are explicitly not asserted Gaussian covariances or canonical stresses. The logarithmic inequalities used for the scalar check were proved analytically in Section 2.6.

A second, independently written and inspected script checks the regular conditional covariance and scales at sizes 3–12, the square and nonsimple octahedral stress matrices, projected-parallel geometric parameters, the axial kernel and coefficient-ratio exponent identity, and the intrinsic/ambient energy identity. It ran successfully with exit status zero. Its Gaussian ridge patterns are justified in Section 2, not inferred from the script's matrices. No floating-point CDF quadrature, optimizer, random search, or imported diagnostic script was run.

Both scripts and their full receipts follow. They are also included as separate files in the companion audit bundle. The finite checks verify the displayed exact algebra only; Sections 4–11 provide the analytic proof.

### 14.3 Combined execution receipt

```json
{
  "analytic_verdict": "Comparison and fixed-positive-threshold uniqueness proved at the full stated scope; not formally verified.",
  "archive_copy_byte_identical": true,
  "independent_replay": {
    "command": "python replay/independent_exact_checks.py",
    "exit_status": 0,
    "output_sha256": "0c2131672fb437c1cb9a53a8d36877f112a4274fac2bce7e1e5185559074f243",
    "scope": "Exact finite matrix and geometric-parameter identities. Gaussian ridge patterns and analytic claims are proved in the Markdown.",
    "script_sha256": "c9ac5f683c99f6f7f1a5f069382979cb6da617fa2ff52a34c58ef2c7b81209a5"
  },
  "numerical_cdf_or_optimizer_runs": false,
  "proof_sha256": "9a99bbbd81a33a73ee2068cad4438c80594b5da09dd219d50f803d4e2001a5e0",
  "review_date": "2026-09-07",
  "supplied_replay": {
    "byte_identical_to_packaged_output": true,
    "command": "python replay/verify_algebra.py",
    "exit_status": 0,
    "output_sha256": "52ed851133f22564488c9fcd6375db1495981deb41d2decedcd821b6adb7f6c1",
    "packaged_output_sha256": "52ed851133f22564488c9fcd6375db1495981deb41d2decedcd821b6adb7f6c1",
    "scope": "Exact finite algebra and rational scalar bounds only.",
    "script_sha256": "e6536ecef5410d060d0cc97158f7ad18d54c3f034f8f6ab5aaf7240f9bbbd810"
  }
}
```

### 14.4 Supplied replay output

```json
{
  "scalar_counterexample": {
    "U": "9/20",
    "X": "773/1280",
    "a": [
      "2/5",
      "3/10",
      "3/10"
    ],
    "analytic_lhs_lower_bounds": [
      "1/10",
      "-3/256",
      "-3/256"
    ],
    "componentwise_remainders": [
      "21/50",
      "-1703/12800",
      "-1703/12800"
    ],
    "linear_rhs": [
      "9/250",
      "-27/2000",
      "-27/2000"
    ],
    "n": 3,
    "reference_mass_per_component": "1/2",
    "scope": "Abstract scalar data; not a Gaussian realization.",
    "sqrt_rhs_rational_upper_bounds": [
      "3/50",
      "-189/16000",
      "-189/16000"
    ],
    "total_remainder": "197/1280",
    "u": [
      "9/50",
      "27/200",
      "27/200"
    ],
    "x": [
      "3/5",
      "1/512",
      "1/512"
    ]
  },
  "scope": "Not formal verification of the analytic Gaussian theorem.",
  "status": "All exact algebra and scalar-adverse assertions passed.",
  "stress": {
    "cube_eigenvalue_multiplicities": {
      "-2": 2,
      "0": 3,
      "4": 1
    },
    "cube_negative_direction_quadratic": "-8",
    "trace_and_lift_sizes": [
      3,
      4,
      5,
      6,
      7,
      8,
      9
    ]
  },
  "symbolic": {
    "binary_KL_identity": true,
    "componentwise_correction_identity": true,
    "row_deficit_identity": true,
    "sqrt_tangent_numerator": true
  }
}
```

### 14.5 Independent replay output

```json
{
  "ambient_cylinder_energy_identity": true,
  "axial_triangle": {
    "PSD_stress_necessary_ratio": "2c",
    "extreme_geometric_kernel_weights": [
      "49/100",
      "51/200",
      "51/200"
    ],
    "only_solution_for_0<c<1_and_t>0": "c=1/2",
    "q_A_over_q_B": "2c exp(t^2 (1-2c)(1+c)/(2c^2(1-c)))",
    "warning": "Geometric kernel weights are not automatically the canonical stress weights."
  },
  "nonsimple_octahedral_cap": {
    "far_support_over_t_squared": "2",
    "near_support_over_t_squared": "1/2",
    "projected_pair_inner_product": "-1/2",
    "stress_over_q_diagonal": "-1",
    "stress_over_q_eigenvalues": {
      "-2": 3,
      "-4": 1,
      "0": 3,
      "2": 1
    },
    "zero_nonantipodal_ridges_per_row": 3
  },
  "projected_parallel_polygon": {
    "actual_supports_over_t": {
      "1": "1",
      "2": "1/2",
      "4": "1"
    },
    "inactive_same_direction_constraint_index": 1,
    "pinned_interval": "[-t,t/2]"
  },
  "python_version": "3.13.5",
  "regular_simplex_sizes": [
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    12
  ],
  "scope": "Exact finite matrix and geometric-parameter checks only; analytic proofs are separate.",
  "script_sha256": "c9ac5f683c99f6f7f1a5f069382979cb6da617fa2ff52a34c58ef2c7b81209a5",
  "square_stress_over_q": {
    "eigenvalue_multiplicities": {
      "-2": 1,
      "0": 2,
      "2": 1
    },
    "negative_direction": [
      1,
      -1,
      1,
      -1
    ],
    "quadratic_value": "-8"
  },
  "status": "All independent exact finite assertions passed.",
  "sympy_version": "1.14.0"
}
```

## Appendix A. Supplied replay code, inspected before execution

The following is the unmodified ZIP member `verify_algebra.py`. It requires SymPy.

```python
#!/usr/bin/env python3
"""Exact algebra and scalar-adverse checks accompanying the analytic proof.

This script does not verify Gaussian support concavity, the covariance
relative differential, or the continuum theorem. Those are proved in the
report. No numerical CDF, optimizer, random scan, or quadrature is used here.
Requires the already installed SymPy package; no network access is used.
"""
from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path

import sympy as sp


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def symbolic_checks() -> dict[str, bool]:
    k, kap, sii, c = sp.symbols('k kap sii c', positive=True)
    lhs = k**2 * (1 - 2*k/kap) - c**2
    rhs = 2*k*(sii-k**2/kap) + k*(k-2*sii)-c**2
    require(sp.expand(lhs-rhs) == 0, 'row-deficit decomposition')

    d, v = sp.symbols('d v', positive=True)
    L = 1 - (v-1)/d
    require(sp.expand(L**2-(1-2*(v-1)/d)-(v-1)**2/d**2) == 0,
            'square-root tangent numerator')

    u, e, U, E, n, p0, A, ast = sp.symbols(
        'u e U E n p0 A ast', positive=True)
    H, P, a, nu = u+e, U+E, u/U, e/E
    J = u*sp.log(n*a) + e*sp.log(n*nu) - H*sp.log(n*H/P)
    binary = u*sp.log((u/H)/(U/P)) + e*sp.log((e/H)/(E/P))
    require(sp.simplify(sp.expand_log(J-binary, force=True)) == 0,
            'binary KL identity')
    row_slack = 1-A/ast-(n*a-1)/d
    support_slack = H*sp.log(H/p0)-d*u*(1-A/ast)
    lhs = H*sp.log(P/(n*p0)) + e*sp.log(n*nu)
    rhs = u*(n*a-1-sp.log(n*a))+d*u*row_slack+support_slack+J
    require(sp.simplify(sp.expand_log(lhs-rhs, force=True)) == 0,
            'exact componentwise pressure-energy correction')

    return {
        'row_deficit_identity': True,
        'sqrt_tangent_numerator': True,
        'binary_KL_identity': True,
        'componentwise_correction_identity': True,
    }


def stress_checks() -> dict[str, object]:
    sizes = range(3, 10)
    for n in sizes:
        # Arbitrary rational symmetric off-diagonal arrays suffice for
        # these algebra identities. They are NOT asserted Gaussian stresses.
        G = sp.eye(n)
        Q = sp.zeros(n)
        for i in range(n):
            for j in range(i+1, n):
                G[i,j] = G[j,i] = sp.Rational((i+j) % 5 - 2, 6)
                Q[i,j] = Q[j,i] = sp.Rational(1+(i+2*j) % 7, 11)
        S = Q.copy()
        for i in range(n):
            S[i,i] = -sum(G[i,j]*Q[i,j] for j in range(n) if j != i)
        require(sp.trace(G*S) == 0, f'trace GS, n={n}')
        z = sp.Matrix([sp.Rational((-1)**i*(i+1), n) for i in range(n)])
        direct = sum(Q[i,j]*(z[i]*z[j]-G[i,j]*(z[i]**2+z[j]**2)/2)
                     for i in range(n) for j in range(i+1,n))
        require(sp.expand(direct-(z.T*S*z)[0]/2) == 0,
                f'lift coefficient, n={n}')

    # Exact canonical cube stress up to its positive common factor q(t).
    S = sp.zeros(6)
    for i in range(6):
        for j in range(6):
            if i//2 != j//2:
                S[i,j] = 1
    z = sp.Matrix([1,1,-1,-1,0,0])
    require(S*z == -2*z, 'cube negative stress direction')
    inertia = S.eigenvals()
    require(inertia == {4: 1, -2: 2, 0: 3}, 'cube spectrum')
    return {
        'trace_and_lift_sizes': list(sizes),
        'cube_eigenvalue_multiplicities': {str(k): v for k,v in inertia.items()},
        'cube_negative_direction_quadratic': str((z.T*S*z)[0]),
    }


def exact_scalar_counterexample() -> dict[str, object]:
    n, p0 = 3, F(1,2)
    x = [F(3,5), F(1,512), F(1,512)]
    u = [F(9,50), F(27,200), F(27,200)]
    X, U = sum(x), sum(u)
    a = [ui/U for ui in u]
    require(a == [F(2,5),F(3,10),F(3,10)], 'normalized pressures')
    require(X == F(773,1280) and U == F(9,20), 'totals')
    require(0 < X-U == F(197,1280), 'positive total energy remainder')
    require(X < n*p0, 'strict mass deficit')
    require(x[0] > u[0] and all(x[i] < u[i] for i in (1,2)),
            'componentwise positivity fails')

    # Analytic bounds proved in the report:
    # log(6/5) >= 1/6; log 2 < 3/4.
    lhs_lower = [x[0]*F(1,6), -F(3,256), -F(3,256)]
    rhs_linear = [u[i]*(n*a[i]-1) for i in range(n)]
    require(all(lhs_lower[i] > rhs_linear[i] for i in range(n)),
            'all linear support inequalities hold')

    # sqrt(3/5) > 2/3 and sqrt(6/5) > 87/80,
    # both certified by rational squaring.
    require(F(3,5) > F(2,3)**2, 'first sqrt bound')
    require(F(6,5) > F(87,80)**2, 'second sqrt bound')
    rhs_sqrt_upper = [u[0]*F(1,3), -u[1]*F(7,80), -u[2]*F(7,80)]
    require(all(lhs_lower[i] > rhs_sqrt_upper[i] for i in range(n)),
            'all stronger sqrt support inequalities hold')
    return {
        'n': n, 'reference_mass_per_component': str(p0),
        'x': list(map(str,x)), 'u': list(map(str,u)),
        'a': list(map(str,a)), 'X': str(X), 'U': str(U),
        'total_remainder': str(X-U),
        'componentwise_remainders': [str(xi-ui) for xi,ui in zip(x,u)],
        'linear_rhs': list(map(str,rhs_linear)),
        'analytic_lhs_lower_bounds': list(map(str,lhs_lower)),
        'sqrt_rhs_rational_upper_bounds': list(map(str,rhs_sqrt_upper)),
        'scope': 'Abstract scalar data; not a Gaussian realization.',
    }


def main() -> None:
    result = {
        'status': 'All exact algebra and scalar-adverse assertions passed.',
        'scope': 'Not formal verification of the analytic Gaussian theorem.',
        'symbolic': symbolic_checks(),
        'stress': stress_checks(),
        'scalar_counterexample': exact_scalar_counterexample(),
    }
    target = Path(__file__).resolve().with_name('exact_checks.json')
    target.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
```

## Appendix B. Independent replay code, inspected before execution

```python
#!/usr/bin/env python3
"""Independent exact finite checks for the pressure/energy audit.

These checks verify matrix identities and exact geometric parameters.
They do not numerically integrate a Gaussian, test all configurations,
or certify an analytic inequality. Canonical ridge patterns are proved
in the accompanying Markdown, not inferred by this program.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import platform
from pathlib import Path

import sympy as sp


def require(value: object, label: str) -> None:
    if not bool(value):
        raise AssertionError(label)


def stress(G: sp.Matrix, Q: sp.Matrix) -> sp.Matrix:
    require(G.rows == G.cols == Q.rows == Q.cols, "matching square matrices")
    S = Q.copy()
    for i in range(G.rows):
        S[i, i] = -sum(G[i, j] * Q[i, j] for j in range(G.rows) if j != i)
    return S


def eigen_receipt(S: sp.Matrix) -> dict[str, int]:
    return {str(k): int(v) for k, v in sorted(S.eigenvals().items(), key=lambda kv: kv[0])}


def main() -> None:
    result: dict[str, object] = {
        "scope": "Exact finite matrix and geometric-parameter checks only; analytic proofs are separate.",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
    }

    # Regular simplex: exact conditional Gram, threshold multiplier squared,
    # normalized stress, and row ratio squared. The common q factor is omitted.
    for n in range(3, 13):
        G = (n * sp.eye(n) - sp.ones(n)) / (n - 1)
        Q = sp.ones(n) - sp.eye(n)
        S = stress(G, Q)
        require(S == sp.ones(n), f"regular stress, n={n}")
        require(G * S == sp.zeros(n), f"regular orthogonality, n={n}")
        c = G[1:, 0]
        conditional = G[1:, 1:] - c * c.T
        variance = sp.Rational(n * (n - 2), (n - 1)**2)
        lower = ((n - 1) * sp.eye(n - 1) - sp.ones(n - 1)) / (n - 2)
        require(conditional == variance * lower, f"conditional Gram, n={n}")
        rho_squared = sp.Rational(n, n - 1)**2 / variance
        require(rho_squared == sp.Rational(n, n - 2), f"reference scale, n={n}")
        C_squared = (n - 1)**2 * (1 - sp.Rational(1, n - 1)**2)
        require(C_squared / n**2 == sp.Rational(n - 2, n), f"regular row ratio, n={n}")
    result["regular_simplex_sizes"] = list(range(3, 13))

    # Square cap: normals e1,e2,-e1,-e2. Orthogonal pairs are actual ridges.
    V = sp.Matrix([[1, 0], [0, 1], [-1, 0], [0, -1]])
    G = V * V.T
    Q = sp.Matrix(4, 4, lambda i, j: int(i != j and G[i, j] == 0))
    S = stress(G, Q)
    z = sp.Matrix([1, -1, 1, -1])
    require(S * z == -2 * z, "square negative lift direction")
    require(eigen_receipt(S) == {"-2": 1, "0": 2, "2": 1}, "square spectrum")
    result["square_stress_over_q"] = {
        "eigenvalue_multiplicities": eigen_receipt(S),
        "negative_direction": list(z),
        "quadratic_value": str((z.T * S * z)[0]),
    }

    # Nonsimple octahedral cap: eight cube-vertex normals, divided by sqrt(3).
    # Hamming-one pairs give edges; Hamming-two pairs meet only at a vertex.
    signs = list(itertools.product([-1, 1], repeat=3))
    V = sp.Matrix(signs)
    G = V * V.T / 3
    Q = sp.Matrix(8, 8, lambda i, j: int(sum(a != b for a, b in zip(signs[i], signs[j])) == 1))
    S = stress(G, Q)
    require(all(S[i, i] == -1 for i in range(8)), "octahedral negative stress diagonal")
    require(G * S == sp.zeros(8), "octahedral stress orthogonality")
    require(eigen_receipt(S) == {"-4": 1, "-2": 3, "0": 3, "2": 1}, "octahedral spectrum")
    g_near, g_far = sp.Rational(1, 3), sp.Rational(-1, 3)
    delta_near_squared = (1 - g_near) / (1 + g_near)
    delta_far_squared = (1 - g_far) / (1 + g_far)
    projected_dot = (sp.Rational(-1, 3) - g_near**2) / (1 - g_near**2)
    require(delta_near_squared == sp.Rational(1, 2), "near support squared")
    require(delta_far_squared == 2, "far support squared")
    require(projected_dot == sp.Rational(-1, 2), "equilateral projected normals")
    result["nonsimple_octahedral_cap"] = {
        "stress_over_q_eigenvalues": eigen_receipt(S),
        "stress_over_q_diagonal": "-1",
        "near_support_over_t_squared": str(delta_near_squared),
        "far_support_over_t_squared": str(delta_far_squared),
        "projected_pair_inner_product": str(projected_dot),
        "zero_nonantipodal_ridges_per_row": 3,
    }

    # A true five-normal polygon with coincident projected directions but
    # different actual supports. Row 0 is pinned at x=t.
    V = sp.Matrix([[1, 0], [0, 1], [sp.Rational(3, 5), sp.Rational(4, 5)], [-1, 0], [0, -1]])
    G = V * V.T
    require(all(G[i, i] == 1 for i in range(5)), "polygon unit normals")
    supports: dict[str, str] = {}
    for j in (1, 2, 4):
        g = G[0, j]
        sigma = sp.sqrt(1 - g**2)
        w = sp.simplify((V.row(j) - g * V.row(0)) / sigma)
        expected = sp.Matrix([[0, 1 if j in (1, 2) else -1]])
        require(w == expected, f"projected direction, j={j}")
        supports[str(j)] = str(sp.simplify((1 - g) / sigma))
    require(supports == {"1": "1", "2": "1/2", "4": "1"}, "actual support ratios")
    result["projected_parallel_polygon"] = {
        "actual_supports_over_t": supports,
        "pinned_interval": "[-t,t/2]",
        "inactive_same_direction_constraint_index": 1,
    }

    # Actual rank-two axial triangles with extreme geometric kernel weights.
    c = sp.symbols("c", positive=True)
    G = sp.Matrix([[1, -c, -c], [-c, 1, 2*c**2 - 1], [-c, 2*c**2 - 1, 1]])
    a = sp.Matrix([c/(1+c), 1/(2*(1+c)), 1/(2*(1+c))])
    require(sp.simplify(G * a) == sp.zeros(3, 1), "axial positive kernel")
    exponent = 1/(2*c**2) - 1/(1-c)
    factored = (1-2*c)*(1+c)/(2*c**2*(1-c))
    require(sp.simplify(exponent - factored) == 0, "axial q-ratio exponent")
    extreme = sp.simplify(a.subs(c, sp.Rational(49, 51)))
    require(extreme == sp.Matrix([sp.Rational(49, 100), sp.Rational(51, 200), sp.Rational(51, 200)]), "extreme geometric weights")
    result["axial_triangle"] = {
        "q_A_over_q_B": "2c exp(t^2 (1-2c)(1+c)/(2c^2(1-c)))",
        "PSD_stress_necessary_ratio": "2c",
        "only_solution_for_0<c<1_and_t>0": "c=1/2",
        "extreme_geometric_kernel_weights": [str(x) for x in extreme],
        "warning": "Geometric kernel weights are not automatically the canonical stress weights.",
    }

    # Ambient-cylinder energy: free Gaussian coordinates supply exactly
    # (d-d0)H, rather than an omitted or sign-indefinite correction.
    d, d0, H, energy = sp.symbols("d d0 H energy")
    pressure = (d0*H - energy)/d
    require(sp.expand(H - pressure - ((d-d0)*H + energy)/d) == 0, "intrinsic/ambient energy identity")
    result["ambient_cylinder_energy_identity"] = True
    result["status"] = "All independent exact finite assertions passed."
    result["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    # Convert the square vector's SymPy integers without silently rounding.
    result["square_stress_over_q"]["negative_direction"] = [int(x) for x in z]  # type: ignore[index]
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    Path(__file__).with_name("independent_exact_receipt.json").write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
```

## Appendix C. Reproduction commands

From the companion bundle directory, using Python with SymPy available:

```sh
python replay/verify_algebra.py
cmp replay/exact_checks.json replay/packaged_exact_checks.json
python replay/independent_exact_checks.py
```

The exact receipts do not replace any proof in Sections 4–11. The analytic reconstruction in this Markdown is self-contained at the scope of the stated theorems.
