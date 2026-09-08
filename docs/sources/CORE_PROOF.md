# A stationary boundary proof of simplex Gaussian domination

Status: reconstructed post-solution proof, 2026-09-07. The original theorem has [dedicated private analytic acceptance](../FSC_TWO_CRITICS_INGESTION_2026-09-07.md). The [construction03/outside01 ingestion](../POST_SOLUTION_03_OUTSIDE_01_INGESTION_2026-09-07.md) records the latest independent reconstruction. The replacements below are new exposition and checked derivations, not a historical-priority or external-assurance claim. Coordinator sources: external required; legacy selected.

The central operation is not cancellation of Gaussian noise or a globally monotone flow. At a hypothetical bad extremum, feasibility supplies the particular directional covariance tests needed by the conditional boundary masses. Full positive-semidefinite stress is a valid stronger certificate, but is not needed. A componentwise scaling identity makes their total large enough, contradicting the extremum.

## Theorem and proof map

Let $\mathcal E_n=\{G\succeq0:\operatorname{diag}G=\mathbf1\}$ and $\Delta_n=(nI-J)/(n-1)$, for $n\ge2$. Write
$$
F_G(t)=\Pr(X_i\le t\text{ for all }i),\quad X\sim N(0,G),
\qquad D_n(t)=F_{\Delta_n}(t).
$$
Then $F_G(t)\ge D_n(t)$ for every $G\in\mathcal E_n$ and real $t$. At each fixed finite $t>0$, equality holds if and only if $G=\Delta_n$.

Here a positive semidefinite matrix is one whose quadratic form is nonnegative. A conditional pin means conditioning one or two Gaussian coordinates to equal a specified value, using their Gaussian conditional law. No density of the full possibly singular vector is required.

The dependencies are:

1. Gaussian conditioning and covariance differentiation give canonical pair weights.
2. A finite set of feasible covariance paths gives exactly the required row inequalities at a minimum.
3. Scalar Cauchy, support log-concavity and homothetic scaling give componentwise mass inequalities.
4. A scalar Cauchy argument converts these to a boundary inequality, with rigid equality.
5. A negative joint minimum of the CDF difference is impossible; induction starts at two coordinates.

The proof uses no full PSD-stress certificate, shape Hessian, boundedness of every conditional cap, optimized exponential tilt, entropy inequality, Ehrhard inequality, deconvolution theorem, or differential equation for a flow.

## 1. Canonical pins and first-order optimality

Fix $n\ge3$ and $t>0$. First suppose $G$ has distinct coordinates, meaning $g_{ij}<1$ for $i\ne j$. For $-1<g_{ij}<1$, set
$$
q_{ij}=\phi_2(t,t;g_{ij})
\Pr(X_\ell\le t\ (\ell\ne i,j)\mid X_i=X_j=t).
$$
Here $\phi$ is the standard normal density and $\phi_2(\cdot,\cdot;c)$ the bivariate density with correlation $c$. Set $q_{ij}=0$ when $g_{ij}=-1$. The relative differential on the elliptope is
$$
DF_G(t)[H]=\sum_{i<j}q_{ij}H_{ij}.
\tag{1}
$$
The word relative means along feasible correlation-matrix perturbations, including changes of rank; it does not claim a density exists in all ambient directions.

For completeness, the singular boundary is harmless here. Under a nonantipodal pair pin, a deterministic third coordinate could equal $t$ only if its unit normal were a duplicate: writing it as $\alpha v_i+\beta v_j$ forces $\alpha+\beta=1$ and $\alpha\beta(1-g_{ij})=0$. Thus all other conditional threshold boundaries have zero probability. Conditional Gaussian convergence makes $q_{ij}$ continuous at such pins. As $g_{ij}\downarrow-1$, the bivariate density at $(t,t)$ tends to zero exponentially. Apply the ordinary positive-definite covariance differentiation formula to $(1-\varepsilon)G+\varepsilon I$, integrate along a feasible line segment, and let $\varepsilon\downarrow0$. These continuity and domination facts give (1), with a remainder small relative to the covariance increment. Full details are in the [fresh audit, sections 4–5](../../../../inbox/pro-chat-exports/gaussian-extremal-theory/criticism/2026-09-07-gpt6-all-dimensional-fsc-fresh-critic-01/attachments/0003__ALL_DIMENSIONAL_FSC_AUDIT.md).

Define the canonical stress and its row sums by
$$
S_{ij}=q_{ij}\ (i\ne j),\qquad
S_{ii}=-\sum_{j\ne i}g_{ij}q_{ij},\qquad
k_i=(S\mathbf1)_i=\sum_{j\ne i}(1-g_{ij})q_{ij}.
\tag{2}
$$
For any frozen $L\succeq0$, the feasible path
$$
G_s=D_s(G+sL)D_s,\qquad (D_s)_{ii}=(1+sL_{ii})^{-1/2}
$$
has objective derivative $\frac12\operatorname{tr}(SL)$. This follows by differentiating the normalization in (1); no full-density or fixed-rank assumption is needed. At a local minimum this derivative is nonnegative for every such path, but we will only use explicitly specified directions.

Every row has a positive pin, without any optimality assumption. Choose $j\ne i$ maximizing $g_{ij}$. Distinctness and $n\ge3$ imply $-1<g_{ij}<1$. For every remaining $\ell$,
$$
\mathbb E[X_\ell\mid X_i=X_j=t]
=t\frac{g_{i\ell}+g_{j\ell}}{1+g_{ij}}<t,
$$
because $g_{i\ell}\le g_{ij}$ and $g_{j\ell}<1$. Zero is strictly inside every inequality for the centered conditional residual, so their joint probability is positive even if the residual is singular. Consequently
$$
k_i>0,\qquad C_i:=\sum_{j\ne i}\sqrt{1-g_{ij}^2}\,q_{ij}>0.
\tag{3}
$$
Put $\kappa=\sum_i k_i$ and $a_i=k_i/\kappa$. Let $\mathbf e^{(i)}$ be the $i$th coordinate vector, and freeze $z_i=\mathbf e^{(i)}-a_i\mathbf1$ at the current covariance. At a local minimum, the feasible choices $L=z_i z_i^\top$ give
$$
\sigma_i=z_i^\top Sz_i=S_{ii}-k_i^2/\kappa\ge0.
$$
These particular tests suffice; the full assertion $S\succeq0$ and its consequence $GS=0$ can leave the proof. For the conditional construction below we require $\operatorname{rank}G\le n-1$; section 4 excludes positive-definite minima directly.

Scalar Cauchy and the displayed directional tests give one useful row bound:
$$
C_i^2
\le k_i\sum_{j\ne i}(1+g_{ij})q_{ij}
=k_i(k_i-2S_{ii})
\le k_i^2(1-2a_i).
\tag{4}
$$
The first is scalar Cauchy with weights $q_{ij}$; the second uses precisely $\sigma_i\ge0$. Thus $0<a_i<1/2$ and $A_i=C_i/k_i\le\sqrt{1-2a_i}$.

Let
$$
d=n-2,\qquad A_*=\sqrt{d/n},\qquad \rho=t/A_*.
$$
The tangent inequality for the concave square root at $a_i=1/n$ gives
$$
d(1-A_i/A_*)\ge na_i-1.
\tag{5}
$$
The right side is signed; replacing it by its absolute value would be false.

## 2. The same pins control actual conditional masses

Continue with $\sigma_i\ge0$ for all $i$ and $r=\operatorname{rank}G\le n-1$. Realize the unit normals $v_i$ in $\mathbb R^{n-1}$, adding unused independent Gaussian coordinates if the intrinsic rank is smaller. Given $v_i\cdot Z=t$, the residual is standard Gaussian in $v_i^\perp$, of dimension exactly $d$. For each $j\ne i$ with $g_{ij}>-1$ define
$$
w_{ij}=\frac{v_j-g_{ij}v_i}{\sqrt{1-g_{ij}^2}},\qquad
b_{ij}=t\frac{1-g_{ij}}{\sqrt{1-g_{ij}^2}}>0.
$$
The conditional success event is the possibly unbounded cap
$$
Q_i(b_i)=\{y\in v_i^\perp:w_{ij}\cdot y\le b_{ij}\text{ for all such }j\}.
$$
Write $h_i(b)=\gamma_d(Q_i(b))$ and $H_i=h_i(b_i)>0$. Conditioning on a single threshold gives
$$
F'_G(t)=\phi(t)\sum_iH_i,\qquad
\partial_{b_{ij}}h_i(b_i)=
\frac{\sqrt{1-g_{ij}^2}}{\phi(t)}q_{ij}.
\tag{6}
$$
Derivatives are taken at the actual supports, not at an equal-support reference where projected directions can coincide. A one-support variation is a Gaussian strip. Conditional boundary atoms at an actual support would force coincident actual supporting planes, hence duplicate original normals. Different actual parallel planes have different supports and cause no such atom; redundant inequalities simply have zero derivative. This conditioning argument handles nonsimple caps and singular residuals. See the [continuing audit, section 5](../../../../inbox/pro-chat-exports/gaussian-extremal-theory/criticism/2026-09-07-gpt6-five-site-critic-all-dimensional-02/attachments/0008__ALL_DIMENSIONAL_INDEPENDENT_AUDIT_2026-09-07.md).

The function $1/h_i$ is convex in positive supports. A sufficient, familiar fact is Prékopa log-concavity of $h_i$: integrate the jointly log-concave Gaussian density restricted to the convex support inequalities, then compose $-\log h_i$ with the convex increasing exponential. For unbounded caps, first intersect all interpolated caps with the same ball, apply the bounded log-concave statement, and pass to the increasing limit. No arbitrary-measurable-function version is needed.

Suppose $h_i(\rho\mathbf1)\ge p_0>0$ for every $i$. The tangent inequality for the convex reciprocal gives
$$
\frac1{p_0}\ge\frac1{h_i(\rho\mathbf1)}
\ge\frac1{H_i}+
\frac{\langle b_i-\rho\mathbf1,\nabla h_i(b_i)\rangle}{H_i^2}.
$$
Thus, using (6),
$$
\frac{H_i^2}{p_0}-H_i
\ge\langle b_i-\rho\mathbf1,\nabla h_i(b_i)\rangle
=\frac{tk_i}{\phi(t)}(1-A_i/A_*).
\tag{7}
$$

Scaling the same cap gives the componentwise positive decomposition
$$
H_i=u_i+e_i,\qquad
u_i=\frac{tk_i}{d\phi(t)},\qquad
e_i=\frac1d\int_{Q_i(b_i)}|y|^2\,d\gamma_d(y)>0.
\tag{8}
$$
Indeed $\gamma_d(sQ)=s^d\int_Q\phi_d(sy)\,dy$, and differentiating at $s=1$ gives $\langle b,\nabla h(b)\rangle=dH-\int_Q|y|^2\,d\gamma_d$. For $s$ near one the derivative is dominated by an integrable multiple of $(1+|y|^2)e^{-|y|^2/8}$, even on unbounded $Q$. Positive supports make $Q$ contain a ball, which proves strict positivity.

Padding is explicit, not a change in intrinsic rank: every unused coordinate contributes exactly $H_i$ to the energy integral. If the original intrinsic tangent dimension is $d_0=r-1$, the old correction $(d-d_0)H_i$ is precisely this free-coordinate energy. Boundedness and positive-spanning arguments can leave the proof.

Set $U=\sum_j u_j$. Equations (5), (7) and (8) yield
$$
\frac{H_i^2}{p_0}-H_i\ge u_i(na_i-1),
\qquad a_i=u_i/U.
$$
Equivalently, these are precisely the quadratic comparison hypotheses
$$
\frac{H_i^2}{np_0}-\frac{u_i^2}{U}\ge\frac{e_i}{n}.
\tag{9}
$$
Both identities must use the same actual canonical pins. An independently chosen positive kernel, translated facet optimizer or formal stress matrix does not supply (6)–(9).

## 3. Scalar mass conversion and boundary rigidity

Here is the entire qualitative scalar argument. Suppose $x_i=u_i+e_i$ with $u_i,e_i>0$, and let $U=\sum u_i$, $E=\sum e_i$, $X=U+E$. Let $M>0$, $\omega_i>0$, $\sum\omega_i=1$, and assume
$$
\frac{x_i^2}{M}-\frac{u_i^2}{U}\ge\omega_i e_i
\quad\text{for every }i.
$$
Choose an index with $e_i/E\le\omega_i$. Cauchy–Schwarz then gives
$$
\frac{x_i^2}{M}-\frac{u_i^2}{U}
\ge\omega_i e_i\ge\frac{e_i^2}{E}
\ge\frac{x_i^2}{X}-\frac{u_i^2}{U}.
$$
Thus $X\ge M$. If $X=M$, for every index
$$
\omega_i e_i\le x_i^2/X-u_i^2/U\le e_i^2/E.
$$
Thus $e_i/E\ge\omega_i$; equal sums force equality throughout. Cauchy equality gives $u_i/U=e_i/E=\omega_i$, and $x_i=M\omega_i$.

Apply this to (9), with $x_i=H_i$, $\omega_i=1/n$ and $M=np_0$. For any distinct configuration of rank at most $n-1$ satisfying these directional tests,
$$
F'_G(t)\ge n\phi(t)p_0.
\tag{10}
$$
If equality holds, the scalar argument forces $a_i=1/n$ and $H_i=p_0$. Equation (7) and (5) force $A_i=A_*$. Equality in scalar Cauchy in (4) makes $(1+g_{ij})/(1-g_{ij})$ constant over each row's positive pins. Since $A_i=A_*$, every positive pin has $g_{ij}=-1/(n-1)$. Each row-maximal pair is a positive pin by section 1, so every off-diagonal entry is at most this value. But
$$
0\le\mathbf1^\top G\mathbf1=n+2\sum_{i<j}g_{ij}\le0,
$$
forcing equality of every entry with the bound. Thus $G=\Delta_n$, without PSD-stress equality or $GS=0$.

No equality classification for Prékopa–Leindler or for the lower-dimensional theorem enters this rigidity argument.

## 4. A strict comparison barrier rules out a negative minimum

For $n=2$, the union bound gives $F_G(t)\ge2\Phi(t)-1=D_2(t)$ when $t>0$. Equality fails if the correlation exceeds $-1$, since the two upper-tail events have positive intersection. For $t\le0$, $D_2(t)=0$.

Assume the comparison for $n-1$ coordinates. Each equal-support reference in section 2 involves at most $n-1$ unit Gaussian scores; append repeated scores if necessary. Therefore its mass is at least
$$
p_0=D_{n-1}(\rho).
$$
Conditioning a regular simplex score directly gives
$$
D_n'(t)=n\phi(t)D_{n-1}\!\left(t\sqrt{\frac n{n-2}}\right)
=n\phi(t)p_0.
\tag{11}
$$

Suppose $F_{G_0}(t_0)-D_n(t_0)=-\delta<0$ for some $t_0>0$. Set $\varepsilon=\delta/(2t_0)>0$ and minimize the explicitly perturbed difference
$$
\Psi(G,t)=F_G(t)-D_n(t)+\varepsilon t.
$$
It is negative at $(G_0,t_0)$. Uniformly over the compact elliptope,
$$
\Psi(G,t)\ge-D_n(t)+\varepsilon t\longrightarrow0\quad(t\downarrow0),
\qquad
\Psi(G,t)\ge-1+\varepsilon t\longrightarrow+\infty\quad(t\to\infty).
$$
Thus a negative global minimum is attained at some $(G_*,t_*)$ with $0<t_*<\infty$. Joint continuity follows from Gaussian weak convergence: each coordinate is a nondegenerate standard Gaussian, so the finite union of coordinate threshold boundaries has zero probability. This linear barrier makes threshold stationarity strict; it is not an unannounced change to a CDF ratio.

Every such CDF is positive at $t>0$: in a unit-normal realization the event contains $\{\|Z\|<t\}$. This also ensures $p_0=D_{n-1}(\rho)>0$. The minimizing covariance has no duplicates. If one coordinate duplicates another, replace just that coordinate by a fresh independent standard Gaussian, leaving the others unchanged. Removing its old duplicate constraint changes no event, whereas adding its new independent constraint multiplies the old probability by $\Phi(t_*)<1$. This strictly improves the objective, a contradiction. A positive-definite minimum is also impossible: for small $s>0$, $G+s(I-J)$ is feasible and (1) gives derivative $-\sum_{i<j}q_{ij}<0$. Hence the minimizing covariance is singular. Section 1 supplies $\sigma_i\ge0$, and the conditional construction applies.

At the interior threshold minimum,
$$
F'_{G_*}(t_*)-D_n'(t_*)=-\varepsilon<0.
$$
Equations (10)–(11) give the opposite inequality. This contradiction proves the comparison by induction, without using boundary rigidity or lower-dimensional uniqueness. For $t\le0$, $D_n(t)=0$ because the regular-simplex scores sum to zero and have no atom at the origin.

Finally, if equality occurs at a fixed positive threshold, that covariance is a global shape minimum and hence has no duplicates and is singular by the same exclusions. The now nonnegative function $F_G-D_n$ touches zero at an interior threshold, so its derivative is zero. The same boundary rigidity proves uniqueness.

## What was compressed and what remains essential

The CDF-difference minimum with an explicit linear barrier replaces Lipschitz envelopes, almost-everywhere differentiation, integration and the tail endpoint estimate. It also proves comparison independently of rigidity; the envelope remains a valid alternative assembly in the original proof. Independent-coordinate replacement replaces infinitesimal duplicate splitting in the core. Explicit Gaussian padding replaces rank-specific energy bookkeeping. Reciprocal-support convexity feeds scalar Cauchy directly, replacing the logarithmic support inequality and entropy mass lemma. The former PSD Cauchy step is now replaced by the finite directional tests; nearest-positive-pin equality removes the PSD equality theorem. The [inverse-energy identity](COVARIANCE_CORRECTION.md) combines these tests into one weaker sufficient derivative condition, retaining support, geometric and mixing losses. This module uses the separate tests because they give the shorter teaching proof; the identity gives explicit compensated descent.

The essential analytic interface is still the identification of canonical pins in (1), (6) and (8). Covariance optimality alone only minimizes a linearization; support concavity alone loses the componentwise scaling budget. The proof works because these operations are compatible. The [abstract comparison and defects](COMPONENTWISE_COMPARISON.md) separate this reusable assembly from its Gaussian realization.
