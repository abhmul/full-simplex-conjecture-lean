---
title: "Why the regular simplex maximizes a Gaussian maximum"
subtitle: "A self-contained teaching manuscript: two proofs from one Gaussian boundary calculus"
author: ""
date: ""
lang: en-US
---

The theorem in this manuscript compares the distributions of Gaussian maxima, not only their expectations. Its proof is an induction on the number of coordinates. The induction becomes possible only after we learn how three different changes of a Gaussian probability fit together: changing the covariance, moving a boundary, and dilating a region. The same conditional Gaussian probabilities occur in all three calculations.

There are two complete presentations. The main presentation uses a finite collection of feasible covariance variations, convexity of reciprocal probability, and the Cauchy--Schwarz inequality. It ends by ruling out a worst counterexample with a small linear penalty in the threshold. The second presentation retains more geometry and uses logarithmic probability and an entropy identity. It ends by comparing the least possible probability at each threshold. Both presentations use the same analytic foundations; their different final arguments do not make those foundations independent of one another.

The background is ordinary graduate linear algebra, probability, measure theory, and analysis. In particular, we use the spectral theorem for real symmetric matrices, change of variables, Fubini--Tonelli, and dominated and monotone convergence. All the specialized facts about Gaussian covariance derivatives, conditioning at boundary values, and integrals of log-concave functions are proved here. The envelope argument is also justified directly, without assuming a theorem about differentiating a minimizing covariance.

Sections 1--2 explain the statement and the scalar mechanism. Sections 3--7 develop the shared foundations. Sections 8--9 give the main proof, including equality. Sections 10--11 give the geometric and logarithmic proof with its alternative global ending. Section 12 explains the retained information and tests the tempting shortcuts. The notation guide at the end can be used while moving between the two presentations.

# 1. The theorem, its geometry, and its elementary boundary cases

## 1.1. What is being compared?

Let $\mathbf1=(1,\ldots,1)^\top\in\mathbb R^n$, and let $J=\mathbf1\mathbf1^\top$. A real symmetric matrix $G$ is **positive semidefinite**, written $G\succeq0$, if

$$
z^\top Gz\ge0\qquad\text{for every }z\in\mathbb R^n.
$$

A **correlation matrix** is a positive-semidefinite matrix with every diagonal entry equal to one. We write

$$
\mathcal E_n=\{G\in\mathbb R^{n\times n}:G=G^\top\succeq0,\ G_{ii}=1\}.
$$

For $G\in\mathcal E_n$, define

$$
F_G(t)=\mathbb P\{X_i\le t\text{ for every }i\},\qquad X\sim N(0,G).
$$

A singular $G$ is allowed: $N(0,G)$ means the centered Gaussian law with covariance $G$, even when that law has no density on $\mathbb R^n$. We will construct it explicitly below.

The distinguished covariance is

$$
\Delta_n=\frac{nI-J}{n-1},\qquad D_n(t)=F_{\Delta_n}(t).
\tag{1.1}
$$

**Theorem 1.1.** For every integer $n\ge2$, every $G\in\mathcal E_n$, and every real $t$,

$$
\boxed{F_G(t)\ge D_n(t).}
\tag{1.2}
$$

For every fixed finite $t>0$,

$$
\boxed{F_G(t)=D_n(t)\quad\Longleftrightarrow\quad G=\Delta_n.}
\tag{1.3}
$$

For real random variables $A,B$, saying that $B$ **stochastically dominates** $A$ means

$$
\mathbb P\{A\le t\}\ge\mathbb P\{B\le t\}\quad\text{for all real }t.
$$

The direction can initially look backwards: the variable that is larger in this sense has the smaller cumulative distribution function. Thus (1.2) says that the regular-simplex maximum is stochastically at least as large as every competing maximum.

## 1.2. Correlation matrices are configurations of unit vectors

By the spectral theorem, a matrix $G\succeq0$ of rank $r$ can be written

$$
G=VV^\top,
$$

where $V$ is an $n$ by $r$ matrix of rank $r$. If $v_i\in\mathbb R^r$ is its $i$th row, then

$$
v_i\cdot v_j=g_{ij},\qquad |v_i|^2=g_{ii}=1.
\tag{1.4}
$$

Here and throughout, $|\cdot|$ is Euclidean norm. Conversely, the matrix of inner products of any collection of unit vectors is a correlation matrix, because

$$
z^\top Gz=\left|\sum_i z_i v_i\right|^2\ge0.
$$

For a standard Gaussian $Z\sim N(0,I_r)$, set $X_i=v_i\cdot Z$. Then $X$ is centered Gaussian with covariance $G$. In this representation,

$$
F_G(t)=\gamma_r(K_t),\qquad
K_t=\{z\in\mathbb R^r:v_i\cdot z\le t\text{ for every }i\},
\tag{1.5}
$$

where

$$
\phi_r(z)=(2\pi)^{-r/2}e^{-|z|^2/2},\qquad
\gamma_r(A)=\int_A\phi_r(z)\,dz.
$$

We write $\phi=\phi_1$ and $\Phi(t)=\int_{-\infty}^t\phi(s)\,ds$.

The region $K_t$ is an intersection of halfspaces, hence closed, convex, and measurable. It need not be bounded. The number $r$ is the dimension of the span of the normals, not necessarily $n-1$.

The identity

$$
\mathbb E(X_i-X_j)^2=2(1-g_{ij})
$$

shows that $g_{ij}=1$ exactly when $X_i=X_j$ almost surely, or equivalently $v_i=v_j$. We call these **repeated coordinates**. Similarly, $g_{ij}=-1$ means $X_j=-X_i$ and $v_j=-v_i$; such normals are **antipodal**. Distinct coordinates will mean $g_{ij}<1$ for every $i\ne j$, not that the covariance is invertible.

Every correlation satisfies $|g_{ij}|\le1$. This follows either from (1.4) and Cauchy--Schwarz or from the nonnegative determinant of the two by two principal submatrix on $i,j$.

## 1.3. Why the covariance in (1.1) is a regular simplex

The vector $\mathbf1$ is in the kernel of $\Delta_n$, while every vector perpendicular to $\mathbf1$ is an eigenvector with eigenvalue $n/(n-1)$. Hence $\Delta_n$ is positive semidefinite, has unit diagonal, and has rank $n-1$. Its off-diagonal entries are all $-1/(n-1)$.

One concrete realization uses the standard coordinate vectors $f_1,\ldots,f_n$ of $\mathbb R^n$:

$$
v_i^*=\sqrt{\frac n{n-1}}\left(f_i-\frac1n\mathbf1\right).
\tag{1.6}
$$

These vectors lie in $\mathbf1^\perp$, have norm one, and have inner products $-1/(n-1)$ when their indices differ. All pairwise squared distances are therefore $2n/(n-1)$. They are affinely independent: if $\sum_i c_i=0$ and $\sum_i c_i v_i^*=0$, then (1.6) gives $\sum_i c_i f_i=0$, so every $c_i=0$. Their convex hull is consequently a regular simplex with $n$ vertices in an $(n-1)$-dimensional space.

For independent standard normal variables $Z_1,\ldots,Z_n$, another useful realization is

$$
\xi_i=\sqrt{\frac n{n-1}}(Z_i-\overline Z),
\qquad \overline Z=\frac1n\sum_jZ_j.
\tag{1.7}
$$

Computing covariances gives $\operatorname{Cov}(\xi)=\Delta_n$. In particular,

$$
\sum_i\xi_i=0\quad\text{almost surely}.
\tag{1.8}
$$

A singular covariance is thus not an exceptional technical nuisance surrounding the optimizer. The optimizer itself is singular.

## 1.4. Nonpositive thresholds and two coordinates

If $t<0$, (1.8) prevents all $\xi_i$ from being at most $t$. If $t=0$, all $\xi_i\le0$ together with (1.8) force every $\xi_i=0$. This event has probability zero, since even the first coordinate has a continuous standard normal law. Therefore

$$
D_n(t)=0\qquad(t\le0).
\tag{1.9}
$$

Comparison at these thresholds follows immediately from $F_G(t)\ge0$. There is no uniqueness assertion there. For example, a vector that contains both $Z$ and $-Z$ has probability zero of having every coordinate at most $t\le0$, regardless of many of its other correlations.

For $n=2$ and $t>0$, inclusion--exclusion gives

$$
F_G(t)=2\Phi(t)-1+\mathbb P\{X_1>t,\ X_2>t\}.
\tag{1.10}
$$

The antipodal pair $(Z,-Z)$ makes the final term zero, and

$$
D_2(t)=2\Phi(t)-1.
\tag{1.11}
$$

If $-1<g_{12}<1$, the bivariate Gaussian density is strictly positive on the open set $\{x_1>t,x_2>t\}$, so the final term in (1.10) is positive. If $g_{12}=1$, that term is $1-\Phi(t)>0$. Thus both comparison and positive-threshold uniqueness are already proved for $n=2$.

All subsequent arguments involving $d=n-2$ will be used only for $n\ge3$.

## 1.5. Compactness, continuity, and a uniform increment bound

We will eventually minimize a probability over $\mathcal E_n$. We record carefully why this is legitimate even at singular matrices.

The set $\mathcal E_n$ is closed: the diagonal constraint is closed, and an entrywise limit of nonnegative quadratic forms is nonnegative. It is bounded because $|g_{ij}|\le1$. In finite dimensions it is therefore compact.

The positive-semidefinite square root is continuous. Here is a short proof that avoids an assumption of invertibility. If $G_m\to G\succeq0$, the matrices $G_m^{1/2}$ are bounded. Every convergent subsequence has a positive-semidefinite limit $A$ with $A^2=G$. There is only one such limit: a positive-semidefinite square root commutes with $G$ and, on each eigenspace of $G$ with eigenvalue $\lambda$, equals $\sqrt\lambda$ times the identity. Thus every subsequential limit is $G^{1/2}$, proving convergence of the entire sequence.

On one probability space let $Z\sim N(0,I_n)$ and use the realization $G_m^{1/2}Z$. If $t_m\to t$, then

$$
G_m^{1/2}Z\longrightarrow G^{1/2}Z\quad\text{almost surely}.
$$

Except on the event that some coordinate of $G^{1/2}Z$ equals $t$, the indicators of the corresponding threshold events converge. That exceptional event has probability zero: each marginal is standard normal, and there are finitely many coordinates. Dominated convergence therefore proves that

$$
(G,t)\longmapsto F_G(t)\quad\text{is jointly continuous on }
\mathcal E_n\times\mathbb R.
\tag{1.12}
$$

For $t>0$, the probability is strictly positive, uniformly over $G$. Each row of $G^{1/2}$ has norm one, so $|Z|<t$ implies $(G^{1/2}Z)_i<t$ for every $i$. Consequently

$$
F_G(t)\ge\gamma_n\{z:|z|<t\}>0.
\tag{1.13}
$$

Finally, if $s\ge t$, the event that the maximum lies in $(t,s]$ requires at least one coordinate to lie in $(t,s]$. The union bound gives

$$
0\le F_G(s)-F_G(t)\le n[\Phi(s)-\Phi(t)]
\le\frac n{\sqrt{2\pi}}(s-t).
\tag{1.14}
$$

These facts use only the common marginal distribution. They do not require distinct coordinates or a fixed rank.

# 2. The scalar mechanism we want the Gaussian calculation to produce

## 2.1. Why a boundary comparison can be enough

The desired inequality concerns the mass of a region, but it will be easier to compare the rate at which that mass grows when its common threshold increases. At a positive threshold this rate is a sum of conditional probabilities, one from each boundary face. Conditioning one coordinate leaves at most $n-1$ remaining coordinates, which is the opening for induction.

There is a difficulty: those conditional probabilities need not each exceed the regular-simplex conditional probability. The argument needs a way to add them while retaining how their derivatives fit together.

The following scalar lemma is the essential addition rule. It is useful to see it before the Gaussian notation becomes elaborate. The later analytic work is not a substitute for this lemma; it is what produces its rather specific hypotheses.

## 2.2. A componentwise Cauchy--Schwarz lemma

**Lemma 2.1 (mass from positive components).** Let $u_i,e_i>0$ for $1\le i\le N$, and define

$$
x_i=u_i+e_i,\qquad U=\sum_i u_i,\qquad E=\sum_i e_i,\qquad P=U+E=\sum_i x_i.
$$

Let $M>0$ and let $\omega_i>0$ satisfy $\sum_i\omega_i=1$. Suppose that, separately for every $i$,

$$
\frac{x_i^2}{M}-\frac{u_i^2}{U}\ge\omega_i e_i.
\tag{2.1}
$$

Then $P\ge M$. If $P=M$, then

$$
\frac{u_i}{U}=\frac{e_i}{E}=\omega_i,
\qquad x_i=M\omega_i
\quad\text{for every }i.
\tag{2.2}
$$

Conversely, the pattern (2.2), with $U+E=M$, gives equality in every hypothesis.

**Proof.** Cauchy--Schwarz applied to

$$
\left(\frac{u_i}{\sqrt U},\frac{e_i}{\sqrt E}\right)
\quad\text{and}\quad (\sqrt U,\sqrt E)
$$

gives

$$
\frac{x_i^2}{P}\le\frac{u_i^2}{U}+\frac{e_i^2}{E}.
\tag{2.3}
$$

At least one index satisfies $e_i/E\le\omega_i$, because both vectors $(e_i/E)_i$ and $(\omega_i)_i$ sum to one. Choose such an index. By (2.1) and (2.3),

$$
\frac{x_i^2}{M}-\frac{u_i^2}{U}
\ge\omega_i e_i
\ge\frac{e_i^2}{E}
\ge\frac{x_i^2}{P}-\frac{u_i^2}{U}.
$$

Cancel the common term. Since $x_i>0$, the resulting inequality $1/M\ge1/P$ says $P\ge M$.

Now suppose $P=M$. For every index, not only the selected one,

$$
\omega_i e_i\le\frac{x_i^2}{P}-\frac{u_i^2}{U}
\le\frac{e_i^2}{E}.
$$

Because $e_i>0$, this gives $\omega_i\le e_i/E$. Equality of the sums forces $e_i/E=\omega_i$ for every $i$. Equality must then hold in (2.3). Equality in the two-dimensional Cauchy--Schwarz inequality says $u_i/U=e_i/E$. This proves (2.2). Its converse follows by substitution. $\square$

The conclusion comes from one component whose normalized remainder is no larger than its reference weight. We do not know in advance which component that is. This is why the hypotheses must hold component by component.

The letter $P$ denotes a total in this scalar lemma, not necessarily a probability less than one. In its Gaussian application it will be the sum of $n$ conditional probabilities, and $\omega_i=1/n$.

## 2.3. What the Gaussian part must supply

For each coordinate we will construct an actual conditional probability $H_i$. Gaussian scaling will give a decomposition

$$
H_i=u_i+e_i,\qquad u_i>0,\ e_i>0.
\tag{2.4}
$$

Here $u_i$ measures part of the rate at which that conditional region expands, and $e_i$ is an actual Gaussian second-moment integral over the same region. Feasible covariance variations will control the relative sizes $u_i/\sum_j u_j$. Convexity in the boundary locations will then yield

$$
\frac{H_i^2}{np_0}-\frac{u_i^2}{\sum_j u_j}\ge\frac{e_i}{n},
\tag{2.5}
$$

where $p_0$ is a common lower bound for certain equal-threshold reference probabilities. Lemma 2.1 will give $\sum_iH_i\ge np_0$.

At a covariance that minimizes $F_G(t)$, the needed covariance variations cannot decrease its value. This is enough. There is no requirement that the same inequality about boundary rates hold at every covariance, and no need to construct a motion that improves all nonregular covariances all the way to the simplex.

# 3. Gaussian conditioning without division by a null event

## 3.1. Orthogonal decomposition is the definition of the conditional law

Let $Z$ be standard Gaussian in a Euclidean space and let $v$ be a unit vector. Complete $v$ to an orthonormal basis. The Gaussian density in that basis factors into one-dimensional standard Gaussian densities. Thus

$$
Z=(v\cdot Z)v+Y,
$$

where $v\cdot Z$ is standard normal, $Y$ is standard Gaussian in $v^\perp$, and the two are independent.

Accordingly, the conditional law of $Z$ given $v\cdot Z=s$ is defined by

$$
s v+Y.
\tag{3.1}
$$

This is not division by $\mathbb P\{v\cdot Z=s\}=0$. It is a specified family of probability laws. Fubini's theorem shows that integrating this family against $\phi(s)\,ds$ recovers the original Gaussian law, so it is a conditional distribution. It is defined at every real $s$, including a threshold at which we wish to evaluate it.

If $v_i,v_j$ are unit vectors with $c=v_i\cdot v_j\in(-1,1)$, put

$$
\sigma=\sqrt{1-c^2},\qquad
w=\frac{v_j-cv_i}{\sigma}.
$$

Then $v_i,w$ are orthonormal. With independent standard normal coordinates $S,T$ and an independent standard Gaussian residual $Y$ perpendicular to both, the ambient Gaussian is

$$
Z=S v_i+T w+Y,
\qquad X_i=S,\quad X_j=cS+\sigma T.
\tag{3.2}
$$

Conditioning $X_i=s_i$, $X_j=s_j$ therefore means replacing $(S,T)$ by

$$
\left(s_i,\frac{s_j-cs_i}{\sigma}\right)
$$

and leaving $Y$ unchanged. If the perpendicular space has dimension zero, $Y$ is simply the deterministic zero vector. This convention includes pair conditioning in an intrinsic two-dimensional configuration.

The bivariate density obtained from (3.2) is

$$
\phi_2(s_i,s_j;c)
=\frac{1}{2\pi\sqrt{1-c^2}}
\exp\left[-\frac{s_i^2-2cs_is_j+s_j^2}{2(1-c^2)}\right].
\tag{3.3}
$$

The factor $1/\sqrt{1-c^2}$ is the Jacobian of the linear change from $(S,T)$ to $(X_i,X_j)$.

## 3.2. The matrix form and its continuity

It is useful to describe the same conditional law without choosing a moving orthonormal basis. Partition a Gaussian covariance according to a nondegenerate group of pinned coordinates and the remaining coordinates:

$$
G=\begin{pmatrix}A&B^\top\\ B&C\end{pmatrix},\qquad A\succ0.
$$

If the pinned coordinates have value $s$, then the remaining coordinates have conditional mean and covariance

$$
BA^{-1}s,\qquad C-BA^{-1}B^\top.
\tag{3.4}
$$

To verify the formula, subtract $BA^{-1}$ times the pinned vector from the remaining vector. The resulting Gaussian residual is uncorrelated with every pinned coordinate. In an ambient standard-Gaussian realization, its coefficient vectors are perpendicular to those of the pinned coordinates; orthogonal Gaussian coordinates are independent by the density factorization used above. Direct covariance calculation gives (3.4). It also proves that the residual covariance is positive semidefinite.

Both quantities in (3.4) depend continuously on the covariance entries while $A$ remains invertible. Conditional laws can therefore be coupled as

$$
\mu_m+C_m^{1/2}W\longrightarrow\mu+C^{1/2}W
\quad\text{almost surely},
\tag{3.5}
$$

where $W$ has a fixed standard Gaussian dimension. Section 1.5 proved the required square-root continuity. When a limiting event has no mass on any of its boundary hyperplanes, dominated convergence gives convergence of its probability. This observation, including its boundary qualification, will be used repeatedly.

## 3.3. Canonical two-coordinate boundary weights

From now on, fix $n\ge3$ and $t>0$, and initially assume distinct coordinates. For $-1<g_{ij}<1$, define

$$
q_{ij}(G,t)=\phi_2(t,t;g_{ij})
\mathbb P\{X_\ell\le t\ (\ell\ne i,j)\mid X_i=X_j=t\}.
\tag{3.6}
$$

The conditional law is exactly the one just constructed. We sometimes call this a **pair pin**: two scores are fixed at their common boundary value. The weight is a two-coordinate boundary density multiplied by the success probability of the remaining conditional scores. It is nonnegative and symmetric in $i,j$.

For an antipodal pair $g_{ij}=-1$, define

$$
q_{ij}(G,t)=0.
\tag{3.7}
$$

At a positive threshold the two equations $X_i=t$ and $X_j=t$ are incompatible for an antipodal pair. We will prove that zero is also the limiting value of (3.6). We do not assign an ordinary bivariate density to that singular pair.

The word **canonical** means that the weight is fixed by the actual covariance and threshold through (3.6)--(3.7). It is not a free parameter that can be replaced by another nonnegative number with a useful algebraic property.

## 3.4. A positive weight exists in every row

Some nonantipodal pair weights can be zero. Nevertheless, each row has a positive one.

**Lemma 3.1.** At distinct coordinates, for $n\ge3$ and $t>0$, choose $j\ne i$ maximizing $g_{ij}$ over that row. Then $-1<g_{ij}<1$ and $q_{ij}>0$.

**Proof.** The upper bound is distinctness. If the maximum were $-1$, every other normal would equal $-v_i$, giving repeated coordinates because $n\ge3$. Thus the pair is nonantipodal.

Formula (3.4) gives, for every $\ell\ne i,j$,

$$
\mathbb E[X_\ell\mid X_i=X_j=t]
=t\frac{g_{i\ell}+g_{j\ell}}{1+g_{ij}}<t.
\tag{3.8}
$$

Indeed, $g_{i\ell}\le g_{ij}$ by the choice of $j$, and $g_{j\ell}<1$ by distinctness. The denominator is positive, and $t>0$, so the strict inequality has the stated direction.

Subtract the conditional mean. All the remaining inequalities now have strictly positive upper bounds. In a standard-Gaussian realization of the conditional residual, a sufficiently small neighborhood of zero satisfies every inequality. That neighborhood has positive probability. If the residual is deterministic, the event instead has probability one. In either case the conditional probability in (3.6) is positive, as is the bivariate density. $\square$

In particular, the quantities

$$
k_i=\sum_{j\ne i}(1-g_{ij})q_{ij},\qquad
C_i=\sum_{j\ne i}\sqrt{1-g_{ij}^2}\,q_{ij}
\tag{3.9}
$$

are strictly positive for every $i$. Antipodal terms in these sums are zero. No minimizing or stationarity assumption was used.

# 4. Differentiating a Gaussian probability through singular covariances

This is the first analytic point where the full domain matters. A density calculation proves the derivative when the covariance is invertible. The optimizer is not invertible. We must therefore prove that the derivative extends to feasible perturbations of a singular covariance, including perturbations that change rank.

## 4.1. The positive-definite calculation and its normalization

Suppose first that $G\succ0$, and write $A=G^{-1}$. Its density on $\mathbb R^n$ is

$$
p_G(x)=(2\pi)^{-n/2}(\det G)^{-1/2}
\exp\left(-\frac12x^\top Ax\right).
$$

Vary the common symmetric entries $g_{ij},g_{ji}$ by one scalar parameter. If $E^{ij}$ has entries one at $(i,j)$ and $(j,i)$ and zero elsewhere, then this variation is $G+sE^{ij}$.

The elementary matrix differentiation identities are

$$
\left.\frac d{ds}(G+sE)^{-1}\right|_{s=0}=-G^{-1}EG^{-1},
\qquad
\left.\frac d{ds}\log\det(G+sE)\right|_{s=0}
=\operatorname{tr}(G^{-1}E).
$$

The first follows by differentiating $(G+sE)(G+sE)^{-1}=I$. For the second, write $\det(G+sE)=\det G\det(I+sG^{-1}E)$ and expand the determinant: its linear term is the trace. Applying these identities with $E=E^{ij}$ gives

$$
\frac{\partial p_G(x)}{\partial g_{ij}}
=\bigl((Ax)_i(Ax)_j-A_{ij}\bigr)p_G(x).
\tag{4.1}
$$

On the other hand, differentiating in the spatial coordinates gives exactly

$$
\partial_{x_i}\partial_{x_j}p_G(x)
=\bigl((Ax)_i(Ax)_j-A_{ij}\bigr)p_G(x).
\tag{4.2}
$$

There is no factor $1/2$ in (4.1): the one correlation parameter changes both symmetric entries.

In a sufficiently small positive-definite neighborhood of $G$, the covariance eigenvalues are bounded above and bounded away from zero. The density derivatives are then bounded in absolute value by a fixed polynomial in $|x|$ times $e^{-c|x|^2}$ for some $c>0$. That is integrable. We may differentiate under the integral defining $F_G(t)$.

Integrate (4.2) first in $x_i$, then in $x_j$, over their intervals $(-\infty,t]$. The Gaussian density and its first derivatives vanish at minus infinity. Fubini and integration by parts therefore give

$$
\begin{aligned}
\frac{\partial F_G(t)}{\partial g_{ij}}
&=\int_{x_\ell\le t,\ \ell\ne i,j}
 p_G(t,t,x_{-ij})\,dx_{-ij}\\
&=q_{ij}(G,t).
\end{aligned}
\tag{4.3}
$$

Here $x_{-ij}$ denotes the list of coordinates other than $i,j$. The last equality is the density factorization into a bivariate density and the corresponding conditional law.

The nonnegative sign in (4.3) says that increasing a single feasible correlation increases this common-threshold probability. But arbitrary correlation matrices cannot be compared entry by entry with $\Delta_n$; that obstacle will be discussed in Section 12.

## 4.2. Why the conditional event has no boundary atom

Fix a possibly singular, distinct-coordinate $G$ and a nonantipodal pair $i,j$. In (3.4) its two by two pinned covariance is invertible, so the remaining conditional mean and covariance vary continuously with $G$.

To conclude continuity of the conditional probability in (3.6), we must rule out positive mass on a remaining threshold. A one-dimensional Gaussian puts positive mass at a single point only if its variance is zero. In the Gram representation, zero conditional variance of coordinate $\ell$ means

$$
v_\ell=\alpha v_i+\beta v_j
$$

for some real $\alpha,\beta$. At the pair pin its deterministic value is $(\alpha+\beta)t$. For this value to equal $t$, positivity of $t$ forces $\alpha+\beta=1$. The unit-length condition then gives

$$
1=|v_\ell|^2
=\alpha^2+\beta^2+2\alpha\beta g_{ij}
=1-2\alpha\beta(1-g_{ij}).
\tag{4.4}
$$

Since $g_{ij}<1$, we obtain $\alpha\beta=0$. Together with $\alpha+\beta=1$, this makes $v_\ell$ equal to $v_i$ or $v_j$, a repeated coordinate. It is excluded.

Thus every remaining conditional threshold has probability zero. Their finite union also has probability zero, even if the joint residual is singular. The coupling argument (3.5), followed by dominated convergence, now proves continuity of the conditional probability in (3.6). The bivariate density is continuous while $g_{ij}>-1$, so $q_{ij}$ is continuous there as well.

Notice the exact role of the hypotheses. The equal threshold and $t>0$ turn the deterministic boundary equation into $\alpha+\beta=1$. Unit lengths then turn that affine relation into a duplicate. A general singular Gaussian boundary event need not have this property.

## 4.3. The antipodal limit

For $-1<c<1$, the conditional probability in (3.6) is at most one, and (3.3) gives

$$
0\le q_{ij}(G,t)\le
\frac{1}{2\pi\sqrt{1-c^2}}
\exp\left(-\frac{t^2}{1+c}\right),\qquad c=g_{ij}.
\tag{4.5}
$$

As $c\downarrow-1$, the exponential tends to zero faster than the square-root factor can diverge. For example, put $u=1/(1+c)$; the relevant factor is bounded by a constant times $\sqrt u\,e^{-t^2u}$, which tends to zero. This can also be seen by bounding $e^{t^2u}$ below by any fixed power of $t^2u$ from its power series.

Consequently the definition $q_{ij}=0$ at an antipodal pair makes every pair weight continuous on the distinct-coordinate part of $\mathcal E_n$. The estimate is uniform when $t$ lies in a compact interval contained in $(0,\infty)$.

We have not proved continuity at a duplicate, or at an antipodal pair with threshold zero. Neither assertion will be used.

## 4.4. Regularization proves the relative differential

**Proposition 4.1.** Fix $t>0$ and a distinct-coordinate $G\in\mathcal E_n$. As $\widehat G\to G$ through correlation matrices,

$$
F_{\widehat G}(t)-F_G(t)
=\sum_{i<j}q_{ij}(G,t)(\widehat g_{ij}-g_{ij})
+o(\|\widehat G-G\|).
\tag{4.6}
$$

Any matrix norm can be used; all norms are equivalent in this fixed finite-dimensional space. The little-$o$ means that the remainder divided by $\|\widehat G-G\|$ tends to zero. The expansion is **relative to the domain** $\mathcal E_n$: it concerns feasible covariance increments, not an extension to arbitrary nonpositive matrices.

**Proof.** For $0<\varepsilon<1$, define

$$
G_\varepsilon=(1-\varepsilon)G+\varepsilon I,
\qquad
\widehat G_\varepsilon=(1-\varepsilon)\widehat G+\varepsilon I.
$$

Both are positive definite. Apply (4.3) along the segment between them:

$$
\begin{aligned}
F_{\widehat G_\varepsilon}(t)-F_{G_\varepsilon}(t)
=(1-\varepsilon)\int_0^1
\sum_{i<j}q_{ij}((1-s)G_\varepsilon+s\widehat G_\varepsilon,t)
(\widehat g_{ij}-g_{ij})\,ds.
\end{aligned}
\tag{4.7}
$$

Because the coordinates of $G$ are distinct, all its off-diagonal entries are bounded above by $1-\eta$ for some $\eta>0$. For $\widehat G$ sufficiently close to $G$ and $\varepsilon$ sufficiently small, all the matrices in (4.7) remain in a compact subset of $\mathcal E_n$ whose off-diagonal entries stay strictly below one. Sections 4.2--4.3 show that the $q_{ij}$ are continuous there, including at antipodal pairs. They are therefore bounded and uniformly continuous on that compact set.

Let $\varepsilon\downarrow0$ in (4.7). Joint CDF continuity from (1.12) handles the left side, and bounded convergence handles the integral. We obtain

$$
F_{\widehat G}(t)-F_G(t)
=\int_0^1\sum_{i<j}q_{ij}((1-s)G+s\widehat G,t)
(\widehat g_{ij}-g_{ij})\,ds.
\tag{4.8}
$$

Subtract the linear expression in (4.6). Its absolute error is bounded by

$$
\sum_{i<j}|\widehat g_{ij}-g_{ij}|
\sup_{0\le s\le1}|q_{ij}((1-s)G+s\widehat G,t)-q_{ij}(G,t)|.
$$

The supremum tends to zero, and the finite sum of the increments is bounded by a constant times $\|\widehat G-G\|$. This proves (4.6). $\square$

The argument has not replaced a singular variation by a variation of the same rank. It proves the first-order formula for the actual feasible increment, including a rank increase. That is precisely the form needed at the boundary of the correlation-matrix domain.

# 5. Moving boundary locations and lowering the number of scores

## 5.1. A differentiability lemma for Gaussian halfspace intersections

A halfspace with unit normal $w$ and boundary location $b$ is $\{y:w\cdot y\le b\}$. In convex geometry $b$ is called a **support number** for that listed inequality. We use this term even if the inequality is redundant, meaning its removal would not change the intersection.

**Lemma 5.1 (differentiation in support numbers).** Let $w_1,\ldots,w_m$ be fixed unit vectors in $\mathbb R^p$, where $p\ge1$, and set

$$
h(b)=\mathbb P\{w_j\cdot Y\le b_j\text{ for every }j\},
\qquad Y\sim N(0,I_p).
$$

Suppose that at $b=b^0$ no two of the listed boundary hyperplanes coincide. Explicitly, if $w_k=w_j$, assume $b_k^0\ne b_j^0$; if $w_k=-w_j$, assume $b_k^0\ne-b_j^0$. Then $h$ is continuously differentiable in a neighborhood of $b^0$, and

$$
\partial_jh(b^0)=\phi(b_j^0)
\mathbb P\{w_k\cdot Y\le b_k^0\ (k\ne j)
\mid w_j\cdot Y=b_j^0\}.
\tag{5.1}
$$

**Proof.** Put $Z=w_j\cdot Y$. By orthogonal decomposition, conditional on $Z=s$,

$$
w_k\cdot Y=(w_k\cdot w_j)s+R_k,
$$

where the centered Gaussian residual vector $R$ is independent of $s$, and $\operatorname{Var}(R_k)=1-(w_k\cdot w_j)^2$.

If this variance is positive, the $k$th conditional coordinate has no atom at its threshold. If it is zero, then $w_k=\pm w_j$, and the noncoincidence hypothesis says that its deterministic value at $s=b_j^0$ is different from $b_k^0$. The same strict separation holds for nearby supports and nearby $s$.

It follows by dominated convergence, using this fixed residual realization, that

$$
(s,b_{-j})\longmapsto
\mathbb P\{w_k\cdot Y\le b_k\ (k\ne j)\mid Z=s\}
$$

is continuous near $(b_j^0,b_{-j}^0)$. Indeed, outside a conditional null set each of the finitely many limiting inequalities is strict on one side or the other, so its indicator is eventually constant.

Conditioning on $Z$ writes $h(b)$ as the integral of this conditional probability against $\phi(s)$ over $s\le b_j$. The one-variable fundamental theorem of calculus gives (5.1), and the derivative is continuous in all the support variables near $b^0$.

This works for every $j$. Continuous partial derivatives on a common open neighborhood imply differentiability. One can check the last statement directly by changing the coordinates of $b$ one at a time: integrate each continuous partial derivative along that coordinate segment, subtract its value at $b^0$, and bound the error by $\|b-b^0\|$ times the maximum oscillation of the partial derivatives. That oscillation tends to zero. $\square$

The proof does not require every constraint to describe a genuine face of codimension one. An inactive constraint has derivative zero. A constraint that touches the region only in a smaller-dimensional set can also have derivative zero. In dimension one, hyperplanes are points, and the same proof applies.

## 5.2. The derivative of the common threshold

Apply Lemma 5.1 to the original normals $v_1,\ldots,v_n$ at supports $t\mathbf1$. Distinct equal-direction normals do not occur. Antipodal normals have hyperplanes at opposite locations, which do not coincide because $t>0$. Thus the fixed-covariance profile is continuously differentiable at every positive threshold, and

$$
F_G'(t)=\phi(t)\sum_{i=1}^n H_i,
\qquad
H_i=\mathbb P\{X_j\le t\ (j\ne i)\mid X_i=t\}.
\tag{5.2}
$$

This is the precise meaning of the boundary-mass calculation: increasing every threshold adds the first-order contributions from all the listed faces. The lemma proves the formula without assuming that the ambient $n$-coordinate law has a density and without using a general surface-variation theorem.

The conditional quantities $H_i(G,t)$ are also jointly continuous at distinct-coordinate covariances and positive thresholds, even through changes of rank. In (3.4), pin only $X_i=t$. A remaining conditional variance can vanish only when $g_{ij}=\pm1$. The value $+1$ is excluded; at $-1$ its deterministic conditional value is $-t<t$. Hence every remaining threshold is a conditional null boundary. Formula (3.5) proves the stated continuity. Together with (5.2), this gives joint continuity of the threshold derivative on this domain. We will use it in the envelope explanation in Section 11.

## 5.3. The actual conditional region

Assume now that $r=\operatorname{rank}G\le n-1$. Realize the normals in $\mathbb R^{n-1}$ by adding zero coordinates to an intrinsic realization. Let $Z$ be standard Gaussian in this larger space. The added independent coordinates do not enter any score, so the score law is unchanged.

For each fixed $i$, conditional on $v_i\cdot Z=t$, write

$$
Z=tv_i+Y,\qquad Y\sim N(0,I_{v_i^\perp}).
$$

The tangent space $v_i^\perp$ has the common dimension

$$
d=n-2\ge1.
\tag{5.3}
$$

For a nonantipodal $j\ne i$, define

$$
\sigma_{ij}=\sqrt{1-g_{ij}^2},\qquad
w_{ij}=\frac{v_j-g_{ij}v_i}{\sigma_{ij}},\qquad
b_{ij}=\frac{t(1-g_{ij})}{\sigma_{ij}}
=t\sqrt{\frac{1-g_{ij}}{1+g_{ij}}}.
\tag{5.4}
$$

The vector $w_{ij}$ is a unit vector in $v_i^\perp$. The original inequality $v_j\cdot Z\le t$ becomes

$$
w_{ij}\cdot Y\le b_{ij}.
$$

An antipodal normal gives $v_j\cdot Z=-t<t$, so its conditional constraint is automatic and is omitted. All retained supports $b_{ij}$ are strictly positive.

Let $b_i$ denote the vector of these actual supports, and let

$$
Q_i(b)=\{y\in v_i^\perp:w_{ij}\cdot y\le b_j
\text{ for all retained }j\},\qquad
h_i(b)=\gamma_d(Q_i(b)).
\tag{5.5}
$$

Then $H_i=h_i(b_i)$. When no argument is displayed, $Q_i$ means the actual region $Q_i(b_i)$.

The word **facet** will mean the part of $K_t$ lying in a hyperplane $v_i\cdot z=t$. Translating that facet by $-tv_i$ produces the region $Q_i$ in its tangent space. Even if there are redundant projected inequalities, $Q_i$ contains an open ball about zero: take its radius smaller than the least retained support. It may be unbounded. The Gaussian construction so far has not supplied a positive relation among the normals or a boundedness theorem.

There are at most $n-1$ retained constraints. This is how conditioning lowers the number of scores. The supports are not all equal, however. The support inequality in Section 6 will compare this actual region with an equal-support reference, while using derivatives only at the actual region.

## 5.4. No tied hyperplanes at the actual supports

To use Lemma 5.1, we must check the projected constraints, not only the original ones.

If two projected unit normals coincide and have equal actual supports, the strictly decreasing function

$$
c\longmapsto t\sqrt{\frac{1-c}{1+c}},\qquad -1<c<1,
$$

forces their correlations with $v_i$ to agree. Reconstructing each original vector as

$$
v_j=g_{ij}v_i+\sqrt{1-g_{ij}^2}\,w_{ij}
$$

would then make the original vectors equal, a contradiction. Oppositely directed projected normals can define the same hyperplane only at opposite supports, which is impossible when both supports are positive. Thus Lemma 5.1 applies at $b_i$.

This does not say that all projected directions are different. Consider, for example,

$$
v_0=(1,0),\quad v_1=(0,1),\quad v_2=(3/5,4/5),
\quad v_3=(-1,0),\quad v_4=(0,-1).
$$

Conditioning on $v_0\cdot Z=t$ leaves the tangent inequalities

$$
y\le t,\qquad y\le t/2,\qquad -y\le t,
$$

and an automatic antipodal constraint. The first two projected directions coincide, but the actual supports differ; the first inequality is inactive. At an equal-support reference the first two would be tied. The corresponding probability function need not be differentiable there. None of our arguments will differentiate there.

## 5.5. The exact identity between support and covariance derivatives

The support derivative (5.1) on the conditional region is

$$
\partial_{b_{ij}}h_i(b_i)=\phi(b_{ij})
\mathbb P\{X_\ell\le t\ (\ell\ne i,j)\mid X_i=X_j=t\}.
$$

By the orthogonal decomposition (3.2),

$$
\phi_2(t,t;g_{ij})
=\frac{\phi(t)\phi(b_{ij})}{\sigma_{ij}}.
$$

The conditional residual law on the two sides is the same: one first pins $X_i$, then its standardized residual score for $X_j$, which is exactly the orthogonal pair conditioning already constructed. Comparing with (3.6) proves

$$
\boxed{\partial_{b_{ij}}h_i(b_i)
=\frac{\sigma_{ij}q_{ij}}{\phi(t)}.}
\tag{5.6}
$$

We now have two useful directional support derivatives:

$$
\boxed{
\begin{aligned}
\sum_j b_{ij}\partial_{b_{ij}}h_i(b_i)&=\frac{tk_i}{\phi(t)},\\
\sum_j\partial_{b_{ij}}h_i(b_i)&=\frac{C_i}{\phi(t)}.
\end{aligned}}
\tag{5.7}
$$

The sums range over the retained constraints. Terms omitted at antipodal pairs would be zero in $k_i,C_i$ anyway. The first identity follows from $b_{ij}\sigma_{ij}=t(1-g_{ij})$; the second is the definition of $C_i$.

Since every actual support is proportional to $t$, (5.7) also proves

$$
\frac d{dt}H_i(G,t)=\frac{k_i(G,t)}{\phi(t)}>0.
\tag{5.8}
$$

In (5.8) the covariance is fixed. The coefficient $q_{ij}$, and therefore $k_i$, may depend on $t$; no derivative of them is needed for this first derivative.

The compatibility is now explicit. The same $q_{ij}$ measures a covariance change in (4.6) and a support change in (5.6). The next section explains why the support probability has a useful tangent bound, and Section 7 computes its scaling derivative exactly.

# 6. Why Gaussian probability is log-concave in its support numbers

The next fact is often quoted as a theorem about log-concave integrals. Here we prove the version needed for Gaussian halfspace intersections, including unbounded intersections and fibers with zero mass.

## 6.1. Concavity, log-concavity, and tangent inequalities

A function $L$ on a convex set is **concave** if

$$
L((1-\theta)x+\theta y)\ge(1-\theta)L(x)+\theta L(y)
\quad(0\le\theta\le1).
$$

A nonnegative function $f$ is **log-concave** if

$$
f((1-\theta)x+\theta y)\ge f(x)^{1-\theta}f(y)^\theta
\quad(0<\theta<1).
\tag{6.1}
$$

Zeros are allowed. If either factor on the right is zero, the right side is zero. On its positive set, log-concavity says that $\log f$ is concave. Its positive set is convex, since the right side of (6.1) is positive between two points where $f$ is positive.

The Gaussian density is log-concave because

$$
|(1-\theta)x+\theta y|^2
=(1-\theta)|x|^2+\theta|y|^2-\theta(1-\theta)|x-y|^2.
\tag{6.2}
$$

An indicator of a convex set is log-concave. Products of log-concave functions are log-concave, by multiplying their defining inequalities. Thus a Gaussian density restricted to a convex region is log-concave, even when the region is unbounded or not symmetric.

A differentiable concave function lies below its tangent:

$$
L(c)\le L(b)+\nabla L(b)\cdot(c-b).
\tag{6.3}
$$

To verify (6.3), apply concavity at $b+s(c-b)$, rearrange to bound $L(c)-L(b)$ by $[L(b+s(c-b))-L(b)]/s$, and let $s\downarrow0$. For a convex function the inequality reverses. Only the tangent at $b$ needs to exist; differentiability at $c$ is irrelevant.

## 6.2. The one-dimensional integral inequality

**Lemma 6.1.** Let $f,g,h:\mathbb R\to[0,\infty)$ be finite measurable log-concave functions, each bounded above by a finite constant times $e^{-x^2/2}$. Fix $0<\theta<1$, and suppose

$$
h((1-\theta)x+\theta y)\ge f(x)^{1-\theta}g(y)^\theta
\quad\text{for all }x,y\in\mathbb R.
\tag{6.4}
$$

Then

$$
\int_{\mathbb R}h\ge
\left(\int_{\mathbb R}f\right)^{1-\theta}
\left(\int_{\mathbb R}g\right)^\theta.
\tag{6.5}
$$

**Proof.** If either integral on the right is zero, the conclusion is immediate. Otherwise divide $f,g$ by their respective integrals and divide $h$ by the product of those integrals with exponents $1-\theta,\theta$. It suffices to prove the assertion when $f$ and $g$ are probability densities.

Their positive sets have interval interiors $I_f,I_g$ of positive length. On such an interior, the logarithm of the density is a finite concave function and is continuous. To see the needed elementary continuity, let $L$ be finite and concave and choose $a<x_0<b$ in its interval. For $x_0<x<b$, concavity gives

$$
\frac{L(b)-L(x_0)}{b-x_0}(x-x_0)
\le L(x)-L(x_0)
\le\frac{L(x_0)-L(a)}{x_0-a}(x-x_0).
$$

The analogous bounds hold to the left of $x_0$. They force $L(x)\to L(x_0)$. Applying this to $\log f$ and $\log g$ proves continuity and strict positivity of the densities on their interval interiors. Endpoint values do not affect any integral.

Let

$$
F(x)=\int_{-\infty}^x f(s)\,ds,\qquad
G_0(y)=\int_{-\infty}^y g(s)\,ds.
$$

On $I_f$ and $I_g$, these are continuously differentiable, strictly increasing maps onto $(0,1)$. Define the increasing matching map

$$
T(x)=G_0^{-1}(F(x)),\qquad x\in I_f.
$$

It sends equal cumulative probabilities to one another. Differentiating the inverse function gives

$$
T'(x)=\frac{f(x)}{g(T(x))}>0.
\tag{6.6}
$$

The map $z(x)=(1-\theta)x+\theta T(x)$ is also continuously differentiable and strictly increasing. A change of variables over its image, followed by (6.4), gives

$$
\begin{aligned}
\int_{\mathbb R}h(z)\,dz
&\ge\int_{I_f}h((1-\theta)x+\theta T(x))
       [(1-\theta)+\theta T'(x)]\,dx\\
&\ge\int_{I_f}f(x)^{1-\theta}g(T(x))^\theta
       [(1-\theta)+\theta T'(x)]\,dx.
\end{aligned}
\tag{6.7}
$$

The elementary weighted arithmetic--geometric mean inequality says

$$
(1-\theta)+\theta r\ge r^\theta\qquad(r>0).
$$

For example, it follows by applying concavity of $\log$ to the numbers $1,r$; that concavity follows from $(\log r)''=-1/r^2<0$. Use it with $r=T'(x)$ in (6.7), and then use (6.6). The last integral is at least

$$
\int_{I_f}f(x)^{1-\theta}g(T(x))^\theta
\left(\frac{f(x)}{g(T(x))}\right)^\theta dx
=\int_{I_f}f(x)\,dx=1.
$$

All the changes of variables can first be made on compact subintervals of $I_f$, where the maps are ordinary continuously differentiable changes of variable. Increasing those subintervals to $I_f$ and using monotone convergence justifies infinite endpoints and the full displayed integrals. Undoing the normalization proves (6.5). $\square$

The map $T$ is only a proof device for this one-dimensional integral inequality. No transport map on the Gaussian covariance domain is being constructed.

## 6.3. Integrating one coordinate at a time

**Proposition 6.2 (the required log-concave integral theorem).** Let $f,g,h:\mathbb R^p\to[0,\infty)$ be finite measurable log-concave functions. Suppose each is bounded by a finite constant times $e^{-|x|^2/2}$. If (6.4) holds in $\mathbb R^p$, then (6.5) holds with integrals over $\mathbb R^p$.

**Proof.** We induct on $p$, with Lemma 6.1 as the base. Write a point of $\mathbb R^p$ as $(x',s)$, where $x'\in\mathbb R^{p-1}$. Define the marginal functions

$$
F_1(x')=\int_{\mathbb R}f(x',s)\,ds,\quad
G_1(y')=\int_{\mathbb R}g(y',s)\,ds,\quad
H_1(z')=\int_{\mathbb R}h(z',s)\,ds.
$$

All are finite and measurable. The Gaussian domination bounds them by constants times $e^{-|x'|^2/2}$, so they remain integrable.

Fix $x',y'$. Apply Lemma 6.1 to the three one-dimensional fibers at $x'$, $y'$, and $(1-\theta)x'+\theta y'$. The original pointwise interpolation inequality supplies its hypothesis. If either of the first two fiber integrals is zero, the desired conclusion is simply nonnegativity. Otherwise the lemma gives

$$
H_1((1-\theta)x'+\theta y')
\ge F_1(x')^{1-\theta}G_1(y')^\theta.
\tag{6.8}
$$

The marginals themselves are log-concave. For example, use two fibers of $f$ as the first two one-dimensional functions and its interpolated fiber as the third. Log-concavity of $f$ supplies (6.4), and Lemma 6.1 gives exactly log-concavity of $F_1$. The same argument works for $G_1,H_1$, including zero fibers.

The induction hypothesis in dimension $p-1$ now applies to (6.8). Fubini--Tonelli identifies its integrals with those of the original functions and proves the result. $\square$

The domination assumption is deliberately tailored to the application. It keeps every fiber and every marginal finite. We have not invoked a more general theorem for arbitrary measurable functions or an unproved approximation of such functions.

## 6.4. Application to support probabilities

Fix unit normals $w_1,\ldots,w_m$ and write

$$
Q(b)=\{y:w_j\cdot y\le b_j\text{ for every }j\},\qquad
h(b)=\gamma_p(Q(b)).
$$

If $x\in Q(b)$ and $y\in Q(c)$, then

$$
(1-\theta)x+\theta y\in Q((1-\theta)b+\theta c).
$$

Combine this inclusion with (6.2). The three functions consisting of the Gaussian density restricted to these three regions satisfy the hypothesis of Proposition 6.2. Therefore

$$
h((1-\theta)b+\theta c)\ge h(b)^{1-\theta}h(c)^\theta.
\tag{6.9}
$$

Thus $h$ is log-concave in the support vector. The proof is valid for unbounded regions: all restricted densities are still dominated by the Gaussian density. A support vector with zero mass causes no difficulty in (6.9). In our use, both support vectors have strictly positive entries and the whole segment between them contains a ball, so all masses along that segment are positive.

The reciprocal is consequently convex. Indeed, taking reciprocals in (6.9) and then applying the arithmetic--geometric mean inequality gives

$$
\frac1{h((1-\theta)b+\theta c)}
\le\frac1{h(b)^{1-\theta}h(c)^\theta}
\le\frac{1-\theta}{h(b)}+\frac\theta{h(c)}.
\tag{6.10}
$$

We will use (6.10) in the main proof and the concavity of $\log h$ in the alternative proof. Both come from the same integral theorem.

## 6.5. Why taking a reciprocal helps

A comparison of $h(b)$ and $h(c)$ directly would not reveal the normalized derivative that occurs in the scalar lemma. Differentiating $1/h$ at an actual support vector produces $-\nabla h/h^2$. Its tangent inequality, after multiplication by $h^2$, gives a difference of the form $h^2/p-h$. That is exactly the quadratic expression needed in (2.5).

Similarly, the tangent inequality for $\log h$ gives $h\log(h/p)$. That expression is designed to interact with the logarithmic addition rule proved in Section 10.

The reciprocal and logarithm are therefore not different probability laws, changes of threshold, or new normalizations of the Gaussian vector. They are functions of the same support probability, chosen to expose useful algebra in its tangent inequality.

# 7. Gaussian scaling and the positive energy in each component

## 7.1. Dilating the actual region

Continue with a distinct-coordinate covariance of rank at most $n-1$, and use the padded tangent dimension $d=n-2$. For one of its actual conditional regions $Q_i=Q_i(b_i)$, simultaneous multiplication of every support by $s>0$ gives

$$
Q_i(sb_i)=sQ_i.
$$

Changing variables $y=sz$ therefore gives

$$
h_i(sb_i)=\gamma_d(sQ_i)=\int_{Q_i}s^d\phi_d(sy)\,dy.
\tag{7.1}
$$

The factor $s^d$ records expansion of volume; the Gaussian density factor decreases as points are moved farther from zero. Differentiate their product:

$$
\frac d{ds}\bigl[s^d\phi_d(sy)\bigr]
=s^{d-1}(d-s^2|y|^2)\phi_d(sy).
$$

For $1/2\le s\le3/2$, its absolute value is at most

$$
C_d(1+|y|^2)e^{-|y|^2/8}
$$

for a constant $C_d$ depending only on $d$. This is integrable on all of $\mathbb R^d$. Dominated convergence justifies differentiation under the integral even if $Q_i$ is unbounded. Evaluating at $s=1$ gives

$$
\left.\frac d{ds}h_i(sb_i)\right|_{s=1}
=dH_i-\int_{Q_i}|y|^2\,d\gamma_d(y).
\tag{7.2}
$$

The support derivative also computes the left side, and (5.7) identifies it as $tk_i/\phi(t)$. Hence

$$
\boxed{
H_i=\frac{tk_i}{d\phi(t)}+
\frac1d\int_{Q_i}|y|^2\,d\gamma_d(y).
}
\tag{7.3}
$$

This is the exact identity that turns a geometric calculation into the positive decomposition required by Lemma 2.1.

## 7.2. Pressure and energy are parts of the same mass

Define

$$
u_i=\frac{tk_i}{d\phi(t)},\qquad
 e_i=\frac1d\int_{Q_i}|y|^2\,d\gamma_d(y).
\tag{7.4}
$$

Thus $H_i=u_i+e_i$. Both terms are strictly positive. Positivity of $u_i$ follows from $t>0$, $k_i>0$, and $d\ge1$. The region $Q_i$ contains a ball about zero, so it contains a positive-volume set of points with $|y|>0$; the integrand in the energy integral is positive there. This proves $e_i>0$.

The symbol $u_i$ is a scalar, not a unit normal. We call it the **pressure part** of the conditional mass because, by (5.8),

$$
u_i=\frac t d H_i'(t).
\tag{7.5}
$$

It is the dimension-normalized rate of expansion of this same conditional region. The symbol $e_i$ is its remaining energy part. The terminology is only a mnemonic for (7.3)--(7.5); no physical model is assumed.

Set

$$
\kappa=\sum_i k_i,\qquad a_i=\frac{k_i}{\kappa},\qquad
U=\sum_i u_i.
$$

The common factor in (7.4) proves the crucial agreement

$$
\boxed{a_i=\frac{u_i}{U}.}
\tag{7.6}
$$

The same normalized weights describe the row sums of the Gaussian covariance derivative and the pressure portions of the conditional masses. An independently chosen kernel vector would not automatically satisfy (7.6).

No uniform lower bound for $e_i$ is claimed as the threshold goes to zero or as the covariance degenerates. The proof needs strict positivity at the particular positive threshold and covariance being examined. It will never divide by an asserted uniform energy bound.

## 7.3. What the unused Gaussian coordinates contribute

Let the intrinsic rank be $r$, and put $d_0=r-1$. Before padding, the conditional region lies in an intrinsic tangent space of dimension $d_0$. Call it $P_i$. After padding,

$$
Q_i=P_i\times\mathbb R^{d-d_0}.
$$

Gaussian product structure gives

$$
\int_{Q_i}|y|^2\,d\gamma_d(y)
=\int_{P_i}|y|^2\,d\gamma_{d_0}(y)+(d-d_0)H_i.
\tag{7.7}
$$

Each unused standard normal coordinate contributes its second moment, one, multiplied by the probability of the constrained event. The identity $\int x^2\phi(x)\,dx=1$ follows, for instance, by integrating $-x\phi'(x)$ and using the vanishing boundary term.

Thus the intrinsic form of the remainder is

$$
e_i=\frac{(d-d_0)H_i+\int_{P_i}|y|^2\,d\gamma_{d_0}(y)}d.
\tag{7.8}
$$

The extra term is not an error or an approximation. It is exactly the Gaussian energy in the unused directions. Padding lets all facets use the common dimension $d=n-2$, which is the dimension of a regular reference facet.

For a concrete example, take four normals $e_1,e_2,-e_1,-e_2$ in an intrinsic plane. Pin one score at $t$. Intrinsically the tangent region is $[-t,t]$. In the padded tangent plane it is $[-t,t]\times\mathbb R$. If $H=2\Phi(t)-1$, then

$$
\int_{[-t,t]}y^2\phi(y)\,dy=H-2t\phi(t),
$$

so the padded energy is $2H-2t\phi(t)$. Formula (7.3), with $d=2$, gives $u=t\phi(t)$ and $e=H-t\phi(t)$. Dropping the unused-coordinate contribution would produce a different, incorrect split.

## 7.4. An unbounded conditional region really can occur

Take three normals in $\mathbb R^2$:

$$
v_0=(1,0),\qquad v_1=(0,1),\qquad v_2=(-3/5,4/5).
$$

After pinning the first score at $t>0$, the two remaining inequalities are $y\le t$ and $y\le2t$. Thus the actual tangent region is $(-\infty,t]$, not a bounded interval. Its mass and energy are

$$
H_0=\Phi(t),\qquad
\int_{-\infty}^t y^2\phi(y)\,dy=\Phi(t)-t\phi(t).
$$

Only the first of the two projected constraints is active, so $k_0=\phi(t)^2$. With $d=1$, (7.3) becomes

$$
\Phi(t)=t\phi(t)+[\Phi(t)-t\phi(t)].
$$

Every term has its asserted meaning and sign. This covariance need not be a minimizer or satisfy the finite directional tests introduced next. The example shows why the shared support and energy calculus should not be proved only for bounded regions.

# 8. The main boundary theorem: finite covariance tests and reciprocal probability

## 8.1. Feasible variations that respect unit variances

We now use a covariance that is a minimum, or more generally satisfies certain necessary inequalities for being a minimum. The constraints are important: arbitrary changes of inner products may destroy positive semidefiniteness or change the diagonal.

Define the symmetric matrix

$$
S_{ij}=q_{ij}\quad(i\ne j),\qquad
S_{ii}=-\sum_{j\ne i}g_{ij}q_{ij}.
\tag{8.1}
$$

This matrix organizes the first variation subject to unit variances. It is often called a **stress matrix**. The name supplies no extra property: at a general configuration $S$ need not be positive semidefinite. Its row sums are exactly

$$
(S\mathbf1)_i=k_i.
\tag{8.2}
$$

Fix a positive-semidefinite matrix $L$ at the current covariance and consider the one-sided path

$$
G_s=D_s(G+sL)D_s,\qquad
(D_s)_{ii}=(1+sL_{ii})^{-1/2},\qquad s\ge0.
\tag{8.3}
$$

The matrix $G+sL$ is positive semidefinite, and conjugation by the positive diagonal matrix $D_s$ preserves that property. Its $i$th diagonal entry after conjugation is one. Thus $G_s\in\mathcal E_n$.

Differentiating entries at $s=0$ gives

$$
\left.\frac d{ds}(G_s)_{ij}\right|_{0+}
=L_{ij}-\frac{g_{ij}}2(L_{ii}+L_{jj}).
$$

Substitute this into the relative differential (4.6). Group the diagonal normalization terms according to their index. The result is

$$
\boxed{\left.\frac d{ds}F_{G_s}(t)\right|_{0+}
=\frac12\operatorname{tr}(SL).}
\tag{8.4}
$$

For $L=zz^\top$, (8.3) has a particularly simple probability interpretation. Add one independent standard Gaussian $W$ to the realization and replace each score by

$$
\frac{X_i+\sqrt s\,z_iW}{\sqrt{1+sz_i^2}}.
$$

The denominator restores its variance to one. The resulting covariance is exactly (8.3). This construction can increase rank. That is allowed in the full correlation-matrix domain and is one reason not to restrict the problem prematurely to a fixed-rank family.

At a local minimum of $G\mapsto F_G(t)$, every feasible one-sided derivative (8.4) is nonnegative. The main proof will use just $n$ specific choices of $z$.

## 8.2. Why these particular directions are selected

Recall $k_i>0$, $\kappa=\sum_i k_i>0$, and $a_i=k_i/\kappa$. Let $f_i$ now denote the $i$th standard coordinate vector of $\mathbb R^n$; this vector is unrelated to the scalar energy $e_i$.

For a scalar $b$, the quadratic form along $f_i-b\mathbf1$ is

$$
(f_i-b\mathbf1)^\top S(f_i-b\mathbf1)
=S_{ii}-2bk_i+b^2\kappa.
$$

As a function of $b$, this is minimized at $b=k_i/\kappa=a_i$. Completing the square makes the choice transparent. Freeze

$$
z_i=f_i-a_i\mathbf1.
$$

At a minimum, the feasible rank-one test $L=z_iz_i^\top$ gives

$$
\boxed{\eta_i:=z_i^\top Sz_i
=S_{ii}-\frac{k_i^2}{\kappa}\ge0.}
\tag{8.5}
$$

These are the finite directional inequalities used by the main proof. We have not assumed $S\succeq0$, $GS=0$, $Ga=0$, or boundedness of the intrinsic region. A true full-domain minimum supplies (8.5), but the boundary theorem below will only need the displayed inequalities themselves.

The weights $a_i$ arose because they optimize a simple common-vector subtraction in the quadratic form. They are not imposed as a symmetry assumption. In particular, they are not assumed to equal $1/n$.

## 8.3. From the covariance tests to a signed row inequality

Cauchy--Schwarz applied to the two lists

$$
\left(\sqrt{(1-g_{ij})q_{ij}}\right)_{j\ne i},
\qquad
\left(\sqrt{(1+g_{ij})q_{ij}}\right)_{j\ne i}
$$

gives

$$
\begin{aligned}
C_i^2
&\le k_i\sum_{j\ne i}(1+g_{ij})q_{ij}\\
&=k_i(k_i-2S_{ii})\\
&\le k_i^2(1-2a_i).
\end{aligned}
\tag{8.6}
$$

For the middle identity, use (8.1) and the definition of $k_i$. For the last inequality, use $S_{ii}\ge k_i^2/\kappa=k_i a_i$ from (8.5).

Since $C_i,k_i>0$, (8.6) implies

$$
0<a_i<\frac12,\qquad
A_i:=\frac{C_i}{k_i}\le\sqrt{1-2a_i}.
\tag{8.7}
$$

Put

$$
d=n-2,\qquad A_*=\sqrt{\frac dn},\qquad
\rho=\frac t{A_*}=t\sqrt{\frac n{n-2}}.
\tag{8.8}
$$

The value $A_*$ is the value of the right side of (8.7) at uniform weights $a_i=1/n$. It also corresponds to the standardized threshold in a regular conditional facet, as we will calculate in Section 9.

For $z>-1$,

$$
\sqrt{1+z}\le1+\frac z2.
$$

This follows from concavity of the square root, or directly from
$1+z/2-\sqrt{1+z}=(\sqrt{1+z}-1)^2/2$. Apply it with $z=-2(na_i-1)/d$. The argument $1+z$ is positive by (8.7). We obtain

$$
\frac{A_i}{A_*}
\le\sqrt{1-\frac{2(na_i-1)}d}
\le1-\frac{na_i-1}{d},
$$

or

$$
\boxed{d(1-A_i/A_*)\ge na_i-1.}
\tag{8.9}
$$

The right side is signed. An index with small pressure $a_i<1/n$ is allowed a negative right side. Replacing it by an absolute value, or insisting that every row separately be at least as favorable as the regular row, would remove the compensation needed by the proof.

## 8.4. Reciprocal probability supplies the scalar hypotheses

Assume the rank is at most $n-1$, so the construction of the $d$-dimensional actual regions is available. Let $p_0>0$ be any number satisfying

$$
h_i(\rho\mathbf1)\ge p_0\qquad\text{for every }i.
\tag{8.10}
$$

The reference keeps each actual list of tangent unit normals and replaces its supports by the common number $\rho$. No translation is optimized, and no covariance derivative is taken at the reference.

The function $1/h_i$ is convex by (6.10) and differentiable at the actual support vector by Lemma 5.1. Its lower tangent at that vector, together with (8.10), gives

$$
\frac1{p_0}\ge\frac1{h_i(\rho\mathbf1)}
\ge\frac1{H_i}
+\frac{\langle b_i-\rho\mathbf1,\nabla h_i(b_i)\rangle}{H_i^2}.
\tag{8.11}
$$

The orientation is worth checking: convexity puts the reference reciprocal above its tangent, while the reference lower bound puts that reciprocal below $1/p_0$.

Multiply by $H_i^2$ and use (5.7). With $u_i=tk_i/(d\phi(t))$, this becomes

$$
\begin{aligned}
\frac{H_i^2}{p_0}-H_i
&\ge\frac{tk_i-\rho C_i}{\phi(t)}\\
&=du_i(1-A_i/A_*)\\
&\ge u_i(na_i-1).
\end{aligned}
\tag{8.12}
$$

Now use the exact scaling identity $H_i=u_i+e_i$ and the normalization $a_i=u_i/U$, where $U=\sum_j u_j$. Rearranging (8.12) gives

$$
\boxed{\frac{H_i^2}{np_0}-\frac{u_i^2}{U}\ge\frac{e_i}{n}.}
\tag{8.13}
$$

Indeed, the right side of (8.12) is $nu_i^2/U-u_i$; moving $H_i-u_i=e_i$ to the other side and dividing by $n$ gives (8.13).

All hypotheses of Lemma 2.1 are now present, with $x_i=H_i$, $M=np_0$, and $\omega_i=1/n$. Therefore

$$
\boxed{F_G'(t)=\phi(t)\sum_iH_i\ge n\phi(t)p_0.}
\tag{8.14}
$$

This proves the nonstrict part of the following theorem.

**Theorem 8.1 (finite-direction boundary comparison).** Let $n\ge3$, $t>0$, and let $G\in\mathcal E_n$ have distinct coordinates and rank at most $n-1$. Construct its actual canonical weights and conditional regions as above. Suppose its $n$ directional quantities in (8.5) are nonnegative and its references satisfy (8.10). Then (8.14) holds. If equality holds in (8.14), then $G=\Delta_n$.

The hypotheses concern the actual covariance and its actual conditional regions. They are not a theorem about arbitrary arrays satisfying just some of the displayed sign conditions.

## 8.5. Equality without a positive-semidefinite stress assumption

Suppose equality holds in (8.14). The equality part of Lemma 2.1 yields

$$
a_i=\frac1n,\qquad H_i=p_0\qquad\text{for every }i.
\tag{8.15}
$$

By (8.7), $A_i\le A_*$. The first two lines of (8.12) now give

$$
0\ge du_i(1-A_i/A_*)\ge0.
$$

Thus $A_i=A_*$ for every row. The endpoints of the chain (8.6) are therefore equal:

$$
C_i^2=k_i^2A_*^2=k_i^2(1-2/n).
$$

Both inequalities in that chain must be equalities. Equality in its first Cauchy--Schwarz inequality means that for every $j$ with $q_{ij}>0$,

$$
\sqrt{\frac{1+g_{ij}}{1-g_{ij}}}
$$

is constant across that row. Its value is $C_i/k_i=A_*$. Solving for the correlation gives

$$
g_{ij}=\frac{A_*^2-1}{A_*^2+1}=-\frac1{n-1}
\qquad\text{whenever }q_{ij}>0.
\tag{8.16}
$$

Lemma 3.1 says that a pair with maximal correlation in each row has positive weight. Hence that row's maximum equals $-1/(n-1)$, and every off-diagonal entry of $G$ is at most this value. Positive semidefiniteness gives

$$
0\le\mathbf1^\top G\mathbf1
=n+2\sum_{i<j}g_{ij}
\le n+n(n-1)\left(-\frac1{n-1}\right)=0.
$$

Every off-diagonal entry must attain its upper bound; otherwise the finite sum would be strictly negative. Therefore $G=\Delta_n$, proving Theorem 8.1.

Neither a lower-dimensional equality theorem nor an equality classification for the log-concave integral theorem was used. Equality is recovered from the concrete rowwise Gaussian geometry.

# 9. Completing the main proof with a strict threshold barrier

The boundary theorem applies to certain covariances at one positive threshold. We now explain why that local information proves the global comparison for every covariance and every threshold.

## 9.1. The lower-dimensional reference and the exact regular recursion

Assume comparison has been proved for $n-1$ coordinates. Each reference $h_i(\rho\mathbf1)$ in (8.10) is the probability that at most $n-1$ standard-normal scores, obtained from unit tangent normals, are all at most $\rho$. At least one tangent normal is present, by Lemma 3.1. If fewer than $n-1$ are listed, repeat any one of them until the list has length $n-1$.

Repeating a constraint does not change its event. The resulting score covariance lies in $\mathcal E_{n-1}$. It may be singular, may have repeated coordinates, and need not have constant row sums. These are precisely reasons the induction hypothesis has to cover the full domain. It gives

$$
h_i(\rho\mathbf1)\ge D_{n-1}(\rho)=:p_0>0.
\tag{9.1}
$$

Positivity follows from (1.13), since $\rho>0$. We use no equality statement at size $n-1$.

Now compute the same conditional probability for the regular covariance. Pin one regular score at $t$. Every remaining coordinate has conditional mean $-t/(n-1)$. Its conditional variance and its covariance with a different remaining coordinate are, respectively,

$$
1-\frac1{(n-1)^2}=\frac{n(n-2)}{(n-1)^2},
\qquad
-\frac1{n-1}-\frac1{(n-1)^2}=-\frac n{(n-1)^2}.
\tag{9.2}
$$

These are direct instances of (3.4). Standardizing the remaining coordinates gives unit variances and off-diagonal correlations $-1/(n-2)$, namely $\Delta_{n-1}$. The standardized threshold is

$$
\frac{t+t/(n-1)}{\sqrt{n(n-2)}/(n-1)}
=t\sqrt{\frac n{n-2}}=\rho.
$$

Formula (5.2), and symmetry among the $n$ coordinates, therefore give

$$
\boxed{D_n'(t)=n\phi(t)D_{n-1}\left(t\sqrt{\frac n{n-2}}\right).}
\tag{9.3}
$$

This calculation explains the reference scale in (8.8). It is not an arbitrary rescaling chosen to make an inequality fit: it is the conditional threshold of the regular configuration itself.

## 9.2. Two exclusions that apply at a positive-threshold global minimum

**Lemma 9.1.** Fix $n\ge3$ and $t>0$. Any global minimizer of $G\mapsto F_G(t)$ on $\mathcal E_n$ has distinct coordinates and rank at most $n-1$.

**Proof.** Suppose a minimizing vector has $X_i=X_j$ almost surely. Keep the other coordinates unchanged and replace $X_i$ by a fresh independent standard normal $W$. Because the constraint on $X_i$ was already enforced by the retained copy $X_j$, the success probability of the remaining old coordinates is exactly $F_G(t)$. The new probability is

$$
\Phi(t)F_G(t)<F_G(t).
$$

Here $F_G(t)>0$ by (1.13), and $\Phi(t)<1$ for finite $t$. The new vector is centered Gaussian with unit variances, so its covariance is an admissible competitor. This contradicts global minimality.

Now suppose the minimizer is positive definite. For sufficiently small $s>0$,

$$
\widehat G_s=G+s(I-J)
$$

is still positive definite and has diagonal one. For example, if the least eigenvalue of $G$ is $\lambda>0$, then
$z^\top\widehat G_sz\ge[\lambda-s\|I-J\|]|z|^2>0$ for small enough $s$. Every off-diagonal entry has derivative $-1$. The covariance differential (4.6) gives

$$
\left.\frac d{ds}F_{\widehat G_s}(t)\right|_{0+}
=-\sum_{i<j}q_{ij}<0,
$$

where strictness follows from Lemma 3.1. This again contradicts minimality. $\square$

This lemma excludes points only from being positive-threshold global minimizers. It does not claim that every singular covariance already satisfies the desired comparison or that every remaining covariance has a positive kernel. In rank one there are only two possible unit vectors, a vector and its negative. Thus a distinct-coordinate configuration with $n\ge3$ also has rank at least two, as needed by the intrinsic geometric interpretation.

## 9.3. Why introduce a linear penalty?

A naive attempt would minimize the unmodified difference $F_G(t)-D_n(t)$ over both variables. At an interior threshold minimum, its derivative is zero. The boundary inequality also has a nonstrict sign, so that approach would need equality rigidity before proving even nonstrict comparison.

A small linear term creates a strict contradiction instead. It also prevents a negative minimum from escaping to arbitrarily large thresholds. This separates comparison from equality and avoids any tail asymptotic estimate.

Suppose there is a counterexample at size $n$:

$$
F_{G_0}(t_0)-D_n(t_0)=-\delta<0.
$$

By (1.9), necessarily $t_0>0$. Set

$$
\varepsilon=\frac{\delta}{2t_0}>0,
\qquad
\Psi(G,t)=F_G(t)-D_n(t)+\varepsilon t,
\qquad t\ge0.
\tag{9.4}
$$

At $(G_0,t_0)$, this function equals $-\delta/2$.

As $t\downarrow0$, uniformly in $G$,

$$
\Psi(G,t)\ge-D_n(t)+\varepsilon t,
$$

and the right side tends to zero. For sufficiently small $t$ it is therefore larger than, say, $-\delta/4$. As $t\to\infty$,

$$
\Psi(G,t)\ge-1+\varepsilon t\longrightarrow+\infty,
$$

again uniformly in $G$. It follows that a minimizing value at most $-\delta/2$ can only occur with $t$ in a compact interval $[a,b]\subset(0,\infty)$ whose threshold endpoints have larger values. Compactness of $\mathcal E_n$ and joint continuity (1.12) give an attained negative global minimum

$$
(G_*,t_*),\qquad 0<t_*<\infty.
$$

No unproved small- or large-threshold comparison was used to obtain this minimum.

## 9.4. The contradiction at the worst point

Since the other terms of $\Psi(G,t_*)$ do not depend on $G$, the covariance $G_*$ is a global shape minimum of $F_G(t_*)$. Lemma 9.1 makes it distinct-coordinate and singular. Its rank is therefore at most $n-1$, and its finite directional quantities (8.5) are nonnegative because the paths (8.3) are feasible.

The lower-dimensional comparison supplies the reference floor (9.1). Theorem 8.1 and the regular recursion (9.3) then give

$$
F_{G_*}'(t_*)\ge n\phi(t_*)D_{n-1}\left(t_*\sqrt{\frac n{n-2}}\right)
=D_n'(t_*).
\tag{9.5}
$$

On the other hand, $t_*$ is an interior minimum of the differentiable fixed-shape function $t\mapsto\Psi(G_*,t)$. Thus

$$
F_{G_*}'(t_*)-D_n'(t_*)=-\varepsilon<0,
\tag{9.6}
$$

contradicting (9.5).

The contradiction proves comparison at size $n$, assuming it at size $n-1$. Section 1.4 supplied the base $n=2$. Induction proves (1.2) for every $n\ge2$ and every positive threshold; (1.9) already handled nonpositive thresholds.

The bad covariance did not have to lie in a balanced class, have a one-dimensional kernel, or remain at the same rank under the variations. Only its extremal property in the full unit-diagonal positive-semidefinite domain was used.

## 9.5. Positive-threshold uniqueness comes afterwards

Fix finite $t_0>0$ and suppose $F_G(t_0)=D_n(t_0)$. For $n=2$, uniqueness was proved in Section 1.4. Let $n\ge3$.

The comparison just established makes $G$ a global shape minimum at $t_0$. Lemma 9.1 again makes it distinct-coordinate and singular, and its finite directional tests are nonnegative. Moreover, comparison at all nearby thresholds for this fixed $G$ says that

$$
t\longmapsto F_G(t)-D_n(t)
$$

has a minimum zero at $t_0$. Both functions are differentiable there, so

$$
F_G'(t_0)=D_n'(t_0).
$$

With the reference floor $p_0=D_{n-1}(t_0\sqrt{n/(n-2)})$, this is equality in Theorem 8.1. Its rigidity conclusion forces $G=\Delta_n$. Conversely, that covariance plainly gives equality.

This proves (1.3). There was no circular use of equality to establish nonstrict comparison. There was also no need for strictness in the lower-dimensional theorem or in the log-concave integral theorem.

# 10. The geometric and logarithmic route

We now give the alternative proof. Set aside the comparison conclusion of Section 9. The argument in this section and Section 11 uses the shared Gaussian foundations, the independently proved exclusions at shape minima, and a different scalar assembly. It retains geometric information that the finite-direction proof deliberately did not need.

## 10.1. All feasible rank-one tests give positive stress

At a distinct-coordinate local minimum, (8.4) applied to every $L=zz^\top$ gives

$$
z^\top Sz\ge0\qquad\text{for all }z\in\mathbb R^n,
$$

which is exactly $S\succeq0$. At a global minimum, distinctness follows from the independent-coordinate replacement in Lemma 9.1, which did not use the comparison theorem.

One can also exclude duplicates at a local minimum: retain a duplicate and replace the other by $\cos\theta\,X_i+\sin\theta\,W$ with independent standard normal $W$. The retained copy still enforces the old constraint. Conditional on any successful old sample, the new noisy constraint has a strictly positive chance of failure, so the new probability is strictly smaller. Its covariance tends to the old one as $\theta\to0$. This observation is not required for the global assembly, but explains the local form of the stress statement.

The definition of the diagonal in (8.1) gives the exact cancellation

$$
\operatorname{tr}(GS)
=\sum_iS_{ii}+\sum_{i\ne j}g_{ij}q_{ij}=0.
\tag{10.1}
$$

For two positive-semidefinite matrices, this forces their product to be zero. Indeed,

$$
0=\operatorname{tr}(G^{1/2}SG^{1/2})
=\|S^{1/2}G^{1/2}\|_F^2,
$$

where $\|A\|_F^2=\sum_{i,j}A_{ij}^2$ is the squared Frobenius norm. Therefore $S^{1/2}G^{1/2}=0$, and multiplication by the square roots gives $SG=GS=0$.

Since $S\mathbf1=k$, it follows that

$$
Ga=0,\qquad a_i=k_i/\kappa>0,\qquad \sum_i a_i=1.
\tag{10.2}
$$

In the Gram representation, (10.2) means

$$
\sum_i a_i v_i=0,
\tag{10.3}
$$

because the squared norm of this sum is $a^\top Ga$. This is a **positive dependence** of all the normals: zero is a weighted average using every normal with positive weight. It is not necessarily the uniform average. The same argument shows $\operatorname{rank}G\le n-1$, without the positive-definite exclusion used by the finite-direction proof.

## 10.2. What the stronger certificate reveals geometrically

Let the normals span the intrinsic space $\mathbb R^r$. For every unit vector $z$ in that space,

$$
\max_i v_i\cdot z>0.
$$

Otherwise every term would be nonpositive, and (10.3) would force every term to be zero. Spanning would then give $z=0$, a contradiction. By compactness of the unit sphere, the continuous function $\max_i v_i\cdot z$ has a strictly positive minimum $c$. Therefore any point in $K_t$ has norm at most $t/c$. The intrinsic cap and each intrinsic facet are bounded.

This boundedness has now been proved under $S\succeq0$. It was not available in the weaker finite-direction proof. Padding still turns lower-rank facets into unbounded cylinders, so even in this route it is useful that the shared analytic facts cover unbounded regions.

There is also a boundary balance. The columns of $V$ span the range of $G=VV^\top$, so $SG=0$ implies $SV=0$. Row $i$ of this equation reads

$$
\sum_{j\ne i}q_{ij}(v_j-g_{ij}v_i)
=\sum_j\sigma_{ij}q_{ij}w_{ij}=0.
\tag{10.4}
$$

Using (5.6), this is $\sum_j\partial_{b_{ij}}h_i(b_i)w_{ij}=0$. It says that the actual boundary weights balance as vectors inside the facet's tangent space.

For an additional interpretation, translate the intrinsic conditional region $P_i$ by a tangent vector $z$. Its supports become $b_{ij}+w_{ij}\cdot z$. On the one hand, differentiating its mass at $z=0$ gives the vector $\sum_j\partial_{b_{ij}}h_i(b_i)w_{ij}$, which vanishes by (10.4). On the other hand,

$$
\gamma_{r-1}(P_i+z)=\int_{P_i}\phi_{r-1}(y+z)\,dy,
$$

whose gradient at zero is $-\int_{P_i}y\,d\gamma_{r-1}(y)$. Differentiation is justified by boundedness, or by the same Gaussian domination as in Section 7. Hence

$$
\int_{P_i}y\,d\gamma_{r-1}(y)=0.
\tag{10.5}
$$

Thus the normalized Gaussian average of the actual physical facet is its tangency point $tv_i$. This is a consequence of the stronger stress certificate, not an assumption that all competitors are centered. We will still compare actual support probabilities; separately optimizing translations of unrelated facets would not reproduce the common equations (10.4)--(10.5).

## 10.3. The geometric row estimate and the logarithmic tangent

For clarity, the second row estimate can now be obtained directly from positive-semidefinite Cauchy--Schwarz:

$$
k_i^2=(f_i^\top S\mathbf1)^2\le S_{ii}\kappa.
\tag{10.6}
$$

This is ordinary Cauchy--Schwarz for $S^{1/2}f_i$ and $S^{1/2}\mathbf1$. Combining it with the first scalar Cauchy inequality in (8.6) gives again

$$
A_i\le\sqrt{1-2a_i},\qquad
d(1-A_i/A_*)\ge na_i-1.
\tag{10.7}
$$

The alternative route has reached the same signed row inequality, but it also knows the positive dependence and the boundary vector balance.

Let $p_0>0$ be a common reference floor as in (8.10). Instead of applying convexity of $1/h_i$, use the upper tangent for the concave function $\log h_i$ at the actual supports:

$$
\log p_0\le\log h_i(\rho\mathbf1)
\le\log H_i+\frac{\langle\rho\mathbf1-b_i,\nabla h_i(b_i)\rangle}{H_i}.
$$

Using (5.7) and multiplying by $H_i$ gives

$$
\boxed{
H_i\log\frac{H_i}{p_0}
\ge\frac{tk_i-\rho C_i}{\phi(t)}
=du_i(1-A_i/A_*)
\ge u_i(na_i-1).
}
\tag{10.8}
$$

The scaling decomposition (7.3) remains $H_i=u_i+e_i$, with $a_i=u_i/U$ and both parts positive. In the intrinsic geometry, it can instead be written as (7.8), with $d_0=r-1\le d$. Thus no rank-dependent remainder has been dropped.

We could use $\log z\le z-1$ in (10.8) and reduce to the quadratic proof. The next lemma keeps the logarithmic information rather than discarding it.

## 10.4. The logarithmic mass lemma

**Lemma 10.1.** Let $u_i,e_i>0$, put $x_i=u_i+e_i$, $U=\sum u_i$, $E=\sum e_i$, and $P=U+E$. Define

$$
a_i=u_i/U,\qquad \nu_i=e_i/E.
$$

Let $\omega_i>0$, $\sum_i\omega_i=1$, and $M>0$. If

$$
x_i\log\frac{x_i}{M\omega_i}
\ge u_i\left(\frac{a_i}{\omega_i}-1\right)
\quad\text{for every }i,
\tag{10.9}
$$

then $P\ge M$. Equality forces $a_i=\nu_i=\omega_i$ and $x_i=M\omega_i$ for every $i$.

**Proof.** The function $z\log z$ is strictly convex on $(0,\infty)$, because its second derivative is $1/z>0$. Apply its two-point convexity inequality to

$$
\frac{x_i}{P\omega_i}
=\frac UP\frac{a_i}{\omega_i}
+\frac EP\frac{\nu_i}{\omega_i}.
$$

Multiplying by $P\omega_i$ yields the componentwise **log-sum inequality**

$$
x_i\log\frac{x_i}{P\omega_i}
\le u_i\log\frac{a_i}{\omega_i}
+e_i\log\frac{\nu_i}{\omega_i}.
\tag{10.10}
$$

Subtract this upper bound from the lower bound (10.9). With $v_i=a_i/\omega_i$,

$$
x_i\log\frac PM
\ge u_i(v_i-1-\log v_i)-e_i\log\frac{\nu_i}{\omega_i}.
\tag{10.11}
$$

The function $v-1-\log v$ is nonnegative and vanishes only at $v=1$: its derivative is $1-1/v$, negative below one and positive above one.

If $P<M$, the left side of (10.11) is negative. Since $u_i>0$, its first term on the right is nonnegative. Therefore $\log(\nu_i/\omega_i)>0$ for every $i$, or $\nu_i>\omega_i$ for every $i$. This contradicts that the two probability vectors have the same sum.

If $P=M$, the same inequality gives $\nu_i\ge\omega_i$ for every $i$, hence $\nu=\omega$. Equation (10.11) then forces $v_i-1-\log v_i=0$ for every $i$. Thus $a=\omega$ as well, and $x_i=M\omega_i$. $\square$

This proof does not begin by summing (10.9). A total deficit would instead force a contradiction at every normalized remainder coordinate. The componentwise positive energy is what permits that inference.

## 10.5. The geometric boundary theorem and its equality

Apply Lemma 10.1 to (10.8), with $x_i=H_i$, $\omega_i=1/n$, and $M=np_0$. We obtain

$$
F_G'(t)=\phi(t)\sum_iH_i\ge n\phi(t)p_0.
\tag{10.12}
$$

This holds for any distinct-coordinate configuration whose canonical stress is positive semidefinite and whose references have the stated floor. A full-domain shape minimum is one way to obtain that stress condition.

For completeness, there is a geometric equality argument that uses the extra information retained in this route. If equality holds in (10.12), Lemma 10.1 gives $a_i=1/n$ and $H_i=p_0$. Equation (10.8) and $A_i\le A_*$ force $A_i=A_*$. Equality follows throughout the two Cauchy inequalities, so

$$
k_i=\kappa/n,\qquad S_{ii}=\kappa/n^2.
$$

Equality in (10.6) gives

$$
S^{1/2}f_i=\frac1n S^{1/2}\mathbf1
\quad\text{for every }i.
$$

To see its coefficient, take the inner product with $S^{1/2}\mathbf1$: the inner product is $k_i=\kappa/n$, and the squared norm of that latter vector is $\kappa$. Taking pairwise inner products now yields

$$
S=\frac{\kappa}{n^2}J.
\tag{10.13}
$$

In particular every pair weight is positive. Equality in scalar row Cauchy makes the off-diagonal correlations constant within each row. Moreover, (10.2) and $a=\mathbf1/n$ give $G\mathbf1=0$. If the common off-diagonal value of row $i$ is $c_i$, its row sum gives $1+(n-1)c_i=0$. Thus every $c_i=-1/(n-1)$, and $G=\Delta_n$.

The finite-direction proof recovered equality using nearest positive pins; this geometric proof recovers it using equality in the positive-semidefinite stress. Both are complete, and neither uses a strict equality theorem for log-concave integrals.

## 10.6. What the logarithmic calculation remembers

Here is an exact form of the information retained by the logarithmic route. Define the relative entropy of positive probability vectors $p,q$ by

$$
D(p\Vert q)=\sum_i p_i\log\frac{p_i}{q_i}.
$$

It is nonnegative: $-\log z\ge1-z$ gives

$$
D(p\Vert q)=-\sum_i p_i\log\frac{q_i}{p_i}
\ge\sum_i(p_i-q_i)=0.
$$

Equality requires $p_i=q_i$ for every $i$, because the scalar inequality is strict except at one. For two-point distributions, write

$$
d_{\mathrm{Ber}}(s\Vert r)
=s\log\frac sr+(1-s)\log\frac{1-s}{1-r},
\qquad 0<s,r<1.
$$

This is the same relative entropy for probabilities of a two-outcome experiment.

In the setting of Lemma 10.1, let

$$
\delta=\log(P/M),\quad v_i=a_i/\omega_i,\quad
s_i=x_i\log\frac{x_i}{M\omega_i}-u_i(v_i-1)\ge0,
$$

and define the log-sum loss

$$
\begin{aligned}
J_i&=u_i\log\frac{a_i}{\omega_i}
+e_i\log\frac{\nu_i}{\omega_i}
-x_i\log\frac{x_i}{P\omega_i}\\
&=x_i\,d_{\mathrm{Ber}}\left(\frac{u_i}{x_i}\,\middle\Vert\,\frac UP\right)\ge0.
\end{aligned}
\tag{10.14}
$$

The second line follows by substituting $a_i=u_i/U$, $\nu_i=e_i/E$, and $x_i=u_i+e_i$. Expanding the logarithms gives the exact identity

$$
\boxed{
x_i\delta+e_i\log\frac{\nu_i}{\omega_i}
=u_i(v_i-1-\log v_i)+s_i+J_i.
}
\tag{10.15}
$$

The three terms on the right have different sources: the scalar inequality $\log v\le v-1$, the supplied componentwise comparison, and the log-sum inequality. Dividing by $e_i$, multiplying by $\omega_i$, and summing gives

$$
\delta\sum_i\omega_i\frac{x_i}{e_i}
=D(\omega\Vert\nu)
+\sum_i\omega_i\left[
\frac{u_i}{e_i}(v_i-1-\log v_i)+\frac{s_i+J_i}{e_i}\right].
\tag{10.16}
$$

Every term on the right is nonnegative. This identity both proves the mass comparison and identifies what equality has to remove.

In the Gaussian application, $s_i$ itself has two visible pieces. Set

$$
\mathcal R_i=d(1-A_i/A_*)-(na_i-1)\ge0,
$$

$$
\mathcal T_i=H_i\log(H_i/p_0)-du_i(1-A_i/A_*)\ge0.
$$

Then $s_i=u_i\mathcal R_i+\mathcal T_i$. The first term records loss in the row geometry and covariance tests; the second records loss in the logarithmic support tangent. Substituting in (10.15) gives

$$
\begin{aligned}
H_i\log\frac{\sum_jH_j}{np_0}+e_i\log(n\nu_i)
={}&u_i[na_i-1-\log(na_i)]\\
&+u_i\mathcal R_i+\mathcal T_i+J_i.
\end{aligned}
\tag{10.17}
$$

This is why entropy is informative even though it is not needed for the shortest qualitative proof. It separates disagreement of the pressure weights, loss in the geometry, loss in the support comparison, and disagreement between the pressure and energy parts.

# 11. The minimum-envelope ending

The strict barrier focused on one hypothetical worst counterexample. The alternative ending follows the least achievable probability as the threshold moves. This makes the induction look like a differential comparison.

## 11.1. The least achievable probability at each threshold

For $n\ge2$ and $t\ge0$, define

$$
m_n(t)=\min_{G\in\mathcal E_n}F_G(t).
\tag{11.1}
$$

This minimum exists by compactness and continuity. It is positive for $t>0$ by the uniform lower bound (1.13). At zero it equals zero because $\Delta_n$ is an admissible covariance and $D_n(0)=0$.

The uniform marginal increment bound gives

$$
0\le m_n(s)-m_n(t)\le n[\Phi(s)-\Phi(t)]
\qquad(s\ge t\ge0).
\tag{11.2}
$$

For the lower bound, every $F_G$ is increasing. For the upper bound, use a covariance attaining the minimum at $t$ as a competitor at $s$. Thus $m_n$ is Lipschitz and in particular continuous.

Now take $n\ge3$; the two-coordinate minimum will supply the base case. Every minimizing covariance at a positive threshold is distinct-coordinate. Its canonical stress is positive semidefinite by Section 10.1. For each of its tangent references, the definition of the lower-size minimum, with duplicated constraints when necessary, gives

$$
h_i(\rho\mathbf1)\ge m_{n-1}(\rho)>0,
\qquad \rho=t\sqrt{\frac n{n-2}}.
$$

The geometric boundary theorem (10.12) therefore implies that every such minimizer satisfies

$$
F_G'(t)\ge b_n(t),\qquad
b_n(t):=n\phi(t)m_{n-1}\left(t\sqrt{\frac n{n-2}}\right).
\tag{11.3}
$$

No lower-size comparison has yet been assumed in obtaining (11.3). It is a recursion involving the actual minimum functions themselves. The function $b_n$ is continuous for $t>0$, and extends continuously to zero with value zero.

## 11.2. Why the minimizing covariance need not be differentiable

At a threshold where $m_n$ happens to be differentiable, choose any minimizing covariance $G$. The fixed-shape function $F_G(s)$ lies above $m_n(s)$ for every $s$ and touches it at the chosen threshold. Hence the difference has a minimum zero there, and

$$
m_n'(t)=F_G'(t)\ge b_n(t).
\tag{11.4}
$$

This calculation differentiates two functions of one real variable at a contact point. It never differentiates a choice $G=G(t)$ of optimizer. That choice need not be unique, continuous, or of constant rank.

There is a familiar way to finish using the fundamental theorem for Lipschitz functions. To make the closing argument independent even of that additional real-analysis result, we next prove the needed integral comparison directly from right-hand difference quotients. This is an elaboration of the same minimum-envelope argument, not an additional Gaussian comparison premise.

## 11.3. A direct integral justification

First we show that for every $t>0$,

$$
\liminf_{h\downarrow0}\frac{m_n(t+h)-m_n(t)}h\ge b_n(t).
\tag{11.5}
$$

Choose a minimizer $G_h$ at $t+h$. Since $m_n(t)\le F_{G_h}(t)$,

$$
\frac{m_n(t+h)-m_n(t)}h
\ge\frac{F_{G_h}(t+h)-F_{G_h}(t)}h.
\tag{11.6}
$$

Consider any sequence $h_j\downarrow0$ along which the left side tends to its lower limit. By compactness, after taking a subsequence $G_{h_j}\to G_0$. Joint CDF continuity and continuity of $m_n$ show that $G_0$ minimizes at $t$:

$$
F_{G_0}(t)=\lim_j F_{G_{h_j}}(t+h_j)=m_n(t).
$$

This limiting covariance has distinct coordinates. Nearby covariances are therefore still separated from duplicates. Section 5.2 proved joint continuity of $F_G'(s)$ at every distinct-coordinate covariance and positive threshold, including changes of rank. Consequently

$$
\frac{F_{G_{h_j}}(t+h_j)-F_{G_{h_j}}(t)}{h_j}
=\frac1{h_j}\int_t^{t+h_j}F_{G_{h_j}}'(s)\,ds
\longrightarrow F_{G_0}'(t).
$$

The integral equality uses only the ordinary fundamental theorem of calculus for a continuously differentiable fixed-shape profile. Equation (11.3) at $G_0$ gives (11.5).

Here is the elementary integration principle needed for (11.5).

**Lemma 11.1.** Let $f$ be continuous on an interval, and let $b$ be continuous there. Suppose at every point short of its right endpoint,

$$
\liminf_{h\downarrow0}\frac{f(t+h)-f(t)}h\ge b(t).
$$

Then for any $a<c$ in the interval,

$$
f(c)-f(a)\ge\int_a^c b(s)\,ds.
$$

**Proof.** Subtract the continuously differentiable function $\int_a^t b(s)\,ds$. It is enough to prove that a continuous function $q$ with lower right difference quotient at least zero cannot decrease.

Fix $\varepsilon>0$ and let $q_\varepsilon(t)=q(t)+\varepsilon t$. Its lower right difference quotient is at least $\varepsilon$. If $q_\varepsilon(c)<q_\varepsilon(a)$, this continuous function attains a maximum on $[a,c]$ at a point $t_*<c$. Every sufficiently small positive increment from that point is nonpositive, so its lower right difference quotient is at most zero, a contradiction. Thus $q_\varepsilon(c)\ge q_\varepsilon(a)$. Let $\varepsilon\downarrow0$. $\square$

Apply the lemma to (11.5) on a positive interval $[a,t]$, and then let $a\downarrow0$. Continuity of $m_n$ at zero, and continuity and boundedness of $b_n$ near zero, give

$$
\boxed{m_n(t)\ge\int_0^t n\phi(s)
 m_{n-1}\left(s\sqrt{\frac n{n-2}}\right)\,ds.}
\tag{11.7}
$$

This is the integral form of the minimum-envelope recursion. In the usual almost-everywhere derivative presentation it is the integral of (11.4); the direct proof above supplies all the closing justification without a differentiable optimizer selection.

## 11.4. Induction and equality in the second presentation

Section 1.4 gives $m_2=D_2$ on $[0,\infty)$. Suppose $m_{n-1}=D_{n-1}$. By the exact regular recursion (9.3), the right side of (11.7) is

$$
\int_0^t D_n'(s)\,ds=D_n(t).
$$

For rigor at zero, first integrate from $a>0$, use the ordinary fundamental theorem there, and then let $a\downarrow0$, using $D_n(a)\to0$. Thus $m_n(t)\ge D_n(t)$. The reverse inequality follows because $\Delta_n$ is an admissible competitor in the minimum (11.1). Therefore $m_n=D_n$.

Induction proves the full comparison for positive thresholds by this second route; (1.9) again handles the others. If $F_G(t_0)=D_n(t_0)$ for finite $t_0>0$, then $G$ is a shape minimum and has positive-semidefinite stress. Since comparison is now proved for all nearby thresholds, the fixed-shape difference touches zero and has derivative zero. Equation (9.3) turns that derivative equality into equality in (10.12). The geometric equality proof in Section 10.5 gives $G=\Delta_n$. The two-coordinate equality case is still the direct calculation in Section 1.4.

This completes the geometric and logarithmic presentation independently of the comparison established in Section 9, while sharing its Gaussian differentiation and support foundations. The extra geometry was obtained from all rank-one tests; the logarithmic mass lemma retained additional information; the envelope described the best possible probability at every threshold. None of these differences creates a second verification of the shared singular-boundary calculus.

# 12. What is essential, and why several plausible shortcuts fail

## 12.1. Entrywise comparison and covariance averaging do not solve the problem

Equation (4.8) gives an immediate monotonicity statement when two distinct-coordinate covariances are ordered entry by entry off the diagonal: increasing every off-diagonal correlation along their feasible segment cannot decrease $F_G(t)$. But a general covariance is not entrywise comparable with $\Delta_n$.

For example, the three scores $(Z,-Z,W)$, with $Z,W$ independent standard normals, have correlations $g_{12}=-1$ and $g_{13}=g_{23}=0$. The regular three-score correlations are all $-1/2$. Some correlations are smaller and some are larger, so the monotone derivative alone does not compare these configurations.

Ordering by positive-semidefinite difference is even less helpful with a fixed diagonal. If $G-H\succeq0$ and both diagonals equal one, then $G-H$ has zero diagonal. Every two by two principal submatrix must have nonnegative determinant, which forces every off-diagonal entry to be zero. Thus $G=H$. There is no nontrivial positive-semidefinite ordering inside a fixed-diagonal class.

Nor can we silently average covariances over permutations and apply Jensen's inequality. The probability is not generally convex or concave as a function of covariance. Already for two coordinates and positive $t$, its first correlation derivative is $q(c)=\phi_2(t,t;c)$, and

$$
\frac{q'(c)}{q(c)}=\frac{c}{1-c^2}+\frac{t^2}{(1+c)^2}.
$$

At $t=1/4$ this equals $-5/12$ when $c=-1/2$, but equals $1/16$ when $c=0$. The second derivative of the probability therefore has both signs on its feasible correlation interval. A covariance-averaging argument needs a property that these probabilities do not possess.

The actual proof uses feasibility only at a minimum, extracting the specific row inequalities needed by the conditional masses.

## 12.2. A favorable total energy does not replace positive energy in every component

The following is an exact scalar example, not a Gaussian covariance. Take three components, $p_0=1/2$, $M=3p_0=3/2$, and

$$
x=\left(\frac35,\frac1{512},\frac1{512}\right),\qquad
u=\left(\frac9{50},\frac{27}{200},\frac{27}{200}\right).
\tag{12.1}
$$

Here $u$ denotes the pressure vector, as in the scalar lemmas. Its total and normalized weights are

$$
U=\frac9{20},\qquad a=\left(\frac25,\frac3{10},\frac3{10}\right).
$$

The total mass and total remainder are

$$
P=\frac{773}{1280}<\frac32=M,\qquad
P-U=\frac{197}{1280}>0.
\tag{12.2}
$$

Nevertheless, for every $i$,

$$
x_i\log(x_i/p_0)\ge u_i(3a_i-1).
\tag{12.3}
$$

For the first coordinate, $\log(6/5)\ge1/6$, because $1/s\ge5/6$ on $[1,6/5]$. Its left side is therefore at least $1/10$, larger than the right side $9/250$. For either small coordinate, its left side is $-\log2/64$. Convexity of $1/s$ puts its integral on $[1,2]$ strictly below the trapezoidal area $3/4$, so $\log2<3/4$. Therefore the small-coordinate left side exceeds $-3/256$, which exceeds the right side $-27/2000$.

The individual remainders are

$$
e=x-u=\left(\frac{21}{50},-\frac{1703}{12800},-\frac{1703}{12800}\right).
$$

Two are negative. The logarithmic mass lemma would be false if positivity of each remainder were replaced by positivity of their sum. The same example defeats that relaxation of the quadratic lemma: $\log z\le z-1$ converts (12.3) into

$$
\frac{x_i^2}{M}-\frac{u_i^2}{U}\ge\frac{x_i-u_i}{3},
$$

yet $P<M$.

The actual Gaussian identity (7.3) excludes exactly this defect. It represents each remainder as its own nonnegative energy integral and proves that integral strictly positive. A bulk moment estimate after summing would not provide the same information.

## 12.3. Positive components do not justify summing the hypotheses too early

A different scalar example keeps every remainder positive but retains only a summed logarithmic hypothesis. Let

$$
\omega=(1/2,1/2),\qquad \mu=(9/10,1/10),\qquad
c=D(\mu\Vert\omega)>0.
$$

Strict positivity of $c$ follows from the equality characterization for relative entropy proved in Section 10.6. Fix any $M>0$ and choose

$$
P=M e^{-c/2}<M,\qquad x=P\mu,\qquad
u=\alpha P\omega,\qquad 0<\alpha<1/5.
$$

Then $U=\alpha P$, $a=\omega$, and $e=x-u$ is positive in both components. However,

$$
\sum_i x_i\log\frac{x_i}{M\omega_i}
=P\left[\log\frac PM+D(\mu\Vert\omega)\right]
=\frac{Pc}{2}>0,
$$

whereas

$$
\sum_i u_i(a_i/\omega_i-1)=0.
$$

Thus the sum of the intended hypotheses holds favorably while the desired total-mass conclusion is false. The logarithmic proof needs the inequality for every component, not merely its sum. This failure is distinct from the negative-remainder failure in Section 12.2.

## 12.4. Some legitimate pair weights vanish

It would simplify equality arguments if every nonantipodal pair always had positive weight, but that claim is false. Let the eight normals in $\mathbb R^3$ be

$$
v_\epsilon=\epsilon/\sqrt3,\qquad \epsilon\in\{-1,1\}^3.
$$

Their common-threshold region is

$$
|z_1|+|z_2|+|z_3|\le\sqrt3\,t.
$$

Choose the two normals $(1,1,1)/\sqrt3$ and $(1,-1,-1)/\sqrt3$. Their correlation is $-1/3$, so they are nonantipodal. Pinning their scores to $t$ gives

$$
z_1=\sqrt3\,t,\qquad z_2+z_3=0.
$$

The remaining cap inequalities then require $z_2=z_3=0$. The conditional residual is a nondegenerate one-dimensional Gaussian along the line $z_2+z_3=0$, and this last event is a single point. Its probability is zero, so this nonantipodal pair has $q_{ij}=0$.

Several faces meet at vertices in this region. Such intersections do not spoil the support differentiation lemma, but they show why one cannot replace it by an assumption that all listed pair intersections are genuine edges. The proof only required a positive pair in each row, and Lemma 3.1 supplied one with an explicit choice.

## 12.5. The exact Cauchy loss and the relation between the routes

The scalar Cauchy proof can retain an exact identity, just as the entropy proof did. In Lemma 2.1 define

$$
s_i^Q=\frac{x_i^2}{M}-\frac{u_i^2}{U}-\omega_i e_i\ge0,
$$

and

$$
\Lambda_i=\frac{u_i^2}{U}+\frac{e_i^2}{E}-\frac{x_i^2}{P}
=\frac{(Eu_i-Ue_i)^2}{PUE}\ge0.
$$

Adding the two definitions, dividing by $e_i$, and summing yields

$$
\boxed{
\left(\frac1M-\frac1P\right)\sum_i\frac{x_i^2}{e_i}
=\sum_i\frac{s_i^Q+\Lambda_i}{e_i}.
}
\tag{12.4}
$$

To check the cancellation, before summing the remaining terms are $\omega_i-e_i/E$, whose sum is zero. All denominators are positive. Thus (12.4) is another proof of the scalar comparison. It identifies disagreement between the normalized pressure and energy portions through $\Lambda_i$. The shorter proof selected one suitable component instead of summing with the weights $1/e_i$.

The logarithmic identity (10.17) retains additional scalar information about the reference weights. Its geometric part can also be unpacked. Define

$$
V_i=k_i(k_i-2S_{ii})-C_i^2\ge0.
$$

Then

$$
k_i^2(1-2a_i)-C_i^2
=2k_i\left(S_{ii}-\frac{k_i^2}{\kappa}\right)+V_i.
\tag{12.5}
$$

The first term is loss in the covariance test, and the second is loss in rowwise scalar Cauchy. There is also the elementary square-root tangent loss in passing to (8.9). These are concrete pieces of a common mechanism, not independent theories being invoked by name.

## 12.6. What the proof needs, and what it does not

The essential analytic compatibility consists of three formulas using the same pair weights:

$$
\begin{aligned}
\text{covariance change:}\quad
&DF_G(t)[\dot G]=\sum_{i<j}q_{ij}\,\dot g_{ij},\\
\text{support change:}\quad
&\partial_{b_{ij}}h_i(b_i)=\sigma_{ij}q_{ij}/\phi(t),\\
\text{scaling:}\quad
&H_i=\frac{tk_i}{d\phi(t)}+\frac1d\int_{Q_i}|y|^2\,d\gamma_d(y).
\end{aligned}
\tag{12.6}
$$

Here $DF_G(t)[\dot G]$ means the relative linear first variation from Proposition 4.1, and $d=n-2$ is the padded tangent dimension. The last line is the mass decomposition itself, rather than an estimate of a total moment.

Unit variances and a common positive threshold are used in the boundary-atom exclusion, in the tangent supports, and in matching the regular reference. The full covariance domain is used to permit the rank-changing variations. Positive energy in every component lets the scalar comparison normalize the remainder separately at each coordinate. The lower-size theorem supplies a value at the reference, not a derivative there.

Several other ingredients are choices of presentation. Reciprocal probability leads directly to a quadratic Cauchy comparison. Logarithmic probability keeps entropy losses. The finite directional proof uses only the particular inequalities it needs; the full positive-stress proof additionally yields weighted geometric balance and centered actual facets. Padding makes the energy uniform in rank; the intrinsic formula explains where the additional energy comes from. The strict barrier avoids an envelope regularity argument and separates comparison from equality. The envelope shows a recursion for the least possible probabilities themselves.

None of the arguments requires an everywhere-improving motion. At a worst counterexample, feasibility gives the required directional signs automatically. Those signs, together with the compatible conditional calculations, make its boundary growth too large for it to be worst. This is why a local argument at an extremum can prove a global stochastic comparison without classifying every stationary point or constructing a convergent flow.

The conclusion is exactly the common-threshold stochastic order in Theorem 1.1. The proof does not assert an order for arbitrary unequal threshold vectors, a stronger likelihood-ratio order, an optimized exponential-tilt inequality, or an optimal configuration under a rank constraint that excludes the regular simplex.

# 13. Notation and source orientation

## 13.1. Notation guide

$G$ is always a correlation matrix; $\Delta_n=(nI-J)/(n-1)$ is the regular one. $F_G(t)$ and $D_n(t)$ are their common-threshold cumulative probabilities. $X$ denotes the Gaussian score vector, while $Z$ or $Y$ denotes an ambient or residual standard Gaussian.

The vectors $v_i$ are the original unit normals. Their intrinsic span has dimension $r$. Once $r\le n-1$ is available, the padded tangent dimension is $d=n-2$. The intrinsic tangent dimension is $d_0=r-1$. The symbols $f_i$ used in matrix tests are standard coordinate vectors, not normals or scalar remainders.

The pair coefficient $q_{ij}$ is defined by the actual two-score conditional law at $t$, with value zero at an antipodal pair. $S$ is the matrix in (8.1), $k_i=(S\mathbf1)_i$, $\kappa=\sum_i k_i$, and $a_i=k_i/\kappa$. Only in the positive-stress route is $a$ known to be a kernel vector before equality is proved.

The tangent unit normals, actual supports, and probabilities are $w_{ij}$, $b_{ij}$, and $H_i=h_i(b_i)=\gamma_d(Q_i)$. The numbers $C_i=\sum_j\sigma_{ij}q_{ij}$ and $A_i=C_i/k_i$ summarize one other support derivative. The common regular values are $A_*=\sqrt{(n-2)/n}$ and $\rho=t/A_*$. The reference floor is $p_0$; in the induction it is $D_{n-1}(\rho)$, and in the unconditional envelope recursion it is $m_{n-1}(\rho)$.

The scalar decomposition is $H_i=u_i+e_i$, with $u_i=tk_i/[d\phi(t)]$ and $e_i=d^{-1}\int_{Q_i}|y|^2\,d\gamma_d(y)$. Their totals are $U,E$, and their normalized distributions are $a,\nu$. In the general scalar lemmas $x_i=u_i+e_i$ and $P=\sum_i x_i$; in the Gaussian application $x_i=H_i$. The symbol $P$ in those scalar lemmas is a total, while $P_i$ in intrinsic geometric formulas is a region. Subscripts distinguish the latter.

## 13.2. Which supplied materials shaped this exposition?

This manuscript is based on the exact supplied writing context and source archive. Its main argument expands `CORE_PROOF.md`: finite covariance directions, reciprocal support probability, scalar Cauchy, a strict threshold barrier, and separate positive-threshold equality. The scalar identities and adverse examples also use `COMPONENTWISE_COMPARISON.md`.

`ALL_DIMENSIONAL_FSC_PRESSURE_ENERGY_PROOF.md` supplies the alternative presentation: positive stress, weighted geometric balance, the componentwise logarithmic comparison, and the minimum envelope. The shared analytic details were reconstructed using both supplied full audits, especially the singular covariance differential, the conditional-density proof of support differentiation, and the Gaussian-dominated log-concave integral theorem. Every such dependency is proved in this manuscript rather than delegated to those files.

The direct right-difference-quotient argument in Section 11.3 is an internal elaboration of the envelope ending. Its additional continuity requirement is proved in Section 5.2. It changes neither the theorem's hypotheses nor its conclusion, and removes the need to assume a differentiability theorem about an envelope or its optimizers.

The supplied older weak-simplex writing examples informed the explanatory style, not the mathematical premises. The operator's normalized weak-simplex predecessor, arXiv:2607.14087v4, is not an independent competing discovery or an input to this proof. No result from it is needed here. The supplied methodological reading and writing checklist guided the attention to motivation, visible hypotheses, and complete dependencies; they are not evidence for any mathematical step.

No external source was retrieved for this manuscript. The proof has undergone private analytic criticism, not formal verification or public acceptance. Its mathematical content is the explicit argument given above, not the existence of those reviews.
