# Independent audit: all-dimensional raw Gaussian maximum comparison

**Date:** 2026-09-07.  
**Object reviewed:** `0012__ALL_DIMENSIONAL_FSC_PRESSURE_ENERGY_PROOF.md` and the required analytic sources inside `0013__fsc_pressure_energy_all_dimensions_2026-09-07.zip`.  
**Verdict:** the argument survives independent reconstruction and proves the stated raw, full-elliptope comparison in every dimension, with uniqueness at every fixed positive threshold. No unresolved analytic premise remains in the proof below. This is an analytic audit, not a formal verification, a priority assessment, or authorization for external mathematical reliance or publication.

The decisive hypothesis is **componentwise** positivity of the actual facet remainder. A positive sum of remainders is insufficient. The proposed proof does establish every individual positive remainder, with the intrinsic tangent dimension retained correctly. Its new finite-measure argument is valid, including equality.

The preceding critic's false-connected-azimuth objection remains an actual defect in the old four-site reconstruction. It is recorded in Section 12, not retrospectively erased. Neither that assertion nor its repair is a dependency of this proof.

## 0. Sources and independence boundary

The supplied standalone proof was read in full, including Appendices A--C, the alternative assembly, the correction identity, and the adverse examples. It is byte-identical to the copy in the new ZIP. The required historical sources inspected were:

* `inputs/0008__pair03_boundary_and_lifting_proof.md`, Sections 2--4 and Appendix A: the covariance differential, duplicate splitting, normalized lift, and the supplied logarithmic integral argument.
* `inputs/FSC_SUPPORT_STRESS_COMPRESSION_2026-09-07.md`, Sections 1--8: the actual-support/stress interfaces and the earlier unpaid conversion, distinguished from a proved premise.
* The current `FRONTIER(5).md`, the new archive's README, source ledger, and proof tree, as scope records, not evidence of validity.
* The preceding critic's `FIVE_SITE_INDEPENDENT_AUDIT.md`, especially Sections 0, 3--6, 8--9, 11, and 12--13, and its independent certificate program, as the authorized earlier critic material.
* `inputs/FSC_STATIONARY_LOCALIZATION_2026-09-06.md`, Section 4, solely to check the scope of the separately optimized five-facet adverse example. Its linked class-raising theorem is not used.

The archive's rival-method reports and unseen coordinator reviews were not mathematical inputs. No project/account memory or unsupplied conversation was queried. Presence of a file in a verified hash manifest does not mean its proof was read.

The only public source inspected was A. Prékopa, *On logarithmic concave measures and functions*, Acta Scientiarum Mathematicarum (Szeged) **34** (1973), 335--343: Theorem 6 and its proof, and the dimension-induction proof of Theorem 3. The author's reprint was inspected in parsed text and page images (PDF pages 3--4 and 8). This checked the precise marginal-log-concavity foundation, not the Gaussian comparison. Appendix A below independently reconstructs the supplied transport proof at the needed class, so no unproved external inequality is left as a premise. The source's other strictness theorems and broad sup-convolution measurability assertions are not used. Theorem 6 applies to a log-concave function, not necessarily a joint probability density in the support and integration variables; only the relevant fiber integrals must be finite. This matters because the support-vector variable is not integrated in the application.

Public source identifier, for reproducibility:

```text
https://rutcor.rutgers.edu/~prekopa/SCIENT2.pdf
```

## 1. Exact theorem and notation

Let
\[
\mathcal E_n=\{G\in\mathbb R^{n\times n}:G=G^\top\succeq0,
\quad G_{ii}=1\},\qquad
\Delta_n=\frac{nI-J}{n-1}.
\]
For \(X\sim N(0,G)\), set
\[
F_G(t)=\Pr(X_i\le t\text{ for all }i),\qquad D_n(t)=F_{\Delta_n}(t).
\]

**Theorem.** For every integer \(n\ge2\), every \(G\in\mathcal E_n\), and every real \(t\),
\[
F_G(t)\ge D_n(t).
\tag{1.1}
\]
For every fixed \(t>0\), equality holds exactly when \(G=\Delta_n\).

All singular ranks and all row sums are allowed. The theorem is not a comparison of optimized translates or tilted measures, is not a fixed-rank optimization theorem, and does not classify every stationary point or every local minimum.

Write \(\phi_m\) for the standard Gaussian density on \(\mathbb R^m\), \(\gamma_m\) for its measure, and \(\phi=\phi_1\), \(\Phi\) for the univariate density and CDF. Represent \(G=VV^\top\) using unit row vectors \(v_i\) spanning the **intrinsic** space \(\mathbb R^r\). Coordinate basis vectors used in matrix inequalities are denoted \(f_i\); they are not the scalar remainders \(e_i\).

## 2. The finite-measure lemma, independently proved

**Lemma 2.1.** Let \(\omega_i>0\), \(\sum_i\omega_i=1\), and let
\[
x_i=u_i+e_i,\qquad u_i>0,\quad e_i>0.
\]
Put
\[
X=\sum_i x_i,\quad U=\sum_i u_i,\quad E=\sum_i e_i,
\qquad a_i=u_i/U,\quad\nu_i=e_i/E.
\]
For \(M>0\), suppose, separately for every index,
\[
x_i\log\frac{x_i}{M\omega_i}
\ge u_i\left(\frac{a_i}{\omega_i}-1\right).
\tag{2.1}
\]
Then \(X\ge M\). If \(X=M\), then
\[
a_i=\nu_i=\omega_i,\qquad x_i=M\omega_i\quad\text{for every }i.
\tag{2.2}
\]
Conversely these patterns, with \(U+E=M\), satisfy every inequality with equality.

**Proof.** Convexity of \(s\log s\), whose second derivative is \(1/s>0\), applied to
\[
\frac{x_i}{X\omega_i}
=\frac UX\frac{a_i}{\omega_i}+\frac EX\frac{\nu_i}{\omega_i}
\]
gives
\[
x_i\log\frac{x_i}{X\omega_i}
\le u_i\log\frac{a_i}{\omega_i}+e_i\log\frac{\nu_i}{\omega_i}.
\]
Subtract this upper bound from (2.1). With \(\psi(v)=v-1-\log v\),
\[
x_i\log\frac XM
\ge u_i\psi(a_i/\omega_i)-e_i\log(\nu_i/\omega_i).
\tag{2.3}
\]
The function \(\psi\) is nonnegative, and vanishes only at one: its derivative is \(1-1/v\), so its unique minimum is \(\psi(1)=0\).

If \(X<M\), (2.3) and \(e_i>0\) force \(\nu_i>\omega_i\) for every index. This contradicts equality of their sums. If \(X=M\), they force \(\nu_i\ge\omega_i\) for every index, hence \(\nu=\omega\). Equation (2.3) then forces \(a_i=\omega_i\) for every index, since \(u_i>0\). Summing the two components proves (2.2). The converse is substitution. QED.

### 2.1 A small strengthening, not needed for the Gaussian proof

Componentwise **nonnegativity** \(e_i\ge0\) already suffices for the non-strict conclusion. Indeed, if some \(e_i=0\), then \(x_i=u_i\), and (2.1) at that index becomes
\[
\log(U/M)\ge\psi(a_i/\omega_i)\ge0.
\]
Thus \(U\ge M\), and \(X\ge M\), strictly if \(E>0\). If \(E=0\) and \(X=M\), applying this argument at all indices gives \(a=\omega\). If there are no zero remainders, Lemma 2.1 applies. Therefore equality in the nonnegative version is either the strictly positive pattern (2.2), or \(E=0\), \(x=u=M\omega\).

This strengthening does **not** allow negative individual remainders, even when their sum is positive; Section 12.1 gives an exact failure of that relaxation.

The strictly positive lemma also works on any probability space with positive integrable pressure and remainder densities and the corresponding pointwise inequality almost everywhere. Its proof is unchanged: a strict mass deficit would force the normalized remainder density to exceed the reference density almost everywhere, contradicting equality of integrals.

## 3. Covariance differentiation across singular ranks

Assume \(t>0\) and \(g_{ij}<1\) for all distinct indices. For \(-1<g_{ij}<1\), define
\[
q_{ij}(G,t)=
\frac{e^{-t^2/(1+g_{ij})}}{2\pi\sqrt{1-g_{ij}^2}}
\Pr(X_\ell\le t\ \forall\ell\ne i,j\mid X_i=X_j=t).
\tag{3.1}
\]
Set \(q_{ij}=0\) for \(g_{ij}=-1\). The conditioning at a nonantipodal pair is the Gaussian conditional law specified by its continuous affine mean and covariance; it is not an arbitrary version at a null conditioning event.

**Lemma 3.1.** Every \(q_{ij}\) is continuous on this distinct-coordinate part of the elliptope, at fixed \(t>0\), and
\[
F_H(t)-F_G(t)=\sum_{i<j}q_{ij}(G,t)(h_{ij}-g_{ij})+o(\|H-G\|)
\tag{3.2}
\]
as \(H\to G\) relative to \(\mathcal E_n\).

**Proof of conditional continuity.** At a nonantipodal pair, the conditional means and covariances depend continuously on \(G\). A remaining conditional coordinate can put an atom at its threshold only if its conditional variance vanishes and its conditional mean equals \(t\). In an intrinsic realization this says
\[
v_\ell=\alpha v_i+\beta v_j,\qquad t(\alpha+\beta)=t.
\]
Since \(t>0\), \(\alpha+\beta=1\). Unit norms then give
\[
1=\alpha^2+\beta^2+2\alpha\beta g_{ij}
=1-2\alpha\beta(1-g_{ij}).
\]
Thus \(\alpha\beta=0\), making \(v_\ell\) equal to \(v_i\) or \(v_j\), excluded. The union of the remaining threshold hyperplanes therefore has conditional probability zero even when the conditional covariance is singular. Gaussian conditional laws converge under convergence of their means and covariances, so their orthant probabilities converge.

At an antipodal limit, the conditional probability is at most one and
\[
0\le q_{ij}\le
\frac{e^{-t^2/(1+c)}}{2\pi\sqrt{1-c^2}}\longrightarrow0
\qquad(c\downarrow-1).
\]
This is why a singular antipodal pin is assigned zero, rather than an ordinary bivariate density. The argument does not apply at \(t=0\), nor does the theorem require it there.

**Proof of the differential.** At positive-definite \(G\), differentiating the Gaussian density in the common symmetric entries \(g_{ij}=g_{ji}\) gives \(\partial_{x_i}\partial_{x_j}\phi_G\). For example this follows directly by differentiating the determinant and quadratic form in the density; the coefficient is
\((G^{-1}x)_i(G^{-1}x)_j-(G^{-1})_{ij}\), precisely the density's mixed spatial derivative divided by the density. Integrating over the lower orthant twice leaves exactly the pair boundary integral (3.1). There is **no additional factor two**.

For singular endpoints, put
\[
G_\eta=(1-\eta)G+\eta I,\qquad H_\eta=(1-\eta)H+\eta I.
\]
Integrate the positive-definite differential along the segment between these two matrices. If \(H\) is near \(G\), all such segments lie in a compact set uniformly separated from repeated-coordinate matrices. The established continuity of the pin weights is uniform on this set, including antipodal limits. Passing to \(\eta\downarrow0\) gives
\[
F_H(t)-F_G(t)
=\int_0^1\sum_{i<j}
q_{ij}((1-s)G+sH,t)(h_{ij}-g_{ij})\,ds.
\]
Continuity of the weights at \(G\) proves (3.2).

Continuity of the CDF itself follows without a nonsingularity assumption: couple the laws using \(G^{1/2}Z\). PSD square roots are continuous, and each coordinate has a continuous \(N(0,1)\) marginal, so the threshold boundary is null. For completeness, continuity of PSD square roots follows from compactness of bounded square roots and uniqueness of the PSD square root: any convergent subsequence of roots has square equal to the limiting matrix. QED.

### 3.1 Geometric normalization cross-check

For a nonantipodal pair, the Jacobian of
\(x\mapsto(v_i\cdot x,v_j\cdot x)\) is \(\sqrt{1-g_{ij}^2}\). Consequently
\[
q_{ij}=\frac1{\sqrt{1-g_{ij}^2}}
\int_{\{v_i\cdot x=v_j\cdot x=t,\ v_\ell\cdot x\le t\}}
\phi_r(x)\,d\mathcal H^{r-2}(x).
\tag{3.3}
\]
This also follows by orthogonally decomposing the standard Gaussian into the two-dimensional span of the pinned normals and its complement. When \(r=2\), the last integral is zero-dimensional. When the feasible intersection has lower dimension than \(r-2\), its weight is zero.

## 4. Full-elliptope minima, positive rows, and intrinsic boundedness

### 4.1 Duplicate splitting is a strict feasible descent

Suppose \(X_i=X_j\) almost surely. Retain \(X_j\) and all other coordinates, and replace \(X_i\) by
\[
\cos\varepsilon\,X_i+\sin\varepsilon\,Z,
\]
where \(Z\) is an independent standard normal. The new success event is a subset of the old one, since the retained copy still imposes the old constraint. Conditional on every successful old sample, nonzero noise has a positive probability of violating the new constraint. The old event has positive probability at \(t>0\), because it contains an intrinsic ball around zero. The decrease is therefore strict. Its covariance tends to \(G\) as \(\varepsilon\to0\).

Every full-elliptope local minimum is consequently distinct-coordinate. For \(n\ge3\) it has intrinsic rank \(r\ge2\), because in rank one there are only two distinct unit normals.

### 4.2 The feasible normalized lift

Define the canonical stress by
\[
S_{ij}=q_{ij}\quad(i\ne j),\qquad
S_{ii}=-\sum_{j\ne i}g_{ij}q_{ij}.
\tag{4.1}
\]
For every \(z\in\mathbb R^n\), the unit normals
\[
v_i(\varepsilon)=
\frac{(v_i,\varepsilon z_i)}{\sqrt{1+\varepsilon^2z_i^2}}
\]
give a feasible full-elliptope variation, with
\[
g_{ij}(\varepsilon)-g_{ij}
=\varepsilon^2\left(z_i z_j-\frac{g_{ij}}2(z_i^2+z_j^2)\right)
+O(\varepsilon^4).
\]
Substitution in (3.2) yields
\[
F_{G(\varepsilon)}(t)-F_G(t)
=\frac{\varepsilon^2}{2}z^\top Sz+o(\varepsilon^2).
\tag{4.2}
\]
At a full-elliptope local minimum, \(S\succeq0\). No fixed-rank stationarity or honest-attainment theorem is being assumed.

### 4.3 An elementary proof that every row has a positive pin

Set
\[
k_i=\sum_{j\ne i}(1-g_{ij})q_{ij},\qquad
C_i=\sum_{j\ne i}\sqrt{1-g_{ij}^2}\,q_{ij},\qquad
\kappa=\sum_i k_i.
\tag{4.3}
\]
Terms at antipodal pairs are zero. For a fixed \(i\), retain the nonparallel other normals and write
\[
\sigma_{ij}=\sqrt{1-g_{ij}^2},\quad
w_{ij}=\frac{v_j-g_{ij}v_i}{\sigma_{ij}},\quad
\delta_{ij}=t\sqrt{\frac{1-g_{ij}}{1+g_{ij}}}>0.
\tag{4.4}
\]
At least one such normal exists, since \(r\ge2\). The \(w_{ij}\) are tangent unit normals. There cannot be two identical \(w\)'s with equal \(\delta\)'s: the function
\(g\mapsto t\sqrt{(1-g)/(1+g)}\) is strictly decreasing, so equal supports force equal correlations and then equal original normals.

Choose \(j\) minimizing \(\delta_{ij}\), and set \(y=\delta_{ij}w_{ij}\). For every retained \(\ell\),
\[
w_{i\ell}\cdot y\le\delta_{ij}\le\delta_{i\ell}.
\]
For \(\ell\ne j\), equality in both inequalities would require an identical tangent normal and equal support, which was excluded. Thus all the other constraints are **strict** at \(y\). Antipodal constraints on the physical pin are automatic because \(-t<t\).

It follows that the pair pin through \(tv_i+y\) has a relatively open feasible neighborhood in its \((r-2)\)-dimensional conditional support; in dimension zero the point itself is feasible. Its conditional Gaussian probability is positive. Thus \(q_{ij}>0\), and hence
\[
k_i>0,\qquad C_i>0\qquad\text{for every }i.
\tag{4.5}
\]
This proves ridge positivity **before** boundedness, without relying on a general polyhedral-face assertion.

### 4.4 PSD trace orthogonality supplies positive dependence

The stress diagonal makes
\[
\operatorname{tr}(GS)=0.
\]
If \(G,S\succeq0\), then
\(\operatorname{tr}(G^{1/2}SG^{1/2})=0\) implies
\(S^{1/2}G^{1/2}=0\). Hence \(GS=SG=0\). Also
\(S\mathbf1=k\), so
\[
a_i=\frac{k_i}{\kappa}>0,\qquad
\sum_i a_i=1,\qquad Ga=0.
\tag{4.6}
\]
In particular \(r\le n-1\), and \(\sum_i a_i v_i=0\).

The intrinsic cap
\[
K=\{x\in\mathbb R^r:v_i\cdot x\le t\text{ for all }i\}
\]
is bounded. Indeed, for each unit \(u\), not all \(v_i\cdot u\) can be nonpositive: the positive relation would force every one to be zero, contrary to spanning. Therefore
\(c=\min_{|u|=1}\max_i v_i\cdot u>0\), and \(K\subseteq B(0,t/c)\).

Everything from (4.3) onward applies to **any** distinct-coordinate configuration with its canonical stress PSD, regardless of whether it has already been identified as a minimum.

## 5. Support differentiation, including all projected degeneracies

The following elementary support-calculus fact is useful for both the physical cap and its facets.

**Lemma 5.1.** Let \(w_1,\ldots,w_m\) be unit vectors in \(\mathbb R^q\), and set
\[
h(b)=\Pr(w_j\cdot Y\le b_j\text{ for all }j),\qquad Y\sim N(0,I_q).
\]
At a support vector \(b\), suppose no pair of supporting hyperplanes coincides: if \(w_\ell=w_j\), assume \(b_\ell\ne b_j\); if \(w_\ell=-w_j\), assume \(b_\ell\ne-b_j\). Then \(h\) is continuously differentiable in a neighborhood of \(b\), and
\[
\partial_j h(b)=\phi(b_j)
\Pr(w_\ell\cdot Y\le b_\ell\ \forall\ell\ne j\mid w_j\cdot Y=b_j).
\tag{5.1}
\]

**Proof.** Condition on the standard normal \(w_j\cdot Y=s\). The remaining conditional variances are \(1-(w_\ell\cdot w_j)^2\). A conditional coordinate is deterministic only for a parallel or antiparallel pair, and its boundary is avoided precisely by the assumed support separation. All other conditional coordinates have nonzero variance. Thus the conditional event has boundary probability zero, and its probability is jointly continuous in \(s\) and the other supports near the specified point. Integrating that conditional probability against \(\phi(s)\) up to \(b_j\) gives (5.1). The derivative is continuous in all supports. Do this for every index; the separation conditions persist on a common open neighborhood. Continuous partial derivatives imply differentiability there. QED.

This proof handles redundant constraints, constraints touching only lower-dimensional faces, and nonsimple vertices. A redundant weaker parallel constraint has derivative zero. No assumption that every listed constraint is a facet is present.

### 5.1 Actual normalized facet masses

On the physical facet \(v_i\cdot x=t\), write \(x=tv_i+y\), \(y\perp v_i\). Antipodal constraints are automatic and are omitted. The tangent cap is
\[
P_i=\{y:w_{ij}\cdot y\le\delta_{ij}\text{ for all retained }j\},
\qquad H_i=\gamma_{d_0}(P_i),\qquad d_0=r-1.
\tag{5.2}
\]
It is bounded, has positive dimension, and contains zero in its interior. Define \(h_i(b)\) using the same tangent normals and variable supports.

Equal projected normals have unequal actual supports, as proved in Section 4.3. Opposite projected normals cannot have coincident hyperplanes at positive supports. Lemma 5.1 therefore applies at the actual support vector, even if the facet is nonsimple or some projected constraints are redundant.

The derivative normalization can be checked by conditional densities, without an appeal to a moving-face formula. Given \(X_i=t\), the coordinate \(X_j\) has mean \(g_{ij}t\), standard deviation \(\sigma_{ij}\), and standardized value \(\delta_{ij}\) at its boundary. Hence
\[
\phi_2(t,t;g_{ij})
=\frac{\phi(t)\phi(\delta_{ij})}{\sigma_{ij}},
\]
and (5.1), with the remaining conditional probability, gives
\[
\boxed{\partial_j h_i(\delta_i)
=\frac{\sigma_{ij}q_{ij}}{\phi(t)}.}
\tag{5.3}
\]
This agrees with the coarea normalization (3.3).

Apply Lemma 5.1 also to the physical normals at support \(t\mathbf1\). Distinct normals cannot have coincident positive-threshold supporting hyperplanes, including antipodal pairs. Thus the fixed-shape CDF is continuously differentiable for positive thresholds, and
\[
\boxed{F_G'(t)=\phi(t)\sum_iH_i.}
\tag{5.4}
\]
In fact (5.3) also gives the independent cross-check
\[
H_i'(t)=\frac{k_i}{\phi(t)}>0,
\tag{5.5}
\]
because every \(\delta_{ij}\) scales linearly with \(t\). No differentiability in a moving minimizing covariance or an optimized translation is used.

### 5.2 Log-concavity in supports

For fixed normals, the function \(\log h_i\) is concave wherever its mass is positive. If \(x\in P(b)\) and \(y\in P(c)\), then
\[
(1-s)x+sy\in P((1-s)b+sc).
\]
The Gaussian density is log-concave because squared norm is convex. Apply the logarithmic integral inequality reconstructed in Appendix A to the three Gaussian densities restricted to these three convex caps. This gives
\[
h_i((1-s)b+sc)\ge h_i(b)^{1-s}h_i(c)^s.
\tag{5.6}
\]
This is ordinary log-concavity, not Ehrhard probit concavity. Neither centeredness nor evenness of the cap is required. All nonempty caps for these fixed tangent normals are bounded: a nonzero common recession direction would already make the actual cap unbounded. Equivalently, the minimum over tangent unit directions of the maximum tangent-normal inner product is strictly positive. Thus the bounded, compactly supported version of the integral theorem proved in Appendix A suffices for every support comparison used here.

The positive-support segment between the actual vector and the reference vector is inside the positive-mass domain, so the differentiable concave upper-tangent inequality at the actual vector is legitimate. The equal-support reference itself may have redundant ties; **no derivative at that reference is used**.

## 6. The all-dimensional boundary comparison

Assume \(n\ge3\), \(t>0\), distinct coordinates, and canonical \(S\succeq0\). Set
\[
d=n-2,\qquad d_0=r-1\le d,\qquad
A_i=\frac{C_i}{k_i},\qquad
A_* =\sqrt{\frac dn},\qquad \rho=\frac{t}{A_*}.
\]

### 6.1 The two rowwise Cauchy inequalities

Scalar Cauchy--Schwarz gives
\[
C_i^2\le
\left(\sum_{j\ne i}(1-g_{ij})q_{ij}\right)
\left(\sum_{j\ne i}(1+g_{ij})q_{ij}\right)
=k_i(k_i-2S_{ii}).
\tag{6.1}
\]
PSD Cauchy--Schwarz, applied to \(S^{1/2}f_i\) and \(S^{1/2}\mathbf1\), gives
\[
k_i^2\le S_{ii}\kappa.
\tag{6.2}
\]
Thus
\[
0<A_i\le\sqrt{1-2a_i},\qquad 0<a_i<1/2.
\tag{6.3}
\]
The strict upper bound on \(a_i\) follows from \(C_i>0\), not from an assumption of honest rank.

Put \(\zeta_i=na_i\). Since
\[
\frac{1-2a_i}{A_*^2}=1-\frac{2(\zeta_i-1)}d>0,
\]
the elementary tangent inequality \(\sqrt{1+s}\le1+s/2\) gives
\[
\boxed{d(1-A_i/A_*)\ge na_i-1.}
\tag{6.4}
\]
It is valid when the right side is negative as well as when it is positive. Extreme positive weights require no separate threshold regime.

### 6.2 A common reference and the logarithmic support inequality

Let \(p_0>0\) satisfy
\[
h_i(\rho\mathbf1)\ge p_0\qquad\text{for every }i.
\tag{6.5}
\]
The concave upper tangent to \(\log h_i\) at \(\delta_i\), together with (5.3), gives
\[
\begin{aligned}
\log p_0
&\le\log H_i+\frac1{H_i}
\sum_j\partial_jh_i(\delta_i)(\rho-\delta_{ij}),\\
H_i\log(H_i/p_0)
&\ge\frac{tk_i-\rho C_i}{\phi(t)}
=\frac{tk_i}{\phi(t)}(1-A_i/A_*).
\end{aligned}
\tag{6.6}
\]
All appearances of \(q_{ij}\) are the same canonical pins at the same \(G,t\).

### 6.3 The actual-facet energy identity

For positive \(s\), \(h_i(s\delta_i)=\gamma_{d_0}(sP_i)\). Change variables in the Gaussian integral:
\[
\gamma_{d_0}(sP_i)=s^{d_0}\int_{P_i}\phi_{d_0}(sy)\,dy.
\]
The domain \(P_i\) is bounded, so differentiation under the integral is immediate. At \(s=1\),
\[
\sum_j\delta_{ij}\partial_jh_i(\delta_i)
=d_0H_i-\int_{P_i}|y|^2\,d\gamma_{d_0}(y).
\]
Equation (5.3) identifies the left side as \(tk_i/\phi(t)\). Consequently, with
\[
u_i=\frac{tk_i}{d\phi(t)},\qquad e_i=H_i-u_i,
\]
we have
\[
\boxed{
H_i=u_i+e_i,\qquad
 e_i=\frac{(d-d_0)H_i+\int_{P_i}|y|^2\,d\gamma_{d_0}(y)}d>0.
}
\tag{6.7}
\]
Every \(u_i>0\) by Section 4.3. Every energy integral is strictly positive because \(d_0\ge1\) and \(P_i\) contains a nonempty open ball. The actual tangent Gaussian is always \(\gamma_{d_0}\); \(d\) is only the normalization and an upper bound on \(d_0\). Lower rank supplies the additional nonnegative dimension-defect term, rather than invalidating the identity.

Equivalently,
\[
\frac{u_i}{H_i}
=\frac{d_0-\mathbb E(|Y|^2\mid Y\in P_i)}d\in(0,1),
\qquad
H_i-\frac t d H_i'(t)>0.
\tag{6.8}
\]
No uniform lower bound on \(e_i/H_i\) as \(t\downarrow0\) is required.

Finally,
\[
\frac{u_i}{\sum_j u_j}=\frac{k_i}{\kappa}=a_i.
\tag{6.9}
\]
Combining (6.4), (6.6), and (6.7) gives exactly
\[
H_i\log(H_i/p_0)\ge u_i(na_i-1),\qquad H_i=u_i+e_i,
\quad u_i,e_i>0.
\tag{6.10}
\]
Apply Lemma 2.1 with \(x_i=H_i\), \(\omega_i=1/n\), and \(M=np_0\). Therefore
\[
\boxed{F_G'(t)\ge n\phi(t)p_0.}
\tag{6.11}
\]
This proves the all-threshold, arbitrary-rank boundary theorem. No comparison of independent optimized facets is asserted.

## 7. Boundary equality is rigid

Suppose equality holds in (6.11). Lemma 2.1 yields
\[
a_i=1/n,\qquad H_i=p_0\quad\text{for every }i.
\]
Now (6.3) gives \(A_i\le A_*\), and (6.6) gives
\[
0\ge\frac{tk_i}{\phi(t)}(1-A_i/A_*)\ge0.
\]
Thus \(A_i=A_*\) for every index. Both (6.1) and (6.2) are equalities, since
\[
A_*^2=A_i^2\le1-2S_{ii}/k_i\le1-2a_i=A_*^2.
\]
In particular \(k_i=\kappa/n\) and \(S_{ii}=\kappa/n^2\). Equality in PSD Cauchy--Schwarz gives
\[
S^{1/2}f_i=\frac1nS^{1/2}\mathbf1\quad\text{for every }i,
\]
so
\[
S=\frac{\kappa}{n^2}J.
\tag{7.1}
\]
Every off-diagonal \(q_{ij}\) is therefore the same strictly positive number. In particular there is no antipodal pair.

Equality in the scalar rowwise Cauchy inequality then says that
\((1+g_{ij})/(1-g_{ij})\) is constant over \(j\ne i\), for every row. Symmetry makes the off-diagonal correlations all equal. Also \(G\mathbf1=0\), since \(Gk=0\) and \(k\) is uniform. Hence their common value is \(-1/(n-1)\), and
\[
G=\Delta_n.
\tag{7.2}
\]
No equality theorem for support log-concavity, no lower-size uniqueness theorem, and no classification of stationary shapes is used.

## 8. Full-domain minimum-envelope assembly

### 8.1 Attainment, positivity, and absolute continuity

For \(t\ge0\), define
\[
m_n(t)=\min_{G\in\mathcal E_n}F_G(t).
\]
The elliptope is compact: it is closed and every entry belongs to \([-1,1]\). Joint continuity in \((G,t)\) follows from the square-root coupling in Section 3 and the nullity of each standard-normal marginal threshold. Thus the minimum exists.

For \(t>0\), a uniform positive bound is available: in the \(n\)-dimensional representation \(X=G^{1/2}Z\), every row of \(G^{1/2}\) has norm one. The event \(|Z|<t\) implies every score is below \(t\). Therefore
\[
m_n(t)\ge\gamma_n(B(0,t))>0.
\tag{8.1}
\]
For \(h\ge0\), the marginal union bound gives
\[
0\le F_G(t+h)-F_G(t)
\le n[\Phi(t+h)-\Phi(t)].
\]
Monotonicity passes to the minimum. For the upper bound choose a minimizer at \(t\), obtaining
\[
0\le m_n(t+h)-m_n(t)
\le n[\Phi(t+h)-\Phi(t)].
\tag{8.2}
\]
Thus \(m_n\) is Lipschitz and absolutely continuous on every compact threshold interval, including intervals starting at zero.

Regular scores sum to zero almost surely and have rank \(n-1\ge1\). All of them being nonpositive therefore forces all of them to vanish, an event of probability zero. Consequently
\[
m_n(0)=D_n(0)=0.
\tag{8.3}
\]

### 8.2 The reference-padding step is unconditional

Fix a positive differentiability point of \(m_n\), and choose **any** minimizing covariance \(G\). It has no duplicates and has canonical PSD stress by Section 4. Its fixed-shape profile \(s\mapsto F_G(s)\) is differentiable at \(t\) by Section 5 and touches \(m_n\) from above. The difference is zero there and differentiable, so
\[
m_n'(t)=F_G'(t).
\tag{8.4}
\]
No measurable choice or differentiability of a moving minimizer is involved.

Each tangent reference cap has between one and \(n-1\) retained unit constraints. Duplicate constraints as necessary to reach exactly \(n-1\) scores. Their Gram matrix is a legitimate \((n-1)\)-score correlation matrix, possibly singular and containing repetitions. Duplicating a constraint changes neither its event nor its probability. Hence
\[
h_i(\rho\mathbf1)\ge m_{n-1}(\rho)>0,
\qquad \rho=t\sqrt{\frac n{n-2}}.
\tag{8.5}
\]
This invokes only the **definition** of the lower-size minimum, not a previously proved lower-size root. No derivative at this possibly tied reference vector is needed.

Use (8.5) as the common \(p_0\) in (6.11). We obtain the unconditional recursion
\[
\boxed{
m_n'(t)\ge n\phi(t)
 m_{n-1}\!\left(t\sqrt{\frac n{n-2}}\right)
\quad\text{for almost every }t>0,\quad n\ge3.
}
\tag{8.6}
\]

### 8.3 The base and the regular recursion

For two scores and \(t>0\), the union bound gives
\[
F_G(t)\ge2\Phi(t)-1=D_2(t),
\]
with equality attained by the antipodal covariance. Thus \(m_2=D_2\).

For \(\Delta_n\), pin one score at \(t\). Each remaining conditional mean is \(-t/(n-1)\), each conditional variance is
\[
1-\frac1{(n-1)^2}=\frac{n(n-2)}{(n-1)^2},
\]
and distinct remaining conditional covariances are
\[
-\frac1{n-1}-\frac1{(n-1)^2}=-\frac n{(n-1)^2}.
\]
After standardization the conditional Gram matrix is \(\Delta_{n-1}\), and its common threshold is \(t\sqrt{n/(n-2)}\). Therefore (5.4) gives
\[
D_n'(t)=n\phi(t)
D_{n-1}\!\left(t\sqrt{\frac n{n-2}}\right).
\tag{8.7}
\]
This includes \(n=3\), where the conditional pair is antipodal; \(n=2\) was handled separately.

Induct on \(n\). If \(m_{n-1}=D_{n-1}\), equations (8.6)--(8.7) and absolute continuity, integrated from zero, give \(m_n\ge D_n\). Feasibility of \(\Delta_n\) gives \(m_n\le D_n\), so equality holds. This proves (1.1) for all nonnegative thresholds and every \(n\ge2\). For negative thresholds, \(D_n(t)=0\) because regular scores sum to zero, so the comparison is immediate.

### 8.4 Uniqueness at every positive threshold

Suppose \(F_G(t_0)=D_n(t_0)\) for some fixed \(t_0>0\). The already established root makes \(G\) a global minimizer at that threshold, hence distinct-coordinate with PSD canonical stress. The function \(F_G(t)-D_n(t)\) is nonnegative at every threshold and has an interior zero at \(t_0\). Its derivative therefore vanishes there.

Take \(p_0=D_{n-1}(t_0\sqrt{n/(n-2)})\) in the boundary theorem. Equation (8.7) identifies the matched derivative with equality in (6.11). Section 7 forces \(G=\Delta_n\). This works at every positive threshold, not merely almost everywhere.

For \(n=2\), equality in the union bound requires the two upper-tail events to have zero intersection. At any correlation strictly above \(-1\), their intersection has positive probability: for correlations in \((-1,1)\) the joint density is positive on the upper quadrant, and at correlation one the intersection is the single standard-normal upper tail. Thus the antipodal covariance is the unique positive-threshold equality case.

## 9. Independent assembly by a negative joint minimum

This checks the integration argument without differentiating the envelope.

Assume the lower-size root, and suppose \(F_G(t)-D_n(t)\) is negative at some \((G,t)\). Uniformly in \(G\),
\[
F_G(t)-D_n(t)\ge-D_n(t)\longrightarrow0\quad(t\downarrow0),
\]
and
\[
F_G(t)-D_n(t)\ge-n[1-\Phi(t)]\longrightarrow0\quad(t\to\infty).
\]
Choose a witnessed negative value. These bounds exclude sufficiently small and sufficiently large thresholds from a sublevel set below half that value. Compactness of the elliptope and joint continuity then give a negative global joint minimum at \((G_*,t_*)\), with \(0<t_*<\infty\).

For fixed \(t_*\), minimizing this CDF difference is exactly minimizing \(F_G(t_*)\), since the subtracted term is constant in \(G\). Thus the full-elliptope PSD-stress argument applies to \(G_*\). Threshold stationarity gives
\[
F_{G_*}'(t_*)=D_n'(t_*).
\]
The lower-size root supplies the regular reference, and the boundary equality theorem forces \(G_*=\Delta_n\), contradicting the negative value. Induction from two scores proves the same all-dimensional theorem.

The objective matters. At a joint critical point of a **ratio** one instead has
\[
\left(F_G/D_n\right)'=0
\quad\Longrightarrow\quad
F_G'=\frac{F_G}{D_n}D_n'.
\]
At a fixed positive threshold, a positive ratio denominator leaves shape minimizers unchanged; it is the threshold matching equation and the endpoint attainment problem that differ. An optimized or tilted objective may also change the shape differential itself. None of those equations is substituted into the CDF-difference proof above.

The two assemblies are independent checks of the final step, not independent proofs of the common boundary theorem.

## 10. Retained nonnegative losses and strictness

The following identities are consequences of the checked proof, not additional premises. Let
\[
P=\sum_iH_i,\quad U=\sum_i u_i,\quad E=\sum_i e_i,
\qquad\nu_i=e_i/E.
\]
Define
\[
\mathcal R_i=1-A_i/A_*-(na_i-1)/d\ge0,
\]
\[
\mathcal T_i=H_i\log(H_i/p_0)
-\frac{tk_i}{\phi(t)}(1-A_i/A_*)\ge0,
\]
and
\[
\begin{aligned}
\mathcal J_i
&=u_i\log(na_i)+e_i\log(n\nu_i)
-H_i\log(nH_i/P)\\
&=H_i\,d_{\mathrm{Ber}}(u_i/H_i\,\Vert\,U/P)\ge0.
\end{aligned}
\tag{10.1}
\]
The last identity follows by expanding the two Bernoulli relative-entropy terms; its sign also follows directly from convexity of \(s\log s\), as in Lemma 2.1. Every argument lies strictly between zero and one where required, by (6.7).

Direct cancellation gives
\[
\boxed{
H_i\log\frac{P}{np_0}+e_i\log(n\nu_i)
=u_i\psi(na_i)+\frac{tk_i}{\phi(t)}\mathcal R_i
+\mathcal T_i+\mathcal J_i.
}
\tag{10.2}
\]
At least one \(i\) has \(\nu_i\le1/n\). At that index the second term on the left is nonpositive and every term on the right is nonnegative. Thus (10.2) is a pointwise certificate of the boundary comparison. It retains rather than discards the information in the remainder distribution.

### 10.1 An explicit split of the geometric loss

Set
\[
\mathscr D_i=S_{ii}-k_i^2/\kappa\ge0,
\qquad
\mathscr V_i=k_i(k_i-2S_{ii})-C_i^2\ge0.
\]
Then
\[
k_i^2(1-2a_i)-C_i^2=2k_i\mathscr D_i+\mathscr V_i.
\tag{10.3}
\]
For \(\zeta_i=na_i\), let
\[
L_i=1-(\zeta_i-1)/d,
\qquad B_i=\sqrt{1-2(\zeta_i-1)/d}.
\]
All denominators below are positive by (6.3), and rationalizing the two square-root differences yields the exact decomposition
\[
\boxed{
\mathcal R_i=
\frac{(\zeta_i-1)^2}{d^2(L_i+B_i)}
+\frac{2k_i\mathscr D_i+\mathscr V_i}
 {A_* k_i^2(\sqrt{1-2a_i}+A_i)}.
}
\tag{10.4}
\]
Thus pressure-weight imbalance, PSD Cauchy loss, scalar Cauchy loss, support-log-concavity loss, and the binary log-sum loss are all visible and nonnegative.

These formulas give exact boundary strictness; they do not themselves provide a uniform CDF stability constant in terms of a matrix norm. Such a statement would require further estimates connecting these actual facet quantities to shape distance and integrating them with suitable control. No such additional claim is made.

### 10.2 A related intrinsic identity, not needed by the proof

Tangential Gaussian integration by parts gives
\[
\int_{P_i}y\,d\gamma_{d_0}(y)
=-\sum_jw_{ij}\partial_jh_i(\delta_i)
=-\frac{(SV)_i}{\phi(t)}.
\]
Here the first equality is the divergence theorem componentwise on the bounded polytope; lower-dimensional intersections do not contribute surface measure. Since \(GS=0\) implies \(SV=0\) (multiply \(SG=SVV^\top=0\) by a right inverse of \(V^\top\)), PSD canonical stress centers every actual tangent facet. The new proof did not need this centering identity, an optimized translation, or an equality theorem for log-concavity.

## 11. What removed the dimension-specific obstruction

The earlier five-site method combined a rowwise lower floor with a joint inequality for inverse-normal facet masses. Converting that information back to total probability required a low-threshold scalar classification and a high-threshold tangent conversion. In six scores the kernel-only scalar inequality can already reverse.

The present argument changes the information retained, not merely the threshold constant or the name of the transform. Ordinary support log-concavity gives an inequality involving **both** actual mass and actual support pressure. Gaussian homothety identifies the difference between those two actual quantities as a positive measure in each component. The finite-measure lemma then converts the componentwise inequalities into a total-mass bound for arbitrary dimension and threshold.

The precise interface is
\[
\text{canonical }q_{ij}
\longrightarrow\partial_jh_i(\delta_i)
\longrightarrow
H_i=\frac{tk_i}{(n-2)\phi(t)}+e_i,
\quad e_i>0.
\]
Neither free stress weights nor independently optimized facets preserve this interface automatically. That is why the old relaxed counterexamples survive while the actual coupled proof closes.

## 12. Adverse controls and the inherited defect

### 12.1 Positive total remainder is insufficient

Take \(n=3\), \(p_0=1/2\), and
\[
x=(3/5,1/512,1/512),\qquad
u^{\rm press}=(9/50,27/200,27/200).
\]
In this subsection write \(u=u^{\rm press}\); these are abstract scalars, not Gaussian data. Then
\[
U=9/20,\quad a=(2/5,3/10,3/10),\quad
X=773/1280<3/2,
\quad X-U=197/1280>0.
\]
Nevertheless every component satisfies
\[
x_i\log(x_i/p_0)\ge u_i(3a_i-1).
\]
For the first component, \(\log(6/5)\ge1/6\), by integrating \(1/s\) on \([1,6/5]\), gives a left side at least \(1/10>9/250\). For each small component, the left side is \(-\log2/64\). Strict convexity of \(1/s\) gives the strict trapezoidal bound \(\log2<3/4\), so this exceeds \(-3/256>-27/2000\).

Even the stronger square-root right side
\(u_i[1-\sqrt{1-2(3a_i-1)}]\) is satisfied: use
\(\sqrt{3/5}>2/3\) and \(\sqrt{6/5}>87/80\), both checked by rational squaring. The remainders are
\[
x-u=(21/50,-1703/12800,-1703/12800).
\]
Thus this is a failure of the **weakened** total-remainder hypothesis, not a failure of Lemma 2.1 or a Gaussian counterexample.

### 12.2 A concrete projected-duplicate and antipodal test

Use the planar unit normals
\[
(1,0),\quad(0,1),\quad(3/5,4/5),\quad(-1,0),\quad(0,-1).
\]
At the facet \(x=t\), the two upward tangent normals coincide, with actual supports \(t\) and \(t/2\). The downward support is \(t\), and the antipodal original constraint is automatic. Therefore
\[
H_i=\gamma_1([-t,t/2])=\Phi(t/2)+\Phi(t)-1.
\]
The weaker upward constraint has derivative zero; the active upward derivative is \(\phi(t/2)\). At equal reference supports the two upward constraints tie, so individual reference derivatives need not exist. The proof never differentiates there. This is an actual singular configuration testing exactly the distinction between the actual and reference support vectors; PSD stress is not asserted for it.

### 12.3 An actual nonsimple, higher-corank test

Let the eight normals be
\[
v_s=s/\sqrt3,\qquad s\in\{-1,1\}^3.
\]
Their physical cap is the octahedron
\[
|x_1|+|x_2|+|x_3|\le\sqrt3\,t.
\]
Four facets meet at each vertex, so the cap is nonsimple. Adjacent facets correspond to sign vectors differing in one coordinate, with correlation \(1/3\), and have a common positive canonical ridge weight \(q(t)\) by symmetry. Facets differing in two coordinates meet only at a vertex, so their pair-pin weight is zero: the conditional Gaussian dimension is one and the feasible set is a singleton. Opposite facets are antipodal and have weight zero.

Consequently the canonical stress is
\[
S=q(t)(A_{\rm cube}-I),
\]
with every diagonal equal to \(-q(t)<0\). The cube characters \(\prod_{j\in A}s_j\) have adjacency eigenvalue \(3-2|A|\), so the stress spectrum divided by \(q(t)\) is
\[
2\ (1\text{ time}),\quad0\ (3),\quad-2\ (3),\quad-4\ (1).
\]
This gives a strict feasible lift descent and excludes this actual nonsimple configuration from local minima. It also directly checks that lower-dimensional face contacts carry zero first-order pin weight, rather than requiring a simplicial or simple-polytope hypothesis. The rational Gram and matrix statements are replayed in `audit_controls.py`; the Gaussian ridge identification is the analytic argument just given.

### 12.4 The actual six-site axial witness remains nonminimizing

At \(t=9/8\), put
\[
c=49/51,\qquad b=2351/2601=(5c^2-1)/4,
\]
and define a six-score covariance with apex-base correlations \(-c\) and all distinct base-base correlations \(b\). It has the exact kernel
\[
a=(49/100,51/500,51/500,51/500,51/500,51/500).
\]
Its eigenvalues are zero, \(250/2601\) with multiplicity four, and \(14606/2601\). One direct realization is
\(v_0=-e_5\), \(v_j=ce_5+\sqrt{1-c^2}\,w_j\), where the \(w_j\) form a regular five-site simplex in \(e_5^\perp\). Hence feasibility and rank five are exact, not numerical eigenvalue judgments.

Let \(q_A\) and \(q_B\) be its apex-base and base-base pin weights. Every base diagonal stress is
\[
S_{jj}=c q_A-4bq_B.
\]
The apex-base density bound gives
\[
q_A<2^{-32},
\]
since \(t^2/(1-c)=4131/128>32\), \(2\pi\sqrt{1-c^2}>1\), and \(e>2\).

For a base-base pin, the residual Gaussian is three-dimensional. Each remaining base constraint has residual margin
\(t(1-b)/(1+b)>1/20\); the apex margin is larger than \(t\). Every residual normal has norm at most one. The cube \([-1/40,1/40]^3\) is therefore feasible, since \(\sqrt3/40<1/20\). Its Gaussian probability exceeds \(1/512000\): its volume is \(1/8000\), and its density is greater than \(1/64\), using \(\pi<4\) and \(e^{-x}\ge1-x\). The pair density exceeds \(1/32\), because \(t^2/(1+b)<3/4\), its exponential numerator exceeds \(1/4\), and its denominator is less than eight. Hence
\[
q_B>1/16384000.
\]
It follows exactly that
\[
\boxed{
S_{jj}<\frac{c}{2^{32}}-\frac{4b}{16384000}
=-\frac{307837897}{1396401242112000}<0.
}
\tag{12.1}
\]
The lift \(z=f_j\) in (4.2) gives a strict feasible descent. Thus this covariance is not a local minimum.

The older kernel-only scalar witness is also retained. The unchanged preceding critic's certificate, replayed in this audit, gives
\[
D_5((9/8)\sqrt{250/199})
\in[0.5237301959862456,0.5237301959862457]
\]
and bounds the kernel-only sum gap above by \(-0.0062421174704335\). These are exact scalar statements from the earlier radial-moment certificate, not a negative Gaussian covariance comparison. The new proof neither asserts the false kernel-only sum inequality nor mistakes these kernel weights for the canonical stress weights of the nonstationary axial covariance.

### 12.5 Other rejected transfers

The cube with normals \(\pm e_1,\pm e_2,\pm e_3\) has canonical stress spectrum
\(q(4,-2,-2,0,0,0)\), with \(q=\phi(t)^2D_2(t)>0\), so it is likewise outside the PSD-stress class. The supplied exact verifier checks this algebra.

Artificial positive matrices satisfying \(GS=0\) and formal closure identities do not supply the support derivative (5.3); only the canonical Gaussian \(q_{ij}\) do. The supplied artificial two-triangle example is therefore not a counterexample to the boundary theorem.

The separately optimized five-facet example in the inspected localization source has a different construction: each facet is allowed an independent translation. Its translation-dependent pressure need not coincide with the original canonical row. The analytic tail comparison in that source is compatible with the new theorem. No class-raising theorem, independently optimized facet completion, or uninspected spectral certificate is imported here.

A fixed-rank or balanced-constrained minimum need not allow every normalized rank lift. Without those admissible directions, PSD of the canonical stress has not been established by (4.2). The full-elliptope theorem is not silently transported to a different feasible class.

### 12.6 The old four-site connected-azimuth defect stays recorded

The earlier four-site reconstruction asserted that an arbitrary convex-cone/cap intersection avoiding the cap center has connected azimuthal sections. This is false. Let
\[
P=(0,0,1),\quad R=\pi/4,\quad
\mathcal C=\{(x,y,z):z\ge0,\ z/4\le x\le z/2,\ |y|\le z\}.
\]
The cone is closed, convex, pointed, and does not contain \(P\). At latitude \(\theta=\arctan(3/4)<R\), its angular section is
\[
1/3\le\cos\varphi\le2/3,
\]
which consists of two disjoint nondegenerate intervals. The \(y\)-constraint is automatic because \(|y|/z\le3/4\).

This invalidates the advertised general section argument, not the cap-cut inequality itself. The preceding critic repaired the four-site application by restricting to an outer great-circle segment clipped by one fixed angular sector. Such a piece has width
\[
v(\theta)=|I\cap[-q_a(\theta),q_a(\theta)]|,
\qquad q_a(\theta)=\arccos(\tan a\cot\theta).
\]
Its width derivative is bounded by that of the uncut equal-area comparison segment, giving the required single-crossing comparison. That specialized repair, not the false general assertion, is the retained geometric route.

The preceding audit also recorded a separate wording error about the strict alternative for the negative orthant. Neither that sentence nor any nonpositive-threshold equality classification is needed here.

**Dependency disposition:** the new induction starts at two scores and uses only Sections 2--8 above. It does not need the geometric four-score theorem, its repair, the old honest-attainment theorem, an optimized translation, Ehrhard's inequality, or any three-through-five cutoff certificate. The old defect has not become true; it has become irrelevant to this new proof.

## 13. Independence of the earlier two-through-five proof

The preceding critic's scalar induction at thresholds \(7/10\), \(9/10\), and \(51/50\) is an independent check of the **mass-conversion portion** of the new theorem through five scores. Its scalar classifications and probit transition certificates are different from the pressure/energy/log-sum argument.

It is not a completely disjoint end-to-end proof. Both routes use the relative covariance differential, full-elliptope lift, canonical stress, actual-support derivative, and minimum-envelope method. Those shared interfaces were reconstructed above, with a simpler minimum-support proof of row positivity and a conditional-probability proof of actual-support differentiability. No prior approval of a shared interface was substituted for its proof.

The earlier repaired spherical four-score theorem supplies an additional geometric control in low dimension. It is optional. The new unconditional recursion (8.6) prevents any circular use of the five-score or all-dimensional root in obtaining the reference masses.

## 14. Corrected dependency tree and status

```text
Elementary Gaussian density/conditioning and linear algebra
  +-- conditional boundary-atom exclusion at distinct coordinates, t>0
  |     +-- relative covariance differential across ranks
  |           +-- duplicate splitting and feasible normalized lift
  |                 +-- canonical stress PSD at full-elliptope minima
  |
  +-- no tied actual projected support planes
  |     +-- minimum-support foot -> every k_i,C_i positive
  |     +-- support derivative = sigma_ij q_ij / phi(t)
  |
  +-- PSD trace orthogonality GS=0
        +-- positive kernel; 2 <= r <= n-1; bounded intrinsic cap
        +-- rowwise scalar/PSD Cauchy inequalities

One-dimensional monotone transport + dimension induction (Appendix A)
  +-- fixed-normal Gaussian support log-concavity

Actual support derivative + Gaussian homothety in dimension r-1
  +-- componentwise H_i = u_i + e_i, u_i,e_i>0

Support log-concavity + row geometry + positive componentwise split
  +-- finite-measure lemma
        +-- all-threshold boundary comparison for canonical PSD stress
        +-- boundary equality forces Delta_n

Compactness + marginal Lipschitz bound + reference padding
  +-- unconditional recursion for attained minima
        +-- elementary two-score base + regular pin recursion
              +-- full all-dimensional raw root
              +-- equality at every positive threshold

Alternative assembly:
  same boundary theorem + uniform endpoint lower bounds for F_G-D_n
    +-- attained negative joint minimum -> contradiction
```

| Claim | Audit status |
|---|---|
| Weighted finite-measure lemma, including equality | Proved in Section 2 |
| Componentwise nonnegative-remainder strengthening | Proved in Section 2.1; not needed |
| Singular relative differential and full lift normalization | Reconstructed in Sections 3--4 |
| Positive row before boundedness | Reproved by the minimum-support foot in Section 4.3 |
| Redundant, antipodal, projected-duplicate, nonsimple support calculus | Reconstructed in Section 5 |
| Correct intrinsic-dimension energy identity | Proved in Section 6.3 |
| Boundary comparison and rigidity at every positive threshold | Proved in Sections 6--7 |
| Unconditional minimum recursion and all-dimensional root | Proved in Section 8 |
| CDF-difference joint-minimum alternative | Independently assembled in Section 9 |
| Exact correction and geometric splits | Proved in Section 10 |
| Old general connected-azimuth assertion | False; retained explicitly in Section 12.6 |
| Old specialized four-site repair | Preserved as an optional earlier route, not a new premise |
| Six-site scalar reversal | Preserved; exact scalar control only |
| Actual six-site axial covariance | Exactly excluded from the minimizing locus |
| Optimized-tilt, fixed-rank, full stationary classification, uniform stability | Not established or asserted by this audit |

## 15. Code execution and assurance boundary

Every supplied program executed in this audit was read before execution. Scripts were copied to replay directories first, so neither the supplied archive nor the preceding critic's inputs were overwritten.

1. All 29 entries in the new archive's `SHA256SUMS.txt` verified. The standalone proof and archived proof were byte-identical.
2. The supplied `verify_algebra.py` completed. Its `exact_checks.json` was byte-identical to the supplied expected output. It checks formal algebraic identities, finite rational stress identities, the cube spectrum, and the abstract scalar falsifier. It does not verify Gaussian support concavity or the continuum theorem.
3. The unchanged preceding critic's `independent_certificates.py` completed. Its JSON was byte-identical to the output in the preceding critic's ZIP. It independently retains the two-through-five exact scalar signs and the six-site scalar/actual-covariance controls. These computations are not dependencies of Sections 2--9.
4. The newly authored standard-library `audit_controls.py` completed. It checks the explicit projected-duplicate support data, exact nonsimple octahedral Gram/stress identities, and every rational premise in the six-site diagonal-stress bound. The analytic pin and density arguments are supplied in Section 12, not delegated to the program.

The exploratory floating-point scripts in the new archive were not executed and none of their output was used. No Monte Carlo, quadrature grid, numerical optimizer, or finite covariance search is evidence for the theorem here. The proof is analytic; the replay evidence checks only the explicitly stated finite assertions.

## Appendix A. Logarithmic integral inequality at the required class

For completeness, let \(0<s<1\), and let \(f,g,h\) be bounded, compactly supported, nonnegative log-concave functions, satisfying
\[
h((1-s)x+sy)\ge f(x)^{1-s}g(y)^s.
\tag{A.1}
\]
This class contains the Gaussian densities restricted to the bounded convex caps used above and is preserved by taking coordinate marginals. We prove
\[
\int h\ge(\int f)^{1-s}(\int g)^s.
\tag{A.2}
\]

The historical root03 appendix sketches an extension to arbitrary measurable functions by approximation. No such unexpanded approximation step is imported here; the following direct proof treats the class actually needed.

### A.1 One dimension

If either of the two masses is zero, the conclusion is immediate. Otherwise replace \(f,g\) by their normalized densities and replace \(h\) by \(h/[(\int f)^{1-s}(\int g)^s]\); the hypothesis persists. A finite positive log-concave function is continuous on the interior of its interval of positivity, because its logarithm is a finite concave function there. Endpoints have measure zero.

Let \(F,G\) be the normalized CDFs on those intervals and define the increasing inverse-CDF transport \(T=G^{-1}\circ F\). In their interiors, \(T\) is continuously differentiable and
\[
T'(x)=f(x)/g(T(x))>0.
\]
The map \(z(x)=(1-s)x+sT(x)\) is strictly increasing. Change variables on its image and use (A.1):
\[
\begin{aligned}
\int h
&\ge\int f(x)^{1-s}g(T(x))^s[(1-s)+sT'(x)]\,dx\\
&\ge\int f(x)^{1-s}g(T(x))^s T'(x)^s\,dx\\
&=\int f(x)\,dx=1.
\end{aligned}
\]
The second line is weighted arithmetic--geometric mean, which follows from concavity of the logarithm. Integration over increasing compact subintervals justifies all endpoint limits by nonnegativity. This proves the normalized assertion, hence the general one-dimensional case.

### A.2 Dimension induction, without a circular marginal theorem

Assume the logarithmic integral inequality has been proved in dimension \(q-1\). First integrate in one coordinate. For each pair of the remaining-coordinate values, the one-dimensional assertion applied to the corresponding positive fibers gives the same interpolation hypothesis for their fiber integrals. Zero fibers give a zero right-hand side and cause no issue.

Those marginal functions are themselves log-concave: apply the already proved one-dimensional assertion to two fibers of the **same** log-concave function and its intermediate fiber. This argument does not invoke the unproved \(q\)-dimensional statement. The resulting marginals are measurable, finite, and log-concave, so the \((q-1)\)-dimensional inductive hypothesis applies to them. Fubini's theorem then gives (A.2) in dimension \(q\).

Finally apply (A.2) to
\[
f(y)=\phi_q(y)\mathbf1_{P(b)}(y),\quad
 g(y)=\phi_q(y)\mathbf1_{P(c)}(y),\quad
 h(y)=\phi_q(y)\mathbf1_{P((1-s)b+sc)}(y).
\]
All three are log-concave, their supports are convex, and the elementary support inclusion and Gaussian log-concavity verify (A.1). This proves exactly (5.6), completing the foundational input without Ehrhard's inequality.

## Final conclusion

The all-dimensional claim is proved by the reconstructed argument, including singular and unbalanced covariances and positive-threshold uniqueness. The formerly missing mass conversion is now paid by an actual same-facet, componentwise-positive pressure/energy split and the finite-measure lemma. The earlier four-site defect remains recorded, but no longer lies on this proof's dependency tree. The old and new proofs share essential covariance/support interfaces, all of which have been checked explicitly here; their downstream conversion arguments are genuinely different.
