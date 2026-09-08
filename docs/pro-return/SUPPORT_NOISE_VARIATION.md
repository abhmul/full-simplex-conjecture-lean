# Deriving feasible covariance variations from support calculus

**Status.** Mathematical derivation in this consultation, not a theorem already in the supplied manuscript or Lean library. No Lean compilation has been performed. This note supplies the complete argument for a proposed replacement of the manuscript's regularized Plackett block. It does not change the statement of FSC, and it does not claim an ambient covariance derivative at a singular matrix.

## 1. What is replaced, and what is retained

The finite-direction proof only needs derivatives of

\[
G_s=D_s(G+sL)D_s,\qquad (D_s)_{ii}=(1+sL_{ii})^{-1/2},\quad s\ge0,
\]

for positive-semidefinite L, including rank-one L. It does not need the entire relative Fréchet differential on the elliptope. The required derivative can instead be obtained from a second-order expansion **in the threshold vector at one fixed covariance**.

Retain canonical one- and two-coordinate regression and the actual-support C¹ theorem from the manuscript, Chapter 5. Replace the positive-definite density derivative, covariance continuity of pair weights, antipodal exponential limiting estimate, and integrated regularization passage by the elementary expectation lemma below. General all-PSD CDF continuity is still needed for compactness; it is a different, already well-supported task.

This is not a claim that the covariance Hessian exists. The threshold Hessian is locally well behaved precisely where the proof uses it: distinct coordinates and a positive common threshold.

## 2. Explicit regression and threshold derivatives

Let G be a correlation matrix and let X have its centered Gaussian law. For a fixed i put c_j=G_{ij} and let

\[
R^{(i)}_j=X_j-c_jX_i.
\]

The residual vector is jointly Gaussian with X_i and has zero cross-covariance with X_i, hence they are independent. Its covariance is G-c cᵀ, interpreted on all original indices; its i-coordinate is identically zero. This is a linear-image construction, so its covariance is PSD even when singular.

For a nonantipodal pair i≠j, write c=G_{ij}, σ=√(1-c²)>0. Define column vectors

\[
\alpha_k=\frac{G_{ki}-cG_{kj}}{1-c^2},\qquad
\beta_k=\frac{G_{kj}-cG_{ki}}{1-c^2},
\]

and P=I-αe_iᵀ-βe_jᵀ. Then R=PX is independent of (X_i,X_j), because PG e_i=PG e_j=0 and the joint vector is Gaussian. The residual covariance Γ=PGPᵀ is PSD by congruence. The canonical pair law at arbitrary real pins (r,s) is

\[
N(\alpha r+\beta s,\Gamma).
\]

Prove the product-law factorization and its Fubini formula; an arbitrary version of a conditional distribution at a null event is neither necessary nor sufficient.

**Event convention.** Evaluate the success event only on indices k≠i,j. Pinned coordinates equal their thresholds deterministically. Including those coordinates when claiming a null frontier is incorrect, although it does not change the numerical probability at the exact pin.

For t>0 set

\[
b_{ij}=t(1-c)/\sigma,\quad
q_{ij}=\frac{\phi(t)\phi(b_{ij})}{\sigma}
 \Pr_{N(\alpha t+\beta t,\Gamma)}(x_k\le t\text{ for }k\ne i,j).
\]

Set q_{ii}=0, and q_{ij}=0 for c=-1. The displayed expression equals the source's bivariate-density definition. Its symmetry follows either from the pair law or the symmetric explicit residual formula.

### Local support C¹ theorem

For fixed unit vectors w_j in a finite-dimensional Euclidean space, define

\[
h(b)=\Pr(\langle w_j,Y\rangle\le b_j\ \forall j).
\]

If no two listed boundary hyperplanes coincide at b⁰, h is C¹ in a neighborhood of b⁰. The precise condition is: for distinct j,k, equal normals require b⁰_j≠b⁰_k, and opposite normals require b⁰_j≠-b⁰_k. Redundancies and unbounded caps are allowed.

One proof uses only slicing and continuous partial derivatives. Condition on ⟨w_j,Y⟩=z by its explicit residual law. Every remaining conditional coordinate is either nondegenerate, or parallel to w_j and deterministic. In the latter case the noncoincidence condition gives strict separation from its threshold at the point in question. Thus, under a fixed Gaussian residual realization, the other-constraint indicator converges almost surely as z and the other supports vary nearby. Dominated convergence gives continuity of the slice probability. The one-dimensional fundamental theorem of calculus gives

\[
\partial_j h(b)=\phi(b_j)\Pr(\text{remaining constraints}\mid\langle w_j,Y\rangle=b_j).
\]

These partial derivatives are continuous on a common neighborhood. To avoid assuming a ready-made multivariable theorem, telescope the increment h(b+v)-h(b) by changing one coordinate at a time. The one-dimensional mean-value theorem and continuity of the finitely many partial derivatives give a remainder bounded by ε∑|v_j|. This proves the Fréchet derivative and its continuity. The multi-strip O(‖v‖²) proof in the manuscript is an alternative, not an extra dependency.

### Why it applies twice

Assume G has distinct coordinates, i.e. G_{ij}<1 for i≠j. Realize its unit normals in any finite-dimensional Gram space; full rank is not needed. At the common positive support t, original boundary hyperplanes are distinct. After pinning i, omit antipodes and set

\[
w_{ij}=(v_j-cv_i)/\sigma,\qquad b_{ij}=t(1-c)/\sigma>0.
\]

The projected boundary hyperplanes are also distinct. Indeed equality of positive supports gives equality of (1-c)/(1+c) after squaring, hence equality of c by cross multiplication. Equality of projected normals then gives equality of original normals, contrary to distinctness. Opposite projected normals cannot have coincident hyperplanes because their supports are both positive. These finitely many strict separations persist in a neighborhood.

Define f_G(b)=Pr(X_k≤b_k for every k). Near b=t1, the single-pin formula is

\[
\partial_i f_G(b)=\phi(b_i)\,h_i\left(\left(\frac{b_j-G_{ij}b_i}{\sqrt{1-G_{ij}^2}}\right)_{j\in K_i}\right),
\]

where K_i consists of nonantipodal indices different from i. An antipodal constraint becomes -b_i≤b_j and remains strictly automatic locally. Applying the support C¹ theorem to h_i shows that the displayed gradient is C¹. Thus f_G is locally C². At b=t1,

\[
\partial_i f_G=\phi(t)H_i,
\qquad
\partial_{ij} f_G=q_{ij}\quad(i\ne j),
\]
\[
\partial_{ii} f_G=-t\phi(t)H_i-\sum_{j\ne i}G_{ij}q_{ij}.
\tag{T}
\]

For i≠j the factor 1/σ from the affine support change combines with the slice derivative to give exactly q. For the diagonal, φ'(t)=-tφ(t), and each affine support has derivative -G_{ij}/σ. These prove every term of (T), including zero contributions from antipodes.

Do not extend this assertion indiscriminately to duplicates or zero threshold. For duplicated scores f(b₁,b₂)=Φ(min(b₁,b₂)), which is not differentiable on the diagonal. For an antipodal pair at threshold zero the analogous corner also invalidates the proposed neighborhood smoothness. Neither case is needed here.

## 3. A bounded-function expectation lemma

Let V be finite-dimensional, f:V→ℝ be bounded and Borel measurable, and suppose at x

\[
f(x+h)=f(x)+\ell(h)+\tfrac12 B(h,h)+R(h),\qquad R(h)=o(\|h\|^2),
\]

where ℓ is continuous linear and B is continuous bilinear. Let ν be a probability measure on V, ∫y dν=0 and ∫‖y‖²dν<∞. Suppose v(0)=0 and v(s)/s→v₀ as s↓0. Then

\[
\int f(x+v(s)+\sqrt{s}\,y)\,d\nu(y)
=f(x)+s\left[\ell(v_0)+\frac12\int B(y,y)\,d\nu(y)\right]+o(s).
\tag{N}
\]

**Proof of the only nontrivial interchange.** The local Peano estimate and boundedness of f imply a global bound |R(h)|≤C‖h‖². Outside a fixed ball of radius r>0, bound the constant and linear terms by constants times ‖h‖²/r² and ‖h‖²/r. Inside that ball use the Peano estimate.

For h_s(y)=v(s)+√s y, v(s)=O(s) gives

\[
\|h_s(y)\|^2/s\le C'(1+\|y\|^2)\quad(0<s\le s_0).
\]

Pointwise, R(h_s(y))/s→0: h_s(y)→0, its squared norm divided by s stays bounded, and the Peano ratio tends to zero (with R(0)=0). The global quadratic bound gives an integrable dominating function. Dominated convergence therefore makes the integrated remainder o(s). The expectation of ℓ(√s y) is zero. Expanding the bilinear term, the cross terms vanish because ∫y=0, its drift-only term is O(s²), and its noise-only term is s∫B(y,y). Finally ℓ(v(s))/s→ℓ(v₀). This proves (N). Only second moments are required; no fourth-moment estimate or Gaussian tail asymptotics are hidden here.

For an implementation, state (N) first with the explicit Peano expansion. Obtain that expansion from the local C¹ derivative proved above. An elementary proof differentiates the Taylor remainder along a segment: differentiability of f' at x bounds its derivative by ε‖h‖² on that segment, and the scalar mean-value inequality bounds the remainder. This avoids assuming that the inspected univariate `Taylor.lean` supplies a multivariate theorem. That file explicitly works with f:ℝ→E; it is not a drop-in vector-domain API.

## 4. The required singular feasible derivative

Take X~N(0,G) and Y~N(0,L) independently, with L PSD. For s≥0, set

\[
X_{s,i}=\frac{X_i+\sqrt{s}Y_i}{\sqrt{1+sL_{ii}}}.
\]

Its covariance is G_s and its diagonal is one. Conditioning on Y gives

\[
F_{G_s}(t)=\mathbb E f_G\bigl(t1+v(s)-\sqrt{s}Y\bigr),
\qquad v_i(s)=t(\sqrt{1+sL_{ii}}-1).
\]

This is an equality of measures followed by Fubini, not noise cancellation. Since v_i'(0+)=tL_{ii}/2, applying (N) and (T) gives

\[
\begin{aligned}
\left.\frac d{ds}\right|_{0+}F_{G_s}(t)
&=\frac12\left[\sum_i tL_{ii}\phi(t)H_i+
                 \sum_{i,j}L_{ij}\partial_{ij}f_G(t1)\right]\\
&=\sum_{i<j}q_{ij}\left(L_{ij}-\frac{G_{ij}}2(L_{ii}+L_{jj})\right)
 =\tfrac12\operatorname{tr}(SL),
\end{aligned}
\tag{V}
\]

where S_{ij}=q_{ij} for i≠j and S_{ii}=-∑_{j≠i}G_{ij}q_{ij}. The drift cancels exactly the -tφ(t)H_i diagonal contribution. This calculation proves the normalization and the factor 1/2.

The derivative is within s≥0, at s=0. It applies to singular G, singular L, rank-increasing paths, antipodal pairs, and pairs whose nonantipodal success probability is zero. It does not require continuity of q as G varies. Its strictness assumptions are exactly t>0 and distinctness of the base G.

## 5. Positive-definite exclusion without a second covariance calculus

The manuscript's positive-definite descent can also use (V). For a positive-definite correlation G choose λ>0 with xᵀGx≥λ‖x‖². Existence follows by minimizing the continuous positive quadratic form on the unit sphere. For n≥1 choose δ=λ/(2n)>0. Cauchy gives (1ᵀx)²≤n‖x‖², hence

\[
L=G-\delta J\succeq (\lambda/2)I\succeq0.
\]

The algebraic identity tr(SG)=0 follows directly from the definition of S, while 1ᵀS1=κ=∑_{i,j≠i}(1-G_{ij})q_{ij}>0. Therefore

\[
\tfrac12\operatorname{tr}(S(G-\delta J))=-\delta\kappa/2<0.
\]

This contradicts minimality along a feasible nonnegative s-path. Thus the same derivative theorem excludes positive-definite minima. No full PSD stress certificate is being introduced.

For the remaining finite tests put a_i=k_i/κ, z_i=e_i-a_i1 and L=z_i z_iᵀ. Freeze a_i at the base matrix. Nonnegative right derivatives give S_{ii}-k_i²/κ≥0. These are precisely the finite-direction inequalities used by the supplied core proof.

## 6. Scope and the first decisive compiler evidence

The mathematical reduction above is complete; its Lean realization remains new work. The first decisive integration probe should prove (V) for the singular rank-two triangle from `PROBES.md`, using the generic expectation lemma and a proved local support expansion—not an assumed derivative oracle. The subsequent universal theorem must retain all PSD G and L under the stated distinctness/positive-threshold hypotheses.

A source-inspected fallback exists: manuscript §§4.1–4.5 and the fresh audit §4 give the regularized relative differential. Do not develop both derivative engines in parallel before the support/noise probe identifies a real blocker. A compiler difficulty with an univariate-versus-vector Taylor API is not by itself a mathematical obstruction: the segment proof above supplies the missing adapter explicitly.
