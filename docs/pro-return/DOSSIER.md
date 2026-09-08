# FSC: formalization architecture and implementation handoff

Date: 2026-09-08. **Status: source-inspected mathematical architecture, with uncompiled Lean probes. No FSC theorem has been certified in this consultation.**

## Recommendation

Use a new local repository, namespace `FSC`, with the supplied exact WSC and mathlib pins. Formalize the finite-direction / support / componentwise-scalar / strict-barrier architecture, not the geometric stress-and-envelope development. Keep the latter as a mathematical explanation and cross-check.

For the first implementation experiment, replace the regularized Plackett block with the support/noise variation theorem proved in [SUPPORT_NOISE_VARIATION.md](SUPPORT_NOISE_VARIATION.md). It derives the exact required singular, rank-increasing feasible derivative from the same support calculus already needed by the proof. This removes actual dependencies, rather than hiding them: full-matrix Gaussian density differentiation, determinant/inverse differentiation, covariance continuity of pair weights, antipodal density asymptotics, and the integrated regularization derivative passage. It adds a local second-order **threshold** expansion and a bounded-function Gaussian expectation lemma. Both are proved in that note. They are new formal work, not library declarations.

Retain the manuscript's relative differential as a documented fallback. Do not run two complete derivative projects merely because the fallback exists. The support/noise route should be judged first by a singular, deterministic-residual, rank-increasing integration probe, then by the universal feasible-path theorem.

A separate simplification is unconditional: put the barrier on `[0,T]`, not `[a,T]` with an auxiliary small a. The endpoint t=0 is harmless and excludes itself. This removes the small-threshold cutoff and endpoint-limit argument from the global assembly.

The files in this handoff are a consultation product, not a launched implementation or a release. The operator retains the launch and release decisions.

## 1. Exact certification contract

For n≥2 let

\[
\mathcal E_n=\{G\in\mathbb R^{n\times n}:G\succeq0,\ G_{ii}=1\},\quad
\Delta_n=(nI-J)/(n-1).
\]

Use mathlib's `multivariateGaussian (0 : WeakSimplex.Coord n) G` and the existing `WeakSimplex.lowerOrthant t`. The real CDF is the `ENNReal.toReal` of this event probability. Prove its probability bounds and the real/measure conversion once. The release theorems are

\[
\forall n\ge2\ \forall G\in\mathcal E_n\ \forall t\in\mathbb R,
\qquad F_{\Delta_n}(t)\le F_G(t),
\]

and, separately,

\[
\forall n\ge2\ \forall G\in\mathcal E_n\ \forall t>0,
\qquad F_G(t)=F_{\Delta_n}(t)\iff G=\Delta_n.
\]

Also expose the strict inequality for G≠Δ_n at t>0 and an event/complement maximum-tail corollary. Do not put positive threshold, distinctness, full rank, balance, or a WSC covariance condition into the comparison theorem. Intermediate analytic lemmas may and should have their true narrower domains.

The final raw statement must use `WeakSimplex.IsCorrelation`, not `IsWeakSimplexCov`. The latter includes an additional PSD condition and proves a different comparison. A Gaussian-sum representation used to compute a derivative is not deconvolution and does not invoke the old WSC result.

[INTERFACES.md](INTERFACES.md) gives Lean-shaped public statements and the principal contracts. They have not been elaborated.

## 2. Reconstructed preferred proof

The source is `mathematical/TEACHING_MANUSCRIPT.md`, Chapters 1–9, especially Chapters 3–8 for the shared analytic interface. `CORE_PROOF.md` is the compact assembly; `COMPONENTWISE_COMPARISON.md` §1 is the only scalar section needed.

### Pair weights and the finite feasible tests

For a distinct-coordinate correlation matrix, t>0 and -1<G_{ij}<1, define q_{ij} using the explicit pair regression law and the bivariate density. Set q=0 on the diagonal and at antipodal pairs. No nonantipodal positivity assumption is made: a pair's remaining event may be impossible, or may have lower-dimensional feasible geometry, and q can be zero.

Define

\[
S_{ij}=q_{ij}\ (i\ne j),\qquad S_{ii}=-\sum_{j\ne i}G_{ij}q_{ij},
\]
\[
k_i=\sum_{j\ne i}(1-G_{ij})q_{ij},\quad
C_i=\sum_{j\ne i}\sqrt{1-G_{ij}^2}\,q_{ij},\quad
\kappa=\sum_i k_i,\quad a_i=k_i/\kappa.
\]

Then S1=k and tr(SG)=0 by finite algebra. Every k_i and C_i is strictly positive. To see this without a polyhedral facet-existence theorem, choose j maximizing G_{ij} among j≠i. For n≥3 and distinct normals this maximum exceeds -1. Every remaining conditional mean at the pair pin is

\[
t\frac{G_{i\ell}+G_{j\ell}}{1+G_{ij}}<t,
\]

since G_{iℓ}≤G_{ij} and G_{jℓ}<1. The residual success set contains a neighborhood of zero in its support, including when that support has dimension zero. Thus this row-maximal pair has q_{ij}>0. This fact is also the eventual equality bridge from positive-weight pairs to every pair.

At a global fixed-threshold shape minimum, the derivative of normalized PSD addition is nonnegative. Apply it to L=z_i z_iᵀ with z_i=e_i-a_i1, where a_i is frozen at the base matrix. The derivative is half of

\[
z_i^TSz_i=S_{ii}-k_i^2/\kappa,
\]

so S_{ii}≥k_i²/κ. Full positivity of S and GS=0 are not needed.

Weighted scalar Cauchy now gives

\[
C_i^2\le k_i(k_i-2S_{ii})\le k_i^2(1-2a_i).
\]

Put d=n-2, A_i=C_i/k_i, A_*=√((n-2)/n). The signed row inequality is

\[
d(1-A_i/A_*)\ge na_i-1.
\tag{R}
\]

A convenient formal proof, preserving equality without a square-root concavity API, is the exact identity

\[
d(1-A/A_*)-(na-1)
=\frac n2(1-2a-A^2)+\frac d2(1-A/A_*)^2.
\tag{Rloss}
\]

Here A_*²=d/n, n>2 and A_*>0. Both terms on the right are nonnegative. This also makes the rigidity conditions transparent.

### Actual support caps, reciprocal comparison and energy

After excluding positive-definite minima, realize G by n unit vectors in R^(n-1). Lower-rank configurations are padded by unused Gaussian directions. Pinning i leaves a tangent space of dimension d=n-2. For each retained nonantipodal j,

\[
\sigma_{ij}=\sqrt{1-G_{ij}^2},\quad
w_{ij}=(v_j-G_{ij}v_i)/\sigma_{ij},\quad
b_{ij}=t(1-G_{ij})/\sigma_{ij}>0.
\]

Let h_i(b) be the Gaussian mass of these inequalities, and H_i=h_i(b_i). The actual-support derivative exists even with parallel redundant inequalities. The three essential equalities are

\[
\partial_{b_j}h_i(b_i)=\frac{\sigma_{ij}q_{ij}}{\phi(t)},\quad
\sum_j\partial_{b_j}h_i(b_i)=\frac{C_i}{\phi(t)},\quad
\sum_j b_{ij}\partial_{b_j}h_i(b_i)=\frac{tk_i}{\phi(t)}.
\tag{P}
\]

They follow from the same pair regression law, not from separately normalized geometric measures. Together with physical support differentiation,

\[
F_G'(t)=\phi(t)\sum_i H_i.
\tag{F}
\]

Prékopa is already available in WSC. Apply its marginalization theorem to the Gaussian density times the indicator of the joint convex set `{(b,y) | ⟨w_j,y⟩≤b_j ∀j}`. It gives log-concavity of h. On positive support vectors h>0; the geometric-mean bound and weighted arithmetic-geometric mean inequality give convexity of 1/h.

Only a one-dimensional support segment is needed. If c=ρ1 and p=h(c), the right tangent inequality at the actual b is

\[
H^2/p-H\ge Dh(b)[b-c].
\]

No derivative at c is required. This matters when equal reference supports produce ties between projected parallel normals.

Take ρ=t/A_* and p₀=D_{n-1}(ρ). At most n-1 retained unit directions occur, and at least one occurs. Extend their list to exactly n-1 by **repeating an existing direction**, not adding independent coordinates. The induction hypothesis gives h_i(ρ1)≥p₀. Consequently

\[
H_i^2/p_0-H_i
\ge (tk_i-\rho C_i)/\phi(t)
=d u_i(1-A_i/A_*)\ge u_i(na_i-1),
\tag{Qsupport}
\]

where u_i=tk_i/(dφ(t)).

The cap Q_i can be unbounded. For s>0,

\[
h_i(sb_i)=s^d\int_{Q_i}\phi_d(sy)\,dy,
\]

and differentiation at s=1 gives

\[
\frac{tk_i}{\phi(t)}=dH_i-\int_{Q_i}\|y\|^2\,d\gamma_d(y).
\]

The derivative under the integral is dominated near one by a constant times
`(1+‖y‖²) exp(-‖y‖²/8)`, over the whole space. Its integrability does not depend on boundedness of Q_i. Define

\[
e_i=\frac1d\int_{Q_i}\|y\|^2\,d\gamma_d(y)>0,
\qquad H_i=u_i+e_i.
\tag{E}
\]

The strict inequality follows because d≥1 and Q_i contains a ball around zero; a smaller annular open subset has positive Gaussian mass and squared norm bounded below by a positive number. Also u_i>0 from k_i>0.

**Exact padding.** If the intrinsic tangent dimension is d₀ and Q_i=Q_i⁰×R^(d-d₀), then

\[
H_i=\gamma_{d_0}(Q_i^0),\qquad
\int_{Q_i}\|y\|^2d\gamma_d
=\int_{Q_i^0}\|y\|^2d\gamma_{d_0}+(d-d_0)H_i.
\]

The main proof need not carry d₀: doing the dilation in the already padded tangent space includes this contribution automatically. Keep the explicit padding identity as an acceptance test, not an omitted correction.

### Componentwise conversion and equality

The elementary scalar theorem is as follows. Let a finite nonempty index set carry strictly positive u_i,e_i,ω_i, let ∑ω_i=1 and M>0, and set U=∑u_i, E=∑e_i, X=U+E. If

\[
\frac{(u_i+e_i)^2}{M}-\frac{u_i^2}{U}\ge\omega_i e_i\quad\text{for every }i,
\tag{C}
\]

then X≥M. If X=M, then u_i/U=e_i/E=ω_i and u_i+e_i=Mω_i.

For completeness the proof uses

\[
\frac{u_i^2}{U}+\frac{e_i^2}{E}-\frac{(u_i+e_i)^2}{X}
=\frac{(Eu_i-Ue_i)^2}{XUE}\ge0.
\]

Choose an index with e_i/E≤ω_i; one exists because both vectors sum to one. Combining this identity with (C) at that index gives `(u_i+e_i)²/M ≥ (u_i+e_i)²/X`, hence X≥M. If X=M, the two inequalities at every index imply e_i/E≥ω_i. Equality of sums makes every ratio equal. Every Cauchy remainder must then vanish, giving u_i/U=e_i/E, and the stated conclusions follow. This proof is independent of Gaussian analysis.

Apply it with x_i=H_i, ω_i=1/n and M=np₀. Equations (Qsupport) and (E) give (C), because a_i=u_i/U. Thus ∑H_i≥np₀, hence F'_G(t)≥nφ(t)p₀.

The reference recursion is

\[
D'_n(t)=n\phi(t)D_{n-1}\left(t\sqrt{n/(n-2)}\right).
\]

It follows by a single pin in Δ_n: after subtracting conditional means and dividing by the conditional standard deviation, the remaining covariance is Δ_{n-1}. This includes the antipodal two-coordinate residual when n=3.

If the boundary slopes are equal, the scalar equality yields H_i=p₀ and a_i=1/n. The sandwich in (Qsupport) forces A_i=A_*. Equality in row Cauchy then forces

\[
G_{ij}=-1/(n-1)\quad\text{whenever }q_{ij}>0.
\]

One convenient formal equality proof expands `∑_j (y_j-(C_i/k_i)x_j)²`, with `x_j=√((1-Gij)qij)` and `y_j=√((1+Gij)qij)`. Its zero total implies the equality for each positive-weight pair. The row-maximal pair is positive, so every off-diagonal entry is at most -1/(n-1). Finally PSD gives

\[
0\le1^TG1=n+2\sum_{i<j}G_{ij}\le0.
\]

A finite sum of nonnegative deficits is zero; every entry equals the simplex entry. No equality theorem for Prékopa is used.

### Exclusions, the barrier and the base cases

A positive-threshold shape minimum has no duplicates. If coordinates i,j coincide almost surely, remove the redundant i and replace it by an independent standard normal. The resulting correlation matrix has CDF Φ(t)F_G(t)<F_G(t), since F_G(t)>0 and Φ(t)<1. This is a finite feasible replacement, not an infinitesimal splitting argument.

A positive-definite shape minimum is excluded by the normalized-addition derivative with L=G-δJ PSD, as proved in the separate support/noise note. Thus the rank-padded tangent construction applies.

Suppose δ=D_n(t₀)-F_{G₀}(t₀)>0. Necessarily t₀>0. Put ε=δ/(2t₀)>0 and

\[
\Psi(G,t)=F_G(t)-D_n(t)+\varepsilon t.
\]

Choose T>max(t₀,1/ε). The elliptope times [0,T] is compact and Ψ continuous. At t₀ its value is -δ/2. At zero it is F_G(0)≥0 because D_n(0)=0. At T it is at least -1+εT>0. A negative minimum therefore occurs at 0<t*<T. The minimizing G* is a fixed-threshold shape minimum. The boundary theorem gives F'_{G*}(t*)≥D'_n(t*), whereas ordinary interior threshold stationarity gives

\[
F'_{G*}(t*)-D'_n(t*)=-\varepsilon.
\]

Contradiction. The proof needs neither an envelope nor continuity of its minimizers, nor a tail limit, nor equality rigidity to establish comparison.

For positive-threshold equality after comparison is known, G is a global shape minimum and the fixed-shape nonnegative difference F_G-D_n touches zero. Its derivative vanishes. The boundary equality theorem then gives G=Δ_n.

For t<0, D_n(t)=0 because the simplex coordinates sum to zero. At t=0, all simplex coordinates being nonpositive forces every coordinate to vanish, an event of probability zero because an individual coordinate is N(0,1). These cases require no singular differentiation.

For n=2, at t>0 inclusion-exclusion gives

\[
F_G(t)=2\Phi(t)-1+\Pr(X_1>t,X_2>t).
\]

The antipodal simplex has the first term as its CDF. If the correlation c>-1, the simultaneous strict exceedance event has positive probability: in a Gram realization, a sufficiently large positive multiple of v₁+v₂ satisfies both strict inequalities since ⟨v_i,v₁+v₂⟩=1+c>0; a neighborhood does too. Standard Gaussian mass of that neighborhood is positive. Thus equality occurs exactly at c=-1. The general nonpositive argument completes the base.

## 3. Representation decisions

**Law layer.** Use the existing total Gaussian definition and explicit PSD hypotheses. Outside PSD it has a Dirac fallback; it is not a smooth ambient extension of the intended Gaussian family. Prove all-PSD affine-image and independent-sum adapters using `IsGaussian.ext`, means and covariances. The required public primitives already exist. Do not unfold the CFC square root throughout the analytic proof.

**Pin layer.** Keep residual laws on the original `Fin n` coordinates and exclude pinned indices in the event. This avoids a `Fin (n-2)` reindexing at every regression calculation. Use explicit α,β and the congruence covariance PGPᵀ. No Schur inverse instance is needed. In applications of the independence API, show that the combined residual/pin vector is jointly Gaussian; two individually Gaussian marginals are not enough.

**Support layer.** Use finite retained-index subtypes and `Coord d` for tangent caps. Prove a generic cap API; translate to Pi coordinates for the existing Prékopa and product-density facts. All comparisons use real CDFs, while measure-valued wrappers preserve the exact probability statement. Do not formalize Hausdorff surface integrals, coarea, moving-face formulas or divergence theorems for this first proof.

**Differentiation.** Expose only `HasDerivWithinAt` on s≥0 for normalized PSD addition, plus ordinary support/threshold derivatives on their genuine open neighborhoods. Nonnegative right derivatives at a boundary minimum are not zero derivatives. The full relative covariance differential can remain an optional theorem.

**Rank.** First prove any PSD correlation is a Gram matrix in dimension n. For a non-PD matrix choose a nonzero kernel vector of the square root. Its image lies in a hyperplane of dimension n-1; an orthonormal identification gives a realization in `Coord (n-1)`, already padded. Pinning a unit vector then gives `Coord (n-2)`. This avoids parameterizing the entire proof by the changing intrinsic rank. The rank-reduction existence wrapper is new formal work; the forward score-law theorem is already public in WSC.

**Compactness and continuity.** Prove elliptope compactness directly: closedness of symmetry and every quadratic inequality, and |Gij|≤1 from e_i±e_j. For joint CDF continuity use the pinned characteristic-function formula, the sequential Lévy theorem, and Portmanteau on a null-frontier event. Varying thresholds can be absorbed in the mean -t1 and a fixed zero orthant. Every marginal at the limit has variance one, so the frontier is null. This avoids needing a matrix-norm continuity theorem for CFC square roots. First-countability turns the sequential result into continuity on the finite-dimensional domain.

## 4. Alternatives and the genuinely shared boundary

The geometric/log/envelope proof adds full PSD stress, trace-orthogonality rigidity GS=0, positive dependence, bounded intrinsic caps, a logarithmic/entropy conversion, and a minimum-envelope argument. Some resulting geometric explanations are valuable, but these mechanisms do not eliminate the singular pin/support compatibility problem. The envelope route additionally needs uniform threshold control and continuity/compactness sufficient to pass through varying minimizing covariances. The finite barrier avoids those dependencies.

The choices need not be bundled. A **finite-direction / log-support tangent / quadratic scalar / barrier** hybrid is valid: from

`H log(H/p₀) ≥ D h(b)[b-ρ1]`

and `log z≤z-1`, obtain exactly (Qsupport). This does not require entropy or a PSD stress theorem. Freeze (Qsupport) as the consumer-facing interface, not a particular reciprocal-convexity API. Prefer the reciprocal argument initially; choose the logarithmic tangent internally only if a compiled probe demonstrates a genuinely simpler wrapper on the pinned library. The mathematical interface and equality proof are identical. No further research conversation is required to decide this small API choice.

## 5. What is already formal, and what remains

[SOURCE_MAP.md](SOURCE_MAP.md) gives exact paths, line ranges, namespaces and scope corrections. The key distinction is:

*Existing public foundations:* arbitrary-PSD Gaussian laws/covariances/marginals, Gram score laws, normal calculus, Prékopa marginalization and the inspected regularization family.

*Adapters, not new foundational theories:* residual/pin products; arbitrary PSD independent Gaussian sums; correlation-only null frontiers; real/ENNReal conversions; joint CDF continuity; inverse Gram/rank-padded realization; support-mass log-concavity.

*New FSC formal mathematics:* no-coincidence support C¹ calculus, repeated support differentiation/Peano expansion, bounded-function noise averaging, feasible normalized covariance derivatives, unbounded dilation and positive energy, the finite-test row/equality argument, the componentwise conversion, reference recursion/padding and the global barrier assembly.

Completing the scalar file is useful but does not discharge any of those analytic interfaces. A theorem with an unproved analytic certificate as an explicit parameter is a conditional assembly, not FSC.

## 6. Ownership and acceptance

Use one integration owner for definitions, public statements, manifests, production imports and the final trust dossier. Once the pin/support/weight normalization is frozen, independent owners can work on generic cap convexity, dilation, scalar algebra, rank/compactness, and the global barrier. Keep file ownership disjoint. Regression and the support/noise derivative must share the same definitions and be integrated together; do not let separate workers each create their own q.

Each accepted interface needs its exact printed type, dependencies, a source locator, a fresh compile log and a transitive axiom report. Preserve counterexamples that prevent stronger false statements. Independently review the equality path while constructing each component, not after the comparison has been declared complete.

[PROBES.md](PROBES.md) specifies the informative compiler experiments and their evidence requirements. [ENVIRONMENT_AND_ACCEPTANCE.md](ENVIRONMENT_AND_ACCEPTANCE.md) gives pins, repository procedure, audit gates and statement review. The supplied Python audit utility passed its own synthetic tests; it has **not** run a Lean audit. The `.lean` files are uncompiled probe attempts with no placeholder theorem bodies.

The first implementation owner should start with the singular support/noise integration contract alongside the scalar probe, not spend an initial phase collecting only easy lemmas. A further architectural consultation is warranted only for an exact blocked universal statement, a counterexample to an asserted intermediate lemma, a demonstrated failure of the chosen representation, or a material change of dependencies. A failed guessed theorem name is not such an obstruction.
