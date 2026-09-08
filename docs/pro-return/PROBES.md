# Compiler experiments that decide the implementation

**None of the Lean probes was compiled here.** `probe_project/` contains complete small proof attempts and exact-name import probes for the separate implementation owner. The more important analytic probes below are acceptance specifications, not falsely completed source files. No analytic premise should be disguised as a typeclass instance, axiom, or imported scaffold.

## Start with both a source/API probe and a singular analytic probe

After the pinned dependencies resolve, compile `FSCProbes/Imports.lean`. Record the printed signatures. In particular check the actual namespaces of the Schur, Haar-scaling and parametric-integral declarations; the supplied inventory has errors there. This is an elaboration test only, not a proof of an FSC adapter.

Compile `FSCProbes/Algebra.lean` and its separate `Audit.lean`. It contains the exact rational Cauchy remainder, signed-row remainder, regression coefficient cancellation, generator diagonal cancellation and a Gram-PSD example. These are deliberately small. Even all of them passing would leave the Gaussian work unproved.

In parallel, take the following singular configuration through the **real law and derivative interfaces**:

\[
v_0=(1,0),\quad v_1=(0,1),\quad v_2=(-3/5,4/5),
\qquad
G=\begin{pmatrix}1&0&-3/5\\0&1&4/5\\-3/5&4/5&1\end{pmatrix}.
\]

Its rank is two. For t>0, every pair residual has covariance zero. Under pins (0,1), the remaining coordinate is t/5<t; under (0,2), the remaining coordinate is 2t>t; under (1,2), it is -t/3<t. Consequently

\[
q_{01}=\phi(t)^2>0,\qquad q_{02}=0,\qquad
q_{12}=\frac53\phi(t)\phi(t/3)>0.
\]

For the first single-pin cap, the remaining inequalities are y≤t and y≤2t: an **unbounded** cap with a parallel redundant constraint. The redundant support derivative is zero. Prove these probabilities and support derivatives in Lean, not merely the rational means.

Then let L=e₂e₂ᵀ and use the normalized-addition path. It has full rank for s>0. The target right derivative at zero is

\[
\left.\frac d{ds}\right|_{0+}F_{D_s(G+sL)D_s}(t)=-\frac25q_{12}.
\]

The exact rational residual and trace calculations have been checked by the supplied Python/SymPy diagnostic. That did **not** check a Gaussian probability or derivative. The Lean acceptance is the complete derivative theorem for this concrete singular example, derived from proved support expansion and expectation lemmas. This is the early evidence that matters more than a large scalar file.

## Canonical regression probe

Prove the full-index pair residual covariance is PSD by congruence, its pinned rows are zero, its cross-covariances with the two pins vanish, and its joint law factors as a product. Then prove the Fubini identity for an arbitrary measurable remaining-coordinate event. Use the above rank-two example so that the residual is a Dirac law, not a nonsingular Gaussian.

Expected discovery: `HasGaussianLaw.indepFun_of_covariance_eval` is typed for Pi-valued families; explicitly construct the joint residual/pin CLM and carry the Euclidean/Pi identification. A proof that only shows both marginals Gaussian is insufficient. A regular conditional law specified merely almost everywhere in the pin parameter is also insufficient for evaluating the fixed equal pin.

**Negative statement check:** it is false that the full n-coordinate lower-orthant frontier is null under the full-index pair law at (t,t). The pinned coordinates lie on it. The success event must exclude them.

## Generic support C¹ and threshold C² probe

Use n=5 planar normals e₁,e₂,(3/5,4/5),-e₁,-e₂ and pin e₁ at t>0. The retained scalar inequalities include y≤t, y≤t/2, and -y≤t. At actual supports there are no coincident boundaries, the weaker upper inequality has derivative zero, and an antipodal original constraint is omitted as automatic.

Prove the C¹ neighborhood contract and the single-slice derivative formula for this example, then generalize. Evaluate the reference with both upper supports equal. Its mass is well defined, but the function of these separate upper supports is not differentiable at the tie. The tangent theorem must therefore differentiate only at the actual supports.

For the original fixed G, apply the generic C¹ result once to the physical supports and once to the conditional supports. Produce the explicit first derivative and threshold Hessian from formula (T). Prove a second-order Peano expansion on the vector domain; do not apply the inspected univariate Taylor theorem as if its domain were `Coord n`.

The generic segment/mean-value proof in `SUPPORT_NOISE_VARIATION.md` supplies a fallback for this adapter. This is an ordinary finite-dimensional analysis task, not a reason to introduce a covariance smoothness axiom.

## Bounded-function noise averaging probe

First prove the generic expectation result under an explicit Peano expansion and a centered probability law with finite second moment. Exhibit the global quadratic remainder bound and the integrable domination `C*(1+‖y‖²)`. Verify that no fourth moment, smooth cutoff, global C² bound or density of the noise law has slipped into the statement.

Specialize to ν=N(0,L), including L singular, and derive the exact normalized-addition derivative using the proved affine-image/product-law identities. This must eventually quantify over every distinct-coordinate PSD correlation G, every PSD L and every t>0. A concrete triangle example alone is not that universal theorem.

A failed C²/Peano API experiment should report the exact unresolved Lean goal, the smallest reproducer and the pinned declarations tried. The fallback is the local segment proof, followed only if necessary by the manuscript's full regularized Plackett route. Do not preemptively build both engines.

## Dilation and padding probe

Take the square e₁,e₂,-e₁,-e₂, n=4 and G its rank-two Gram matrix. A facet in the required padded dimension d=2 is `[-t,t] × ℝ`. Put H=2Φ(t)-1. Prove

\[
\int_{[-t,t]\times\mathbb R}(x^2+z^2)\,d\gamma_2=2H-2t\phi(t),
\]

so u=tφ(t) and e=H-tφ(t)>0. The intrinsic interval alone contributes H-2tφ(t); the unused Gaussian direction contributes another H. Forgetting that H term is a genuine rank-padding error.

Use `truncated_second_moment` for the one-dimensional calculation and product Gaussian moments for the padding. Also prove the unbounded half-line dilation identity from the triangle example. Neither test may assume compact support. The universal dilation theorem must show the integrable majorant before applying the parametric-integral API.

## Scalar, row-rigidity and barrier probes

The standalone scalar acceptance is the full finite componentwise theorem with equality, not just its two-variable rational identity. Keep the strict positivity of every e_i and ω_i. As a negative test, u=e=(1/2,0), ω=(1/2,1/2), M=6/5 satisfies the relaxed componentwise inequalities but has total mass one. Thus allowing empty occupied components without changing the statement is false.

Prove the row inequality using the explicit nonnegative loss (Rloss), and prove its equality through the zero sum of squares. The needed row positivity is only for a row-maximal pair; do not invent universal q positivity.

Prove an abstract strict linear-barrier theorem on a compact shape space and thresholds [0,T]. Verify explicitly: the reference value at zero is zero; the upper endpoint uses only probability bounds and εT>1; the minimum is interior in threshold; shape variations are feasible right directions, while threshold stationarity is an ordinary two-sided derivative. Comparison must not consume equality rigidity. Then prove the fixed-positive-threshold equality assembly separately.

## Integration evidence and escalation

A passing probe report contains the exact statement and command, compiler/version and dependency revisions, exit status, the fresh axiom report, and the remaining hypotheses. The owner should distinguish source-known, elaborated, kernel-checked local, conditional assembly and closed public theorem.

An architecture-changing blocker is a counterexample to the claimed local support expansion, a mismatch between the explicit pair laws in two analytic operations, failure of the exact padded energy identity, or a universal feasible derivative that cannot be obtained without materially different assumptions. A namespace correction or finite-index cast is not such a blocker.

No further Pro turn is a prerequisite to starting these probes. Any later consultation should receive the minimal failed Lean example and exact mathematical statement, not merely a report that “singular Gaussian calculus is difficult.”
