# Componentwise comparison: convexity, pressure and positive remainder

Date: 2026-09-07. Coordinator sources: external required; legacy selected. These are checked mathematical derivations from the pressure-energy proof, independently reconstructed by read-only reviewers; historical novelty is not asserted. The [Gaussian proof](CORE_PROOF.md) uses only section 1. Sections 2–5 record natural generality, exact losses and failed relaxations.

The principle is elementary but its input is strong: mass is split into a pressure part and a nonnegative remainder at every component, and the comparison uses those same pressure weights. An uncontrolled favorable sum is not a substitute. The exact identities below also identify particular weighted aggregate conditions that do suffice.

## 1. Quadratic assembly is sufficient

Let $u_i,e_i,\omega_i,M>0$, $\sum_i\omega_i=1$, and define
$$
x_i=u_i+e_i,\quad U=\sum_i u_i,\quad E=\sum_i e_i,\quad X=U+E,
\quad a_i=u_i/U,\quad \nu_i=e_i/E.
$$
The useful primitive is already quadratic:
$$
\frac{x_i^2}{M}-\frac{u_i^2}{U}\ge\omega_i e_i
\quad\text{for every }i
\quad\Longrightarrow\quad X\ge M.
\tag{QH}
$$
Indeed Cauchy gives $x_i^2/X\le u_i^2/U+e_i^2/E$. Choose an index with $\nu_i\le\omega_i$ and compare the two inequalities. If $X=M$, applying them at every component gives $\nu_i\ge\omega_i$; equal sums and Cauchy equality imply $a=\nu=\omega$ and $x=M\omega$.

The original logarithmic hypothesis
$$
x_i\log\frac{x_i}{M\omega_i}
\ge u_i(a_i/\omega_i-1)
\tag{H}
$$
implies (QH) by $\log z\le z-1$. Thus entropy is not an essential qualitative dependency.

An exact certificate retains the discarded quadratic losses. Define
$$
s_i^Q=\frac{x_i^2}{M}-\frac{u_i^2}{U}-\omega_i e_i\ge0,\qquad
Q_i=\frac{u_i^2}{U}+\frac{e_i^2}{E}-\frac{x_i^2}{X}
=\frac{(Eu_i-Ue_i)^2}{XUE}\ge0.
$$
Adding these identities, dividing by $e_i$ and summing gives
$$
\left(\frac1M-\frac1X\right)\sum_i\frac{x_i^2}{e_i}
=\sum_i\frac{s_i^Q+Q_i}{e_i}.
\tag{Q}
$$
In particular, with $\alpha=U/X$, $\beta=E/X$ and
$\chi^2(a\Vert\nu)=\sum_i(a_i-\nu_i)^2/\nu_i$,
$$
\frac XM-1\ge
\frac{\alpha\beta\,\chi^2(a\Vert\nu)}
{1+\alpha^2\chi^2(a\Vert\nu)}.
\tag{1}
$$
This measures disagreement between pressure and remainder distributions, not by itself their distance to the reference $\omega$.

Equation (Q) gives a legitimate compensated version: individual $s_i^Q$ may have either sign if $\sum_i s_i^Q/e_i\ge0$. Comparison still follows, but its equality no longer identifies $\omega$. Indeed choose any positive $a\ne\omega$ and $U+E=M$, and set $u=Ua$, $e=Ea$, $x=Ma$. Then every $Q_i=0$ and $\sum_i s_i^Q/e_i=0$, while $a=\nu\ne\omega$. The stronger componentwise premise supplies the reference rigidity used by the Gaussian proof.

Occupied components also matter. If zero masses are admitted while retaining positive reference weights, even (QH) can fail: $x=(1,0)$, $u=e=(1/2,0)$, $\omega=(1/2,1/2)$ and $M=6/5$ satisfy its inequalities but $X=1<M$. Empty components cannot silently carry reference mass.

## 2. A single convex-perspective generalization

Let $\psi:(0,\infty)\to\mathbb R$ be strictly increasing, $\psi(1)=0$, with $f(z)=z\psi(z)$ convex. Now allow $e_i\ge0$, retaining $u_i,\omega_i,M>0$. Then
$$
x_i\psi\!\left(\frac{x_i}{M\omega_i}\right)
\ge u_i\psi(a_i/\omega_i)\quad\text{for every }i
\quad\Longrightarrow\quad X\ge M.
\tag{P}
$$

If some $e_i=0$, monotonicity in its inequality gives $U\ge M$, hence the result. Otherwise $E>0$ and all $\nu_i>0$. Convexity gives the componentwise perspective inequality
$$
x_i\psi\!\left(\frac{x_i}{X\omega_i}\right)
\le u_i\psi(a_i/\omega_i)+e_i\psi(\nu_i/\omega_i).
$$
A hypothetical $X<M$, together with (P), would force $\psi(\nu_i/\omega_i)>0$ for every $i$, hence $\nu_i>\omega_i$ for every $i$, impossible.

If $E>0$ and $f$ is strictly convex, equality forces all remainders positive and $a=\nu=\omega$. Mixed zero and positive remainders give $X=U+E>M$. If $E=0$, equality in this weaker theorem allows arbitrary $a$: it means only $X=M$. This differs from (H), whose zero-remainder equality additionally forces $a=\omega$, because $z-1-\log z$ vanishes only at one.

This is one mechanism, not a catalogue of unrelated inequalities. The logarithmic choice $\psi(z)=\log z$ weakens the right side of (H) from $u_i(a_i/\omega_i-1)$ to $u_i\log(a_i/\omega_i)$. The choice $\psi(z)=z-1$ is exactly (QH). More generally,
$$
\psi_s(z)=\frac{z^s-1}{s},\qquad \psi_0(z)=\log z,\qquad
(z\psi_s(z))''=(s+1)z^{s-1}.
$$
For $s>-1$ this gives comparison and strict-convexity rigidity. At $s=-1$ comparison survives, but pressure rigidity fails: the hypothesis reduces to $e_i\ge(M-U)\omega_i$, whose equality permits arbitrary $a$.

Strict increase without convex perspective is insufficient. For $\psi_{-2}(z)=(1-z^{-2})/2$, take
$$
\omega=(1/2,1/2),\quad x=(1/5,4/5),\quad
u=(1/20,9/20),\quad e=(3/20,7/20),\quad M=21/20.
$$
Here $U=E=1/2$ and $X=1<M$. Nevertheless (P) is equivalent to
$$
M^2\le x_i\left(U^2/u_i+e_i/\omega_i^2\right),
$$
whose two right sides are $28/25$ and $352/225$, both larger than $441/400=M^2$. This exact counterexample tests the proposed relaxation, not a Gaussian covariance.

The same perspective proof extends to densities $u,e>0$ relative to a probability measure, with positive finite totals and pointwise hypotheses almost everywhere. The contradiction is pointwise, so no entropy integrability is required beyond well-defined finite pointwise values. No infinite-dimensional Gaussian consumer is inferred merely from this measure version.

## 3. Entropy is a finer certificate, not the core proof

Return to positive $u_i,e_i$ and hypothesis (H). Let
$$
\delta=\log(X/M),\quad v_i=a_i/\omega_i,\quad h(v)=v-1-\log v,
\qquad
s_i=x_i\log\frac{x_i}{M\omega_i}-u_i(v_i-1)\ge0.
$$
The componentwise mixing loss is
$$
J_i=u_i\log v_i+e_i\log(\nu_i/\omega_i)
-x_i\log\frac{x_i}{X\omega_i}
=x_i d_{\rm Ber}(u_i/x_i\Vert U/X)\ge0,
$$
where $d_{\rm Ber}(p\Vert q)=p\log(p/q)+(1-p)\log((1-p)/(1-q))$.
Direct algebra gives
$$
x_i\delta+e_i\log(\nu_i/\omega_i)=u_i h(v_i)+s_i+J_i.
\tag{2}
$$
For probability vectors, let $D(p\Vert q)=\sum_i p_i\log(p_i/q_i)$. Divide (2) by $e_i$, average with $\omega_i$, and obtain
$$
\delta\sum_i\omega_i\frac{x_i}{e_i}
=D(\omega\Vert\nu)+
\sum_i\omega_i\left[
\frac{u_i}{e_i}h(v_i)+\frac{s_i+J_i}{e_i}
\right].
\tag{E}
$$
All terms on the right are nonnegative. In the Gaussian application $s_i$ itself retains separate support-concavity and geometric Cauchy losses; see the [original proof, section 8](../../../../inbox/pro-chat-exports/gaussian-extremal-theory/construction/2026-09-07-gpt6-five-site-global-methods-02/attachments/0012__ALL_DIMENSIONAL_FSC_PRESSURE_ENERGY_PROOF.md).

The exact identity remains valid for signed $s_i$. Thus the single compensated condition $\sum_i\omega_i s_i/e_i\ge0$ is sufficient for comparison and, unlike the quadratic aggregate, still forces full $a=\nu=\omega$ equality rigidity. The other pressure and information losses on the right remain nonnegative. This is a different, explicitly weighted hypothesis, not a rehabilitation of an arbitrary summed-entropy relaxation.

There is an exact variational form. Put
$$
b_i=x_i/e_i,\qquad c_i=[u_i h(v_i)+s_i+J_i]/e_i.
$$
Equation (2) says $\nu_i=\omega_i e^{c_i-\delta b_i}$, so
$$
\sum_i\omega_i e^{c_i-\delta b_i}=1,\qquad
\delta=\sup_{\pi\in\Delta}
\frac{\sum_i\pi_i c_i-D(\pi\Vert\omega)}
{\sum_i\pi_i b_i}.
\tag{G}
$$
To verify the supremum, its numerator minus $\delta$ times its denominator is $-D(\pi\Vert\nu)\le0$, with equality at $\pi=\nu$. Thus no separate infinite-dimensional variational theorem is needed. Certified lower costs $0\le\underline c_i\le c_i$ give $\delta\ge r$, where $r\ge0$ is the unique root of $\sum_i\omega_i e^{\underline c_i-rb_i}=1$.

The two losses are genuinely different. The pressure term $h$ is the Bregman divergence generated by $-\log$, whereas $J_i$ is the mixing deficit of $z\log z$. For the joint law $P(i,0)=u_i/X$, $P(i,1)=e_i/X$, $\sum J_i/X$ is the mutual information between the site and the component label. Treating all of them as a single unnamed KL penalty conceals which operation is being controlled.

## 4. Quantitative scope and adverse examples

If $u_i/x_i\in[q_-,q_+]\subset(0,1)$, set $B=(1-q_+)^{-1}$ and $m=q_-/(1-q_-)$. Equation (E) yields
$$
D(\omega\Vert\nu)\le B\delta,\qquad
D(\omega\Vert a)\le B\delta/m.
$$
Pinsker's inequality then gives the corresponding squared $\ell^1$ bounds with a factor two. These are conditional finite-distribution stability statements. Converting them to covariance distance requires additional geometric estimates and nondegeneracy; no uniform FSC stability theorem is asserted.

Both degenerations are real under (H):

- Fix $\omega=(1/2,1/2)$ and $a=(3/4,1/4)$. For $0<\alpha<2/3$, take $X=M e^{3\alpha/4}$, $x=X\omega$, $u=\alpha Xa$ and $e=x-u$. The first component of (H) is equality and the second is immediate. As $\alpha\downarrow0$, $\delta\to0$ while $a$ stays nonuniform.
- Fix positive $\nu\ne\omega$, let $\mu=(1-\beta)\omega+\beta\nu$, $m_\beta=\min_i\mu_i/\omega_i$, $X=M/m_\beta$, $x=X\mu$, $u=(1-\beta)X\omega$ and $e=\beta X\nu$. Every $x_i\ge M\omega_i$, so (H) holds. As $\beta\downarrow0$, $\delta\to0$ while $\nu$ stays nonuniform.

Even keeping positive $e_i$ does not permit summing the hypotheses first. Take $\omega=(1/2,1/2)$, $\mu=(9/10,1/10)$, $d_*=D(\mu\Vert\omega)>0$, $X=M e^{-d_*/2}$, $x=X\mu$, $u=\alpha X\omega$, $0<\alpha<1/5$. Then $e=x-u>0$, the summed left side of (H) is $Xd_*/2>0$ and the summed right side is zero, but $X<M$.

Conversely, retaining componentwise (H) but only a positive total $\sum e_i$, allowing negative individual remainders, also fails. The exact source counterexample is preserved in the [original audit](../FSC_PRESSURE_ENERGY_AUDIT_2026-09-07.md). These are different failures: lost componentwise inequalities and lost componentwise positivity.

## 5. Established theory and a tested Gaussian extension

The organizing outside operation is convex perspective, $t f(x/t)$: quadratic-over-linear and log-sum are two instances. This is standard convex analysis, not a new name for our result. [Boyd–Vandenberghe, section 3.2.6](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf). The exact Jensen/Bregman relation and the two generators above have the stated finite positive-domain hypotheses. [Banerjee et al., Definition 1, Table 1 and section 3.1.1](https://jmlr.org/papers/volume6/banerjee05b/banerjee05b.pdf). Our derived componentwise assembly, quantitative identities and tested consumer are stated explicitly rather than attributed as already present in those sources.

For $n\ge3$, $t>0$ and distinct centered unit-variance Gaussian scores with $\operatorname{rank}G\le n-1$, retain the canonical $a_i,k_i,C_i$ and $A_*=\sqrt{(n-2)/n}$. PSD stress is a sufficient way to obtain the original row condition, but the weaker logarithmic theorem needs only
$$
(n-2)\left(1-\frac{C_i}{k_iA_*}\right)\ge\log(na_i)
\quad\text{for every }i.
\tag{L}
$$
Actual support log-concavity and padded homothety then give (P) with $\psi=\log$, $x_i=H_i$, $u_i=tk_i/[(n-2)\phi(t)]$, $\omega_i=1/n$ and $M=np_0$. Therefore $F'_G(t)\ge n\phi(t)p_0$ whenever the common-support references have mass at least $p_0>0$. Equilibrium and PSD stress are not assumptions of this conditional boundary theorem. No regular-only equality classification is inherited after dropping PSD.

The weaker condition holds for some actual non-PSD configurations. For $n=4$, take normals $v,w,-v,-w$ with $c=v\cdot w=\sqrt3/2$, $\sigma=\sqrt{1-c^2}=1/2$. Let $q_\pm=\phi_2(t,t;\pm c)$. All pressure weights are $1/4$ and
$$
\frac{C_i}{k_i}=
\frac{\sigma}{1-c\tanh(ct^2/\sigma^2)}
\le\frac{1/2}{1-3t^2}
\le\frac8{13}<\frac1{\sqrt2}
\qquad(0<t\le1/4).
$$
Thus (L) holds, but $S_{ii}=c(q_--q_+)<0$. Small balanced rank-three disphenoid perturbations retain both strict inequalities at each fixed such threshold, by continuity of canonical pins.

This example establishes that PSD is not necessary. Its symmetry makes every facet bound individually favorable, so it does not exhibit a new pressure-compensation phenomenon. It is a boundary test, not an additional flagship theorem or an all-threshold flow.

### A genuine nonuniform-pressure compensation example

A three-score example separates the two row hypotheses and forces compensation between actual facet masses. Take
$$
v_0=(1,0),\quad v_1=(-3/5,4/5),\quad v_2=(-3/5,-4/5),
\qquad t^2=\frac9{10}\log\frac{120}{109}.
$$
At an apex/base pin the third score is $-11t/5<t$; at the base/base pin the apex is $-5t/3<t$. Thus the conditional probabilities in the canonical pins equal one, and
$$
q_A=\frac5{8\pi}e^{-5t^2/2},\qquad
q_B=\frac{25}{48\pi}e^{-25t^2/18},\qquad q_A/q_B=109/100.
$$
Directly,
$$
a=(109/298,189/596,189/596),\qquad
A=(1/2,229/378,229/378).
$$
The apex satisfies the stronger linear condition. Each base satisfies precisely the strict separation
$$
\log\frac{567}{596}
<1-\frac{229\sqrt3}{378}
<-\frac{29}{596}=3a_1-1.
$$
These inequalities have rational certificates: use $1.73205<\sqrt3<1.73206$ and $\log(1+z)\ge z-z^2/2$ at $z=29/567$. The [exact check](check_exact.py) verifies the rational margins, weights and stress. In fact
$$
S/q_B=\frac1{500}
\begin{pmatrix}654&545&545\\545&467&500\\545&500&467\end{pmatrix}
$$
has eigenvector $(0,1,-1)$ of eigenvalue $-33/500$, so it is not PSD.

The actual conditional intervals are $[-2t,2t]$ at the apex and $[-4t/3,2t]$ at either base. Every equal-support reference is $[-\sqrt3t,\sqrt3t]$, with mass $p_0=D_2(\sqrt3t)$. Since $\Phi$ is strictly concave on the positive axis,
$$
H_{\rm base}=\Phi(2t)+\Phi(4t/3)-1
<2\Phi(5t/3)-1<p_0,\qquad H_0>p_0.
$$
Nevertheless the weaker logarithmic assembly gives $H_0+2H_{\rm base}>3p_0$, with strictness because $a$ is not uniform. Hence $F'_G(t)>D'_3(t)$ although two actual facet masses are smaller than their references. All relevant inequalities are strict and persist in a small neighborhood. This is an actual rank-two Gaussian triangle, not independent scalar data; its positive geometric kernel $(3/8,5/16,5/16)$ is different from its canonical pressure distribution.

## 6. The exact qualitative scalar hypothesis: interpolation toward one

Construction03 sharpened section 2's sufficient convex-perspective criterion. The [joint ingestion](../POST_SOLUTION_03_OUTSIDE_01_INGESTION_2026-09-07.md) records independent reconstruction. Let $\psi:(0,\infty)\to\mathbb R$ be $C^1$ and strictly increasing, with $\psi(1)=0$ and $\psi'(1)>0$. Set
$$
f(z)=z\psi(z),\qquad R_\psi(z)=\frac{z\psi(z)}{z-1},\quad
R_\psi(1)=\psi'(1).
$$
The following are equivalent:

1. $R_\psi$ is nondecreasing on $(0,\infty)$.
2. $f(\alpha z+1-\alpha)\le\alpha f(z)$ for $z>0$ and $0\le\alpha\le1$; this is star-convexity about the reference one, not full convexity.
3. For every finite positive probability vector $\omega$, every $u_i,e_i>0$ and $M>0$, with $x_i=u_i+e_i$, $U=\sum u_i$, $X=\sum x_i$, $a_i=u_i/U$,
$$
x_i\psi\!\left(\frac{x_i}{M\omega_i}\right)
\ge u_i\psi\!\left(\frac{a_i}{\omega_i}\right)\quad\text{for every }i
\quad\Longrightarrow\quad X\ge M.
\tag{SC}
$$
4. The same implication holds for two components and arbitrary positive reference weights.

Dividing the anchored inequality by $z-1$, with the sign reversed on the left of one, gives equivalence of 1 and 2. Its differential form is
$z(z-1)\psi'(z)-\psi(z)\ge0$ for $z\ne1$.

Here is the mechanism of sufficiency. If $0<w\le1$, anchored convexity and strict increase of $\psi$ imply
$$
f(\alpha z+(1-\alpha)w)\le\alpha f(z),
\tag{A}
$$
strictly when $w<1$. For $z>1$, use the anchored secant if the argument exceeds one, and the sign of $f$ otherwise. For $z<1$, use the anchored secant when the argument is at least $z$; below $z$, use $\psi(m)\le\psi(z)<0$ and $m>\alpha z$ to get $m\psi(m)<\alpha z\psi(z)$. The case $z=1$ is immediate. Put $\alpha=U/X$, $\nu_i=e_i/(X-U)$, $z_i=a_i/\omega_i$, $w_i=\nu_i/\omega_i$, and $m_i=x_i/(X\omega_i)$. Some $w_i\le1$. If $X<M$, then
$m_i\psi((X/M)m_i)<f(m_i)\le\alpha f(z_i)$ at that index, contradicting (SC).

For necessity, failure of the anchored inequality gives $z>0$, $\alpha\in(0,1)$ and $w<1$ close enough to one that
$f(\alpha z+(1-\alpha)w)>\alpha f(z)$. Choose $\omega=(\varepsilon,1-\varepsilon)$,
$$
z_1=z,\ w_1=w,\quad
z_2=\frac{1-\varepsilon z}{1-\varepsilon},\
w_2=\frac{1-\varepsilon w}{1-\varepsilon}.
$$
Let $a_i=\omega_i z_i$, $\nu_i=\omega_i w_i$, $u_i=\alpha a_i$, $e_i=(1-\alpha)\nu_i$, so $X=1$. Choose $0<c<(1-\alpha)(1-w)$ and $M=(1-c\varepsilon)^{-1}>1$. The first row remains strict for small $\varepsilon$. In the second row, the difference in (SC), divided by $\omega_2$, equals
$$
\psi'(1)\bigl((1-\alpha)(1-w)-c\bigr)\varepsilon+o(\varepsilon)>0.
$$
Thus both hypotheses hold while $X<M$. This proves necessity with its actual regularity and variable-reference scope, not necessity for a fixed uniform Gaussian facet count.

If $R_\psi$ is strictly increasing on each side of one, equality in (SC) with all $e_i>0$ forces $a_i=\nu_i=\omega_i$ and $x_i=M\omega_i$. Indeed (A) first excludes any $w_i<1$, so $\nu=\omega$; strict anchored secants then force $z_i=1$. If some $e_i=0$, its row forces $U\ge M$; mixed zero and positive remainders prohibit equality. If all remainders vanish, pressure rigidity need not hold. Empty cells still cannot carry positive reference mass.

An exact enlargement of the sufficient class is
$$
\psi(z)=(1-1/z)(2-e^{-z}).
$$
Here $R_\psi'=e^{-z}>0$ and $z^2\psi'(z)=2+e^{-z}(z^2-z-1)>0$, but $f''(z)=e^{-z}(3-z)<0$ for $z>3$. Thus full convexity is not necessary. It remains useful for the quantitative Jensen, Bregman and KL losses above. A larger scalar class does not supply a new geometric support inequality by itself.

The Gaussian [covariance correction](COVARIANCE_CORRECTION.md) gives a different gain: its weighted aggregate equality becomes rigid because geometric variance losses are retained. This does not invalidate the weaker abstract aggregate equality counterexample.

### The sharp equality requirement is one-sided

A further independently checked extraction weakens the sufficient two-sided strictness above. Within the stated generator class, universal pressure rigidity for positive remainders holds if and only if $R_\psi$ is strictly increasing on at least one of $(0,1)$ or $(1,\infty)$. This is a universal assertion over finite families with at least two coordinates; the one-coordinate case is trivial.

At $X=M$, the preceding proof forces $\nu=\omega$. With $\alpha=U/X$ and $z_i=a_i/\omega_i$, equality in each row is precisely
$$
R_\psi(\alpha z_i+1-\alpha)=R_\psi(z_i).
$$
Strictness on one side forbids deviations on that side; $\sum_i\omega_i z_i=1$ then forbids deviations only on the other side. Conversely, if monotone $R_\psi$ is not strictly increasing on either side, it has a nontrivial flat interval on each. Choose $z_-<1<z_+$ inside these flats and positive weights with $\omega_-z_-+\omega_+z_+=1$. Choose $\alpha<1$ sufficiently close to one that both $\alpha z_\pm+1-\alpha$ stay in their flats. Taking $u_i=\alpha\omega_i z_i$, $e_i=(1-\alpha)\omega_i$, and $M=X=1$ gives nonrigid equality with all remainders positive. No new geometric support consumer follows from this refinement.
