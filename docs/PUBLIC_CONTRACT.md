# Exact FSC certification contract

Status: mathematical contract frozen for implementation; no listed release theorem is implemented yet.

For every integer $n\ge2$, every real positive-semidefinite correlation matrix $G$, and every real $t$, put
$$
\Delta_n=(nI-J)/(n-1),\qquad
F_G(t)=\Pr_{X\sim N(0,G)}(\forall i,\ X_i\le t).
$$
Certify
$$
F_{\Delta_n}(t)\le F_G(t).
$$
Separately, for every fixed $t>0$, certify
$$
F_G(t)=F_{\Delta_n}(t)\quad\Longleftrightarrow\quad G=\Delta_n.
$$

Use the transparent existing WeakSimplex.IsCorrelation predicate, not IsWeakSimplexCov. A public real CDF must have a proved bridge to the actual Gaussian event measure. Identify WeakSimplex.regularSimplexGram with the displayed matrix under n≥2; audit natural versus real subtraction. Expose the strict positive-threshold inequality and finite-maximum tail corollary with the direction checked.

Comparison includes every PSD rank, duplicates, antipodes and nonpositive thresholds. Equality includes every correlation matrix at a positive threshold; no generic-position hypothesis remains. Do not certify only the normalized WSC theorem, an MGF comparison, balanced matrices, honest simplices, full rank, or a conditional analytic-certificate statement.

Proposed public names and schematic types are in [the returned interfaces](pro-return/INTERFACES.md). They are design inputs, not elaborated declarations. The lead may fix syntax and representation while preserving this exact mathematical contract; any substantive change requires review. Before acceptance, independently inspect fully printed types and unfold predicate aliases.

The intended axiom whitelist is any subset of propext, Classical.choice and Quot.sound. An ordinary-axiom proof of a different or conditional statement is not acceptance. Final source, dependency revisions, command exits and the fresh axiom report must identify the same revision.
