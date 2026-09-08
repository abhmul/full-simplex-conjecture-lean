# Proposed public statements and internal contracts

**Every Lean block in this document is schematic and uncompiled.** Names prefixed `FSC` are proposed declarations, not supplied library APIs. Proof bodies are deliberately not represented by axioms or placeholder Lean files. Existing exact names are catalogued separately in `SOURCE_MAP.md`.

## Public definitions and final theorem statements

Use transparent definitions initially. The public covariance predicate is the existing WSC predicate with no added covariance inequality.

```lean
namespace FSC
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Coord (n : ℕ) := WeakSimplex.Coord n
abbrev simplex (n : ℕ) : Mat n := WeakSimplex.regularSimplexGram n

noncomputable def cdf {n : ℕ} (G : Mat n) (t : ℝ) : ℝ :=
  (ProbabilityTheory.multivariateGaussian (0 : Coord n) G
    (WeakSimplex.lowerOrthant t)).toReal

def CorrSet (n : ℕ) : Set (Mat n) :=
  {G | WeakSimplex.IsCorrelation G}

def DistinctScores {n : ℕ} (G : Mat n) : Prop :=
  ∀ i j : Fin n, i ≠ j → G i j < 1

-- Proposed release theorems:
theorem cdf_simplex_le {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    cdf (simplex n) t ≤ cdf G t

theorem cdf_eq_simplex_iff {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (ht : 0 < t) :
    cdf G t = cdf (simplex n) t ↔ G = simplex n

theorem cdf_simplex_lt {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (ht : 0 < t) (hne : G ≠ simplex n) :
    cdf (simplex n) t < cdf G t

theorem lowerOrthant_simplex_le {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    ProbabilityTheory.multivariateGaussian (0 : Coord n) (simplex n)
      (WeakSimplex.lowerOrthant t) ≤
    ProbabilityTheory.multivariateGaussian (0 : Coord n) G
      (WeakSimplex.lowerOrthant t)
end FSC
```

The final equality theorem is not restricted to generic matrices. Prove the entrywise formula for `simplex n`: diagonal one and off-diagonal `-1 / ((n : ℝ) - 1)` for n≥2. This identifies the alias with `(nI-J)/(n-1)`, without ambiguity between natural subtraction and real subtraction. The definitions at n=0,1 are irrelevant; the theorems explicitly exclude them.

Also prove `cdf_eq_probability_coordinateMax_le` using the existing maximum/event dictionary, and obtain the stochastic-order tail statement by finite-measure complementation. This protects against accidentally reversing the stochastic-order convention.

## All-PSD law and continuity interfaces

Proposed law adapter, with all means and matrices explicit:

```lean
-- A : Matrix (Fin m) (Fin n) ℝ; no injectivity or full rank required.
-- lin A : Coord n →L[ℝ] Coord m is the matrix CLM.
theorem map_affine_multivariateGaussian
    (μ : Coord n) (G : Mat n) (hG : G.PosSemidef)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Coord m) :
    Measure.map (fun x ↦ b + lin A x)
      (multivariateGaussian μ G) =
    multivariateGaussian (b + lin A μ) (A * G * A.transpose)
```

The actual linear-map constructor should be the existing matrix-to-Euclidean CLM. Prove this through `IsGaussian.ext`; do not infer Gaussianity merely from first two moments. A companion theorem identifies `X + √s Y` under the product of the two centered PSD Gaussian laws with covariance `G+sL`, for s≥0.

```lean
theorem continuous_cdf_on_correlations {n : ℕ} :
    Continuous (fun p : {G : Mat n // WeakSimplex.IsCorrelation G} × ℝ ↦
      cdf p.1.1 p.2)

theorem isCompact_corrSet (n : ℕ) : IsCompact (CorrSet n)

theorem cdf_pos {n : ℕ} (hn : 1 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) (ht : 0 < t) :
    0 < cdf G t
```

Joint continuity has no distinctness assumption. The ordinary orthant null-frontier adapter needs only PSD and positive marginal variances; the correlation specialization has variance one. For a Gaussian with deterministic coordinates, any generalized null-frontier theorem must separately require that a deterministic mean differs from the relevant threshold. The pair success event excludes the pinned coordinates.

## Canonical pair law: freeze definitions before analytic parallelism

For i≠j and -1<c=Gij<1, define α,β and P as in `SUPPORT_NOISE_VARIATION.md`. Define `pairLaw G i j r s` as `multivariateGaussian (α*r+β*s) (P*G*Pᵀ)` on `Coord n`. Both scalar pin values are genuine real inputs, not values of a chosen conditional-probability version.

The core factorization theorem identifies the law of `(P X,(X_i,X_j))` with the product of its two Gaussian laws. Its hypotheses are `IsCorrelation G`, i≠j, and -1<Gij<1. Its residual is allowed to have rank zero. The covariance identities, product law and Fubini formula are separate named results.

Define `pairSuccess G i j t : ℝ` by the probability of `∀ k, k≠i → k≠j → x k≤t` under that pair law at (t,t). Define

```lean
-- Schematic piecewise definition; classical decidability is local.
q G t i j :=
  if i ≠ j ∧ -1 < G i j ∧ G i j < 1 then
    normalPDF t * normalPDF (t * (1 - G i j) / Real.sqrt (1 - (G i j)^2)) /
      Real.sqrt (1 - (G i j)^2) * pairSuccess G i j t
  else 0
```

The outside-domain zero convention is a totalization, not a covariance derivative assertion at duplicates or at zero threshold. Prove symmetry, nonnegativity, and the row-max positivity theorem at n≥3, t>0, distinct-coordinate correlations. Do not assert q>0 for every nonantipodal pair.

The one-pin law has mean `t * G[:,i]` and covariance `G-G[:,i]G[:,i]ᵀ`. Its remaining-coordinate success probability is `singlePinMass G t i`. Define `boundarySlope G t := normalPDF t * ∑ i, singlePinMass G t i`. The support realization must prove that this is exactly φ(t)∑H_i.

## Fixed-normal support calculus

Let d:ℕ, let ι be any finite type, and let `w : ι → Coord d`, `b : ι → ℝ`. Define

```lean
cap w b := {y : Coord d | ∀ j, inner (w j) y ≤ b j}
capMass w b := (stdGaussian (Coord d) (cap w b)).toReal
capEnergy w b := ∫ y in cap w b, ‖y‖ ^ 2 ∂stdGaussian (Coord d)
```

Here the inner product is real, all w_j are unit, and finite intersections give measurability. The finite type may be empty. Define `NoCoincident w b` by the two implications for equal and opposite normals, for each pair of distinct indices.

The C¹ interface must provide **a neighborhood**, not just coordinate derivatives at a point:

```lean
theorem support_C1_at
    (hw : ∀ j, ‖w j‖ = 1) (hsep : NoCoincident w b) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ b ∈ U ∧
      ContDiffOn ℝ 1 (capMass w) U ∧
      ∀ c ∈ U, HasFDerivAt (capMass w) (supportGradient w c) c
```

`supportGradient w c` is the explicit continuous linear map
`h ↦ ∑ j, normalPDF (c j) * sliceMass w c j * h j`, where `sliceMass` uses the fixed single-pin residual construction. Redundant inequalities have zero coefficients where appropriate. No boundedness, simplicity or linear independence of the w_j is assumed.

The support-convexity consumer-facing interface should be the tangent inequality, which permits either reciprocal or logarithmic implementation:

```lean
theorem quadratic_support_tangent
    (hw : ∀ j, ‖w j‖ = 1)
    (hb : ∀ j, 0 < b j) (hc : ∀ j, 0 < c j)
    (hsep : NoCoincident w b) :
    (capMass w b)^2 / capMass w c - capMass w b ≥
      supportGradient w b (b - c)
```

There is deliberately no `NoCoincident w c`. The actual point is differentiable; the reference need not be.

The scaling interface is

```lean
theorem hasDerivAt_capMass_dilate
    (hw : ∀ j, ‖w j‖ = 1) (b : ι → ℝ) :
    HasDerivAt (fun s : ℝ ↦ capMass w (s • b))
      ((d : ℝ) * capMass w b - capEnergy w b) 1
```

At s near one, `cap w (s • b)=s • cap w b`. This theorem does not need support differentiability, positivity of b, or boundedness of the cap. The positive-energy theorem separately assumes 1≤d and every b_j>0. Compatibility with the support gradient is a chain-rule corollary under `NoCoincident w b`. A separate product-space theorem records the exact energy contribution of padding.

## Peano expansion and the singular feasible derivative

Use a generic expansion predicate rather than a guessed multivariable Taylor declaration:

```lean
-- V is a finite-dimensional real normed vector space.
-- l : V →L[ℝ] ℝ; B : V →L[ℝ] V →L[ℝ] ℝ.
Peano2 f x l B :=
  (fun h ↦ f (x + h) - f x - l h - (1/2 : ℝ) * B h h)
    =o[𝓝 (0 : V)] (fun h ↦ ‖h‖ ^ 2)
```

The generic expectation theorem assumes a Borel measurable globally bounded f, a probability measure ν with zero vector mean and integrable squared norm, v(0)=0, a right derivative v'(0+)=v₀, and `Peano2 f x l B`. Its conclusion is

```lean
HasDerivWithinAt
  (fun s : ℝ ↦ ∫ y, f (x + v s + Real.sqrt s • y) ∂ν)
  (l v₀ + (1/2 : ℝ) * ∫ y, B y y ∂ν) (Set.Ici 0) 0
```

Prove `Peano2` for the threshold-vector CDF at t1 using repeated support C¹ calculus. The matrix of B must be exactly formula (T) in the support/noise note.

Define the normalized covariance entrywise:

```lean
normalizedAdd G L s i j :=
  (G i j + s * L i j) /
    (Real.sqrt (1 + s * L i i) * Real.sqrt (1 + s * L j j))
```

Its feasibility theorem has `hG : IsCorrelation G`, `hL : L.PosSemidef`, `hs : 0≤s`. No derivative is asserted on non-PSD matrices. The main analytic contract is

```lean
theorem hasDerivWithinAt_normalizedAdd
    {n : ℕ} (hn : 3 ≤ n)
    (G L : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (hL : L.PosSemidef)
    (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt (fun s ↦ cdf (normalizedAdd G L s) t)
      ((1/2 : ℝ) * Matrix.trace (stress G t * L)) (Set.Ici 0) 0
```

A rank-one specialization supplies the n finite z_i tests. The same general statement with L=G-δJ excludes positive-definite minima. These are right-derivative inequalities at a minimum, not zero derivative equations.

## Rank and facet compatibility

```lean
theorem exists_padded_unit_gram {n : ℕ} (hn : 3 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hnotPD : ¬ G.PosDef) :
    ∃ v : Fin n → Coord (n - 1),
      (∀ i, ‖v i‖ = 1) ∧ WeakSimplex.codeGram v = G
```

For each i, construct an isometry from its tangent hyperplane to `Coord (n-2)`. Its retained index type is `{j : Fin n // j≠i ∧ -1<G i j}`. The maps w_i,b_i have the formulas from the dossier. The compatibility theorem must simultaneously identify:

`singlePinMass G t i = capMass w_i b_i`,

`supportGradient w_i b_i (coordinate j) = σij*qij/φ(t)`,

`supportGradient w_i b_i b_i = t*k_i/φ(t)`,

`supportGradient w_i b_i 1 = C_i/φ(t)`.

The same selected Gram realization and tangent isometry must be used across these identities. All probabilities are invariant under changing the isometry, but that invariance is a proved law adapter, not a definitional equality to assume.

## Scalar and global assembly contracts

For `[Fintype ι] [Nonempty ι]`, real u,e,ω on ι, M>0, positivity of every u_i,e_i,ω_i, ∑ω_i=1, and componentwise (C), export both `M≤∑(u_i+e_i)` and the equality conclusion `u_i/U=e_i/E=ω_i` and `u_i+e_i=M*ω_i`. Positivity of every remainder is part of the actual theorem; the documented zero-component counterexample prevents weakening it silently.

The boundary theorem should consume the lower-size **comparison only**, not lower-size uniqueness. With n≥3,t>0, `hG : IsCorrelation G` and

`hMin : ∀ C, IsCorrelation C → cdf G t ≤ cdf C t`,

plus lower-size comparison at ρ=t√(n/(n-2)), return

1. `HasDerivAt (cdf G) (boundarySlope G t) t`;
2. `n * normalPDF t * cdf (simplex (n-1)) ρ ≤ boundarySlope G t`;
3. equality in 2 implies `G = simplex n`.

Duplicate and positive-definite exclusions belong inside the passage from `hMin` to the analytic hypotheses. Do not expose singularity or distinctness as unproved assumptions of the final induction theorem.

The barrier theorem can be proved abstractly on a nonempty compact shape space K, with continuous f:K×[0,∞)→[0,1], continuous D:[0,∞)→[0,1], D(0)=0, and the fixed-threshold minimizer slope inequality for every t>0. It returns D(t)≤f(k,t). The equality corollary adds the boundary equality implication. These abstract hypotheses must be explicit in any provisional assembly, and fully discharged before the public FSC root is accepted.

### Explicit scalar signatures

These remain **schematic, uncompiled Lean signatures**. The sums range over the whole finite nonempty index type, and all divisions are in ℝ.

```lean
theorem componentwise_compare
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u e omega : ι → ℝ) (M : ℝ)
    (hu : ∀ i, 0 < u i) (he : ∀ i, 0 < e i)
    (ho : ∀ i, 0 < omega i) (hM : 0 < M)
    (homega : ∑ i, omega i = 1)
    (hcomp : ∀ i,
      (u i + e i)^2 / M - (u i)^2 / (∑ j, u j)
        ≥ omega i * e i) :
    M ≤ ∑ i, (u i + e i)

theorem componentwise_equality
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u e omega : ι → ℝ) (M : ℝ)
    (hu : ∀ i, 0 < u i) (he : ∀ i, 0 < e i)
    (ho : ∀ i, 0 < omega i) (hM : 0 < M)
    (homega : ∑ i, omega i = 1)
    (hcomp : ∀ i,
      (u i + e i)^2 / M - (u i)^2 / (∑ j, u j)
        ≥ omega i * e i)
    (heq : ∑ i, (u i + e i) = M) :
    ∀ i, u i / (∑ j, u j) = omega i ∧
      e i / (∑ j, e j) = omega i ∧ u i + e i = M * omega i
```

### An explicit abstract barrier signature

This convenient version assumes joint continuity on all real thresholds; the application has it. It needs derivative information only at positive-threshold global shape minimizers. No differentiability of the minimum envelope is assumed.

```lean
theorem compact_slope_comparison
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (f : K → ℝ → ℝ) (D d : ℝ → ℝ)
    (hf : Continuous (fun p : K × ℝ ↦ f p.1 p.2))
    (hD : Continuous D)
    (hf_bounds : ∀ k t, 0 ≤ f k t ∧ f k t ≤ 1)
    (hD_bounds : ∀ t, 0 ≤ D t ∧ D t ≤ 1)
    (hD_zero : D 0 = 0)
    (hD_deriv : ∀ t, 0 < t → HasDerivAt D (d t) t)
    (hmin_slope : ∀ k t, 0 < t →
      (∀ l, f k t ≤ f l t) →
      ∃ v : ℝ, HasDerivAt (f k) v t ∧ d t ≤ v) :
    ∀ k t, 0 ≤ t → D t ≤ f k t
```

A reference shape attaining D is useful in the FSC interpretation but is **not needed by this abstract comparison theorem**. The proof uses only bounds, continuity, D(0)=0 and the minimizer slope condition. Negative-threshold comparison is discharged separately for FSC by D(t)=0. Equality rigidity is a separate theorem after comparison, using the derivative of the fixed-shape nonnegative difference at its positive zero.
