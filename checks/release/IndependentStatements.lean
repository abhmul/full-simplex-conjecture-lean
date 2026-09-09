import FSC

/-! Independent public-root statement checks. Every endpoint below expands the
correlation predicate, the covariance normalization and the actual Gaussian event. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FSCChecks.IndependentStatements

theorem simplex_matrix_expanded {n : ℕ} (hn : 2 ≤ n) :
    FSC.simplex n = (1 / ((n : ℝ) - 1)) •
      ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ))) :=
  FSC.simplex_eq_scaled_matrix hn

theorem correlation_expanded {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) :
    WeakSimplex.IsCorrelation G ↔ G.PosSemidef ∧ ∀ i, G i i = 1 := Iff.rfl

theorem gaussian_event_expanded {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    FSC.cdf G t =
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) G {x | ∀ i, x i ≤ t}).toReal :=
  rfl

/-- Every real threshold and every PSD matrix with unit diagonal, in actual event measure form. -/
theorem comparison_expanded {n : ℕ} (hn : 2 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ)
    (hPSD : G.PosSemidef) (hdiag : ∀ i, G i i = 1) (t : ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        ((1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ)))) {x | ∀ i, x i ≤ t} ≤
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) G {x | ∀ i, x i ≤ t} := by
  rw [← simplex_matrix_expanded hn]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact FSC.cdf_simplex_le hn G ⟨hPSD, hdiag⟩ t

/-- Equality of the actual probabilities at one fixed positive threshold characterizes Δ. -/
theorem equality_expanded {n : ℕ} (hn : 2 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ)
    (hPSD : G.PosSemidef) (hdiag : ∀ i, G i i = 1) (t : ℝ) (ht : 0 < t) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) G {x | ∀ i, x i ≤ t} =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        ((1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ)))) {x | ∀ i, x i ≤ t}) ↔
      G = (1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ))) := by
  rw [← simplex_matrix_expanded hn]
  constructor
  · intro heq
    exact (FSC.cdf_eq_simplex_iff hn G ⟨hPSD, hdiag⟩ t ht).mp (congrArg ENNReal.toReal heq)
  · rintro rfl
    rfl

/-- Strictness has precisely the nonsimplex and positive-threshold conditions. -/
theorem strict_comparison_expanded {n : ℕ} (hn : 2 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ)
    (hPSD : G.PosSemidef) (hdiag : ∀ i, G i i = 1) (t : ℝ) (ht : 0 < t)
    (hne : G ≠ (1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ)))) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        ((1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ)))) {x | ∀ i, x i ≤ t} <
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) G {x | ∀ i, x i ≤ t} := by
  rw [← simplex_matrix_expanded hn] at hne ⊢
  apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact FSC.cdf_simplex_lt hn G ⟨hPSD, hdiag⟩ t ht hne

theorem tail_event_expanded {n : ℕ} (hn : 0 < n) (t : ℝ) :
    {x : EuclideanSpace ℝ (Fin n) | ∃ i, t < x i} =
      {x | t < WeakSimplex.coordinateMax hn x} := by
  ext x
  have h := not_congr (WeakSimplex.coordinateMax_le_iff_mem_lowerOrthant hn x t)
  simpa only [not_le, WeakSimplex.lowerOrthant, Set.mem_setOf_eq, not_forall] using h.symm

/-- The simplex maximizes the upper tail: the arbitrary-correlation measure is on the left. -/
theorem tail_comparison_expanded {n : ℕ} (hn : 2 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ)
    (hPSD : G.PosSemidef) (hdiag : ∀ i, G i i = 1) (t : ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) G {x | ∃ i, t < x i} ≤
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        ((1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ)))) {x | ∃ i, t < x i} := by
  rw [← simplex_matrix_expanded hn, tail_event_expanded (by omega : 0 < n) t]
  exact FSC.coordinateMax_tail_le_simplex hn G ⟨hPSD, hdiag⟩ t

theorem strict_tail_comparison_expanded {n : ℕ} (hn : 2 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ)
    (hPSD : G.PosSemidef) (hdiag : ∀ i, G i i = 1) (t : ℝ) (ht : 0 < t)
    (hne : G ≠ (1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ)))) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) G {x | ∃ i, t < x i} <
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        ((1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ)))) {x | ∃ i, t < x i} := by
  rw [← simplex_matrix_expanded hn] at hne ⊢
  rw [tail_event_expanded (by omega : 0 < n) t]
  exact FSC.coordinateMax_tail_lt_simplex hn G ⟨hPSD, hdiag⟩ t ht hne

theorem tail_equality_expanded {n : ℕ} (hn : 2 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ)
    (hPSD : G.PosSemidef) (hdiag : ∀ i, G i i = 1) (t : ℝ) (ht : 0 < t) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) G {x | ∃ i, t < x i} =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        ((1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ)))) {x | ∃ i, t < x i}) ↔
      G = (1 / ((n : ℝ) - 1)) • ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ))) := by
  rw [← simplex_matrix_expanded hn, tail_event_expanded (by omega : 0 < n) t]
  exact FSC.coordinateMax_tail_eq_simplex_iff hn G ⟨hPSD, hdiag⟩ t ht

end FSCChecks.IndependentStatements

#print WeakSimplex.IsCorrelation
#print FSC.cdf
#check FSC.simplex_apply
#check FSCChecks.IndependentStatements.simplex_matrix_expanded
#check FSCChecks.IndependentStatements.gaussian_event_expanded
#check FSC.cdf_simplex_le
#check FSC.cdf_eq_simplex_iff
#check FSC.cdf_simplex_lt
#check FSCChecks.IndependentStatements.comparison_expanded
#check FSCChecks.IndependentStatements.equality_expanded
#check FSCChecks.IndependentStatements.strict_comparison_expanded
#check FSC.lowerOrthant_simplex_le
#check FSC.coordinateMax_tail_le_simplex
#check FSC.coordinateMax_tail_lt_simplex
#check FSC.coordinateMax_tail_eq_simplex_iff
#check FSCChecks.IndependentStatements.tail_comparison_expanded
#check FSCChecks.IndependentStatements.strict_tail_comparison_expanded
#check FSCChecks.IndependentStatements.tail_equality_expanded

#print axioms FSC.cdf_simplex_le
#print axioms FSC.cdf_eq_simplex_iff
#print axioms FSC.cdf_simplex_lt
#print axioms FSC.lowerOrthant_simplex_le
#print axioms FSC.coordinateMax_tail_le_simplex
#print axioms FSC.coordinateMax_tail_lt_simplex
#print axioms FSC.coordinateMax_tail_eq_simplex_iff
#print axioms FSCChecks.IndependentStatements.simplex_matrix_expanded
#print axioms FSCChecks.IndependentStatements.correlation_expanded
#print axioms FSCChecks.IndependentStatements.gaussian_event_expanded
#print axioms FSCChecks.IndependentStatements.comparison_expanded
#print axioms FSCChecks.IndependentStatements.equality_expanded
#print axioms FSCChecks.IndependentStatements.strict_comparison_expanded
#print axioms FSCChecks.IndependentStatements.tail_event_expanded
#print axioms FSCChecks.IndependentStatements.tail_comparison_expanded
#print axioms FSCChecks.IndependentStatements.strict_tail_comparison_expanded
#print axioms FSCChecks.IndependentStatements.tail_equality_expanded
