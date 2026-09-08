import FSC.Gaussian.ProjectedNormals
import FSC.LinearAlgebra.PaddedGram
import FSC.Support.GramInvariance

/-! Projected facet normals in the fixed padded tangent dimension, with exact ordinary Gram agreement. -/

noncomputable section

open MeasureTheory ProbabilityTheory Submodule
open scoped InnerProductSpace

namespace FSC

/-- Projected unit direction in any specified realization of the original Gram matrix. -/
def realizationProjectedNormal {d n : ℕ} (v : Fin n → Coord d)
    (G : Mat n) (i : Fin n) (j : RetainedPair G i) : Coord d :=
  (pairSigma G i j)⁻¹ • (v j - G i j • v i)

theorem gram_realizationProjectedNormal {d n : ℕ} (v : Fin n → Coord d)
    (G : Mat n) (hG : G.PosSemidef) (hgram : Matrix.gram ℝ v = G) (i : Fin n) :
    Matrix.gram ℝ (realizationProjectedNormal v G i) = Matrix.gram ℝ (projectedNormal G i) := by
  have hi (j k : Fin n) : inner ℝ (v j) (v k) = G j k :=
    congrFun (congrFun hgram j) k
  ext j k
  simp only [Matrix.gram_apply, realizationProjectedNormal, projectedNormal,
    real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
    hi, inner_gramVectors G hG]

theorem realizationProjectedNormal_mem_tangent {d n : ℕ} (v : Fin n → Coord d)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (hgram : Matrix.gram ℝ v = G)
    (i : Fin n) (j : RetainedPair G i) : realizationProjectedNormal v G i j ∈ (ℝ ∙ v i)ᗮ := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
  have hi (k l : Fin n) : inner ℝ (v k) (v l) = G k l :=
    congrFun (congrFun hgram k) l
  simp only [realizationProjectedNormal, real_inner_smul_left, inner_sub_left,
    hi, hG.2, correlation_entry_symm G hG.1 i, mul_one, sub_self, mul_zero]

/-- The actual projected normal in the full padded tangent space. -/
def paddedFacetNormal {n : ℕ} (hn : 3 ≤ n) (v : Fin n → Coord (n - 1))
    (hv : ∀ k, ‖v k‖ = 1) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hgram : Matrix.gram ℝ v = G) (i : Fin n) (j : RetainedPair G i) : Coord (n - 2) :=
  paddedTangentCoordinates hn (v i) (hv i)
    ⟨realizationProjectedNormal v G i j, realizationProjectedNormal_mem_tangent v G hG hgram i j⟩

theorem gram_paddedFacetNormal {n : ℕ} (hn : 3 ≤ n) (v : Fin n → Coord (n - 1))
    (hv : ∀ k, ‖v k‖ = 1) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hgram : Matrix.gram ℝ v = G) (i : Fin n) :
    Matrix.gram ℝ (paddedFacetNormal hn v hv G hG hgram i) =
      Matrix.gram ℝ (projectedNormal G i) := by
  rw [← gram_realizationProjectedNormal v G hG.1 hgram i]
  ext j k
  simp only [Matrix.gram_apply, paddedFacetNormal, LinearIsometryEquiv.inner_map_map,
    Submodule.coe_inner]

theorem norm_paddedFacetNormal {n : ℕ} (hn : 3 ≤ n) (v : Fin n → Coord (n - 1))
    (hv : ∀ k, ‖v k‖ = 1) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hgram : Matrix.gram ℝ v = G) (i : Fin n) (j : RetainedPair G i) :
    ‖paddedFacetNormal hn v hv G hG hgram i j‖ = 1 := by
  rw [norm_eq_of_gram (gram_paddedFacetNormal hn v hv G hG hgram i) j]
  exact norm_projectedNormal G hG i j

theorem noCoincident_paddedFacetNormal {n : ℕ} (hn : 3 ≤ n) (v : Fin n → Coord (n - 1))
    (hv : ∀ k, ‖v k‖ = 1) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hgram : Matrix.gram ℝ v = G) (hDistinct : DistinctScores G)
    (i : Fin n) (t : ℝ) (ht : 0 < t) :
    NoCoincident (paddedFacetNormal hn v hv G hG hgram i) (fun j ↦ pairSupport G t i j) :=
  (noCoincident_projectedNormals G hG hDistinct i t ht).of_gram
    (norm_projectedNormal G hG i) (gram_paddedFacetNormal hn v hv G hG hgram i)

/-- All listed supports have exactly the same cap probability in ordinary and padded realizations. -/
theorem capMass_paddedFacetNormal {n : ℕ} (hn : 3 ≤ n) (v : Fin n → Coord (n - 1))
    (hv : ∀ k, ‖v k‖ = 1) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hgram : Matrix.gram ℝ v = G) (i : Fin n) (b : RetainedPair G i → ℝ) :
    capMass (paddedFacetNormal hn v hv G hG hgram i) b = capMass (projectedNormal G i) b :=
  capMass_eq_of_gram _ _ (gram_paddedFacetNormal hn v hv G hG hgram i) b

/-- The same physical slice gradient is retained in the padded tangent realization. -/
theorem supportGradient_paddedFacetNormal {n : ℕ} (hn : 3 ≤ n) (v : Fin n → Coord (n - 1))
    (hv : ∀ k, ‖v k‖ = 1) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hgram : Matrix.gram ℝ v = G) (hDistinct : DistinctScores G)
    (i : Fin n) (t : ℝ) (ht : 0 < t) :
    supportGradient (paddedFacetNormal hn v hv G hG hgram i) (fun j ↦ pairSupport G t i j) =
      supportGradient (projectedNormal G i) (fun j ↦ pairSupport G t i j) :=
  supportGradient_eq_of_gram _ _ (norm_projectedNormal G hG i)
    (gram_paddedFacetNormal hn v hv G hG hgram i) _
    (noCoincident_projectedNormals G hG hDistinct i t ht)

end FSC
