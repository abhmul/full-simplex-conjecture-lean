import FSC.Support.Slicing
import FSC.LinearAlgebra.PaddedGram

/-! Actual orthogonal-projection Gaussian laws and the padded tangent realization of every pin. -/

noncomputable section

open MeasureTheory ProbabilityTheory Submodule
open scoped InnerProductSpace

namespace FSC

/-- Orthogonal projection has the standard Gaussian law on its full target subspace. -/
theorem map_orthogonalProjection_stdGaussian {d : ℕ} (K : Submodule ℝ (Coord d)) :
    (stdGaussian (Coord d)).map K.orthogonalProjectionOnto = stdGaussian K := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map]
    · simp only [integral_id_stdGaussian, map_zero]
    · exact IsGaussian.integrable_id
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian, covarianceBilin_stdGaussian,
      K.adjoint_orthogonalProjectionOnto]
    rfl

/-- The unit-normal residual is exactly the orthogonal-complement projection. -/
theorem normalResidual_eq_starProjection {d : ℕ} (w : Coord d) (hw : ‖w‖ = 1) :
    normalResidual w = (ℝ ∙ w)ᗮ.starProjection := by
  apply ContinuousLinearMap.ext
  intro y
  simp only [normalResidual_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hw]

/-- The ambient residual law is the actual standard Gaussian on the embedded tangent space. -/
theorem map_normalResidual_stdGaussian {d : ℕ} (w : Coord d) (hw : ‖w‖ = 1) :
    (stdGaussian (Coord d)).map (normalResidual w) =
      (stdGaussian ((ℝ ∙ w)ᗮ)).map ((ℝ ∙ w)ᗮ.subtypeL) := by
  rw [normalResidual_eq_starProjection w hw, Submodule.starProjection]
  change (stdGaussian (Coord d)).map
    (((ℝ ∙ w)ᗮ.subtypeL) ∘ ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), map_orthogonalProjection_stdGaussian]

/-- Every prescribed pin is translation of that same embedded tangent Gaussian. -/
theorem sliceLaw_eq_map_subspaceGaussian {d : ℕ} (w : Coord d) (hw : ‖w‖ = 1) (z : ℝ) :
    sliceLaw w z = (stdGaussian ((ℝ ∙ w)ᗮ)).map
      (fun y : (ℝ ∙ w)ᗮ ↦ z • w + (y : Coord d)) := by
  rw [sliceLaw_eq_map_normalResidual, map_normalResidual_stdGaussian w hw,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The frozen slice law is an actual affine image from the fixed `n-2` tangent coordinates. -/
theorem sliceLaw_eq_map_paddedTangent {n : ℕ} (hn : 3 ≤ n)
    (w : Coord (n - 1)) (hw : ‖w‖ = 1) (z : ℝ) :
    sliceLaw w z = (stdGaussian (Coord (n - 2))).map
      (fun y ↦ z • w + ((paddedTangentCoordinates hn w hw).symm y : Coord (n - 1))) := by
  have hmap := stdGaussian_map (paddedTangentCoordinates hn w hw).symm
  rw [sliceLaw_eq_map_subspaceGaussian w hw z, ← hmap,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end FSC
