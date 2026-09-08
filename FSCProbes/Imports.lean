/- Pinned source/API probes. This module is outside the FSC release root. -/
import WeakSimplexConjectureLean.Core.Correlation
import WeakSimplexConjectureLean.Core.Euclidean
import WeakSimplexConjectureLean.Coding.Gram
import WeakSimplexConjectureLean.Coding.BayesValue
import WeakSimplexConjectureLean.Normal.PDFCDF
import WeakSimplexConjectureLean.Normal.TruncatedMoments
import WeakSimplexConjectureLean.LogConcavity.Prekopa
import WeakSimplexConjectureLean.LogConcavity.Indicators
import WeakSimplexConjectureLean.Gaussian.Regularization
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.LinearAlgebra.Matrix.PosDef

#check WeakSimplex.IsCorrelation
#check WeakSimplex.Coord
#check WeakSimplex.lowerOrthant
#check WeakSimplex.measurableSet_lowerOrthant
#check WeakSimplex.regularSimplexGram
#check WeakSimplex.gramNormalization
#check WeakSimplex.map_codeScore_stdGaussian
#check WeakSimplex.normalPDF_pos
#check WeakSimplex.hasDerivAt_normalPDF
#check WeakSimplex.hasDerivAt_normalCDF
#check WeakSimplex.truncated_second_moment
#check WeakSimplex.isLogConcave_lintegral_right
#check WeakSimplex.measurable_isLogConcave_lintegral_right
#check WeakSimplex.map_gaussianRegularization_eq_multivariateGaussian
#check WeakSimplex.tendstoInDistribution_regularized_multivariateGaussian
#check ProbabilityTheory.multivariateGaussian
#check ProbabilityTheory.multivariateGaussian_of_not_posSemidef
#check ProbabilityTheory.IsGaussian.ext
#check ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eval
#check ProbabilityTheory.measurePreserving_eval_multivariateGaussian
#check MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun
#check MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
#check MeasureTheory.Measure.integral_comp_smul
#check hasDerivAt_integral_of_dominated_loc_of_deriv_le
#check Matrix.PosDef.fromBlocks₁₁

noncomputable section

open Filter MeasureTheory ProbabilityTheory WeakSimplex
open scoped ENNReal Topology InnerProductSpace

namespace FSCProbes.Imports

/-- The public Gram-score law gives the actual orthant event without rank or unit assumptions. -/
theorem gram_lowerOrthant {m d : ℕ} (code : Fin m → Coord d) (t : ℝ) :
    multivariateGaussian (0 : Coord m) (codeGram code) (lowerOrthant t) =
      stdGaussian (Coord d) {y | ∀ i, ⟪code i, y⟫_ℝ ≤ t} := by
  rw [← map_codeScore_stdGaussian code,
    Measure.map_apply (by unfold Coord.ofFun; fun_prop) (measurableSet_lowerOrthant t)]
  rfl

/-- Build the joint Gaussian law through one linear map before using coordinate independence. -/
theorem joint_linear_image_factorization {d m k : ℕ}
    (G : Matrix (Fin d) (Fin d) ℝ)
    (A : Coord d →L[ℝ] (Fin m → ℝ)) (B : Coord d →L[ℝ] (Fin k → ℝ))
    (hcross : ∀ i j,
      cov[fun x ↦ A x i, fun x ↦ B x j; multivariateGaussian (0 : Coord d) G] = 0) :
    (multivariateGaussian (0 : Coord d) G).map (fun x ↦ (A x, B x)) =
      ((multivariateGaussian (0 : Coord d) G).map A).prod
        ((multivariateGaussian (0 : Coord d) G).map B) := by
  have hjoint : HasGaussianLaw (fun x : Coord d ↦ (A x, B x))
      (multivariateGaussian (0 : Coord d) G) :=
    IsGaussian.hasGaussianLaw_id.map (A.prod B)
  have hindep := hjoint.indepFun_of_covariance_eval hcross
  exact hindep.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)

/-- An affine image is Gaussian even when the linear map has rank zero. -/
theorem affine_image_isGaussian {d m : ℕ}
    (G : Matrix (Fin d) (Fin d) ℝ) (A : Coord d →L[ℝ] Coord m) (b : Coord m) :
    IsGaussian ((multivariateGaussian (0 : Coord d) G).map (fun x ↦ A x + b)) := by
  have hmap :
      ((multivariateGaussian (0 : Coord d) G).map A).map (fun y ↦ y + b) =
        (multivariateGaussian (0 : Coord d) G).map (fun x ↦ A x + b) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [← hmap]
  infer_instance

/-- Direct finite-dimensional Prékopa consumer for measurable convex support sections. -/
theorem convex_support_marginal {m d : ℕ}
    (s : Set ((Fin m → ℝ) × (Fin d → ℝ)))
    (hs : MeasurableSet s) (hc : Convex ℝ s) :
    Measurable (fun r : Fin m → ℝ ↦ ∫⁻ y : Fin d → ℝ, convexIndicator s (r, y)) ∧
      IsLogConcave (fun r : Fin m → ℝ ↦ ∫⁻ y : Fin d → ℝ,
        convexIndicator s (r, y)) := by
  exact measurable_isLogConcave_lintegral_right
    (measurable_convexIndicator hs) (isLogConcave_convexIndicator hc)

/-- The pinned Schur API is in `Matrix.PosDef`, despite the source header's inventory. -/
theorem schur_complement_posSemidef {m d : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin d) ℝ)
    (D : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) [Invertible A]
    (hblock : (Matrix.fromBlocks A B B.conjTranspose D).PosSemidef) :
    (D - B.conjTranspose * A⁻¹ * B).PosSemidef :=
  (Matrix.PosDef.fromBlocks₁₁ B D hA).mp hblock

/-- Haar scaling uses the ambient dimension, including dimension zero. -/
theorem haar_scaling {d : ℕ} (f : (Fin d → ℝ) → ℝ) (r : ℝ) :
    (∫ x : Fin d → ℝ, f (r • x)) =
      |(r ^ d)⁻¹| * ∫ x : Fin d → ℝ, f x := by
  simpa using Measure.integral_comp_smul (volume : Measure (Fin d → ℝ)) f r

/-- A concrete dominated-derivative consumer: integrate scalar dilation of any L1 function. -/
theorem hasDerivAt_integral_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ ∫ a, x * f a ∂μ) (∫ a, f a ∂μ) x₀ := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x a ↦ x * f a) (F' := fun _ a ↦ f a)
    (bound := fun a ↦ ‖f a‖) (s := Set.univ) (x₀ := x₀)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun x ↦ (hf.const_mul x).aestronglyMeasurable)
    (hf.const_mul x₀) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ _ _ ↦ le_rfl) hf.norm
    (Filter.Eventually.of_forall fun a x _ ↦ by
      simpa using (hasDerivAt_id x).mul_const (f a))
  exact h.2

end FSCProbes.Imports

#print FSCProbes.Imports.gram_lowerOrthant
#print FSCProbes.Imports.joint_linear_image_factorization
#print FSCProbes.Imports.affine_image_isGaussian
#print FSCProbes.Imports.convex_support_marginal
#print FSCProbes.Imports.schur_complement_posSemidef
#print FSCProbes.Imports.haar_scaling
#print FSCProbes.Imports.hasDerivAt_integral_mul
#print axioms FSCProbes.Imports.gram_lowerOrthant
#print axioms FSCProbes.Imports.joint_linear_image_factorization
#print axioms FSCProbes.Imports.affine_image_isGaussian
#print axioms FSCProbes.Imports.convex_support_marginal
#print axioms FSCProbes.Imports.schur_complement_posSemidef
#print axioms FSCProbes.Imports.haar_scaling
#print axioms FSCProbes.Imports.hasDerivAt_integral_mul
