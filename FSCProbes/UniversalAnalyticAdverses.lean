import FSC.Gaussian.ThresholdExpansion
import FSC.Simplex.BaseCases
import FSCProbes.TriangleVariation

/-! Concrete consumers of the closed universal derivative. The five-direction
example reuses the rational directions in checks/wp05-support/Adverse.lean.
The independent triangle calculation remains in its original module. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Topology BigOperators

namespace FSCProbes.UniversalAnalyticAdverses

open FSC

theorem triangle_trace_coefficient (t : ℝ) (ht : 0 < t) :
    (1 / 2 : ℝ) * Matrix.trace
      (stress SingularTriangle.gram t * TriangleVariation.noiseCov) =
      -(2 / 5 : ℝ) * q SingularTriangle.gram t 1 2 := by
  have h20 : q SingularTriangle.gram t 2 0 = 0 := by
    rw [q_symm _ SingularTriangle.gram_isCorrelation, SingularTriangle.q_02 t ht]
  have h21 : q SingularTriangle.gram t 2 1 = q SingularTriangle.gram t 1 2 :=
    q_symm _ SingularTriangle.gram_isCorrelation 2 1 t
  norm_num [Matrix.trace, Matrix.mul_apply, TriangleVariation.noiseCov,
    stress, SingularTriangle.gram, Fin.sum_univ_succ]
  simp only [SingularTriangle.gram] at h20 h21
  rw [h20, h21]
  ring

/-- The universal theorem has the same canonical q coefficient as the independent proof. -/
theorem triangle_universal_derivative (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt
      (fun s ↦ cdf (normalizedAdd SingularTriangle.gram TriangleVariation.noiseCov s) t)
      (-(2 / 5 : ℝ) * q SingularTriangle.gram t 1 2) (Set.Ici 0) 0 := by
  rw [← triangle_trace_coefficient t ht]
  exact FSC.hasDerivWithinAt_normalizedAdd _ _ SingularTriangle.gram_isCorrelation
    SingularTriangle.gram_distinct TriangleVariation.noiseCov_posSemidef t ht

def planarNormals : Fin 5 → Coord 2 :=
  ![WeakSimplex.Coord.ofFun ![1, 0], WeakSimplex.Coord.ofFun ![0, 1],
    WeakSimplex.Coord.ofFun ![3 / 5, 4 / 5], WeakSimplex.Coord.ofFun ![-1, 0],
    WeakSimplex.Coord.ofFun ![0, -1]]

theorem planar_unit (j : Fin 5) : ‖planarNormals j‖ = 1 := by
  have hs : ‖planarNormals j‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases j <;> norm_num [planarNormals, Fin.sum_univ_two]
  nlinarith [norm_nonneg (planarNormals j)]

theorem planar_injective : Function.Injective planarNormals := by
  intro i j heq
  have h₀ := congrArg (fun v : Coord 2 ↦ v 0) heq
  have h₁ := congrArg (fun v : Coord 2 ↦ v 1) heq
  fin_cases i <;> fin_cases j <;> norm_num [planarNormals] at *

def fiveGram : Mat 5 := WeakSimplex.codeGram planarNormals

theorem fiveGram_rank_le_two : fiveGram.rank ≤ 2 := by
  let A : Matrix (Fin 5) (Fin 2) ℝ := fun i j ↦ planarNormals i j
  have hA : fiveGram = A * A.transpose := by
    ext i j
    simp [fiveGram, WeakSimplex.codeGram, Matrix.gram_apply, PiLp.inner_apply,
      Matrix.mul_apply, A, mul_comm]
  rw [hA]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width A)

theorem fiveGram_isCorrelation : WeakSimplex.IsCorrelation fiveGram := by
  refine ⟨WeakSimplex.codeGram_posSemidef planarNormals, fun i ↦ ?_⟩
  simp [fiveGram, WeakSimplex.codeGram, Matrix.gram_apply, planar_unit]

theorem fiveGram_distinct : DistinctScores fiveGram := by
  intro i j hij
  exact (inner_lt_one_iff_real_of_norm_eq_one (planar_unit i) (planar_unit j)).mpr
    (fun h ↦ hij (planar_injective h))

theorem fiveGram_actual_law :
    Measure.map
      (fun z : Coord 2 ↦ WeakSimplex.Coord.ofFun (fun i ↦ inner ℝ (planarNormals i) z))
      (stdGaussian (Coord 2)) = multivariateGaussian (0 : Coord 5) fiveGram :=
  WeakSimplex.map_codeScore_stdGaussian planarNormals

theorem fiveGram_actual_peano (t : ℝ) (ht : 0 < t) :
    Peano2 (thresholdCDF fiveGram) (WeakSimplex.Coord.ofFun (fun _ : Fin 5 ↦ t))
      (thresholdGradient fiveGram (WeakSimplex.Coord.ofFun (fun _ : Fin 5 ↦ t)))
      (fderiv ℝ (thresholdGradient fiveGram)
        (WeakSimplex.Coord.ofFun (fun _ : Fin 5 ↦ t))) :=
  peano2_thresholdCDF fiveGram fiveGram_isCorrelation fiveGram_distinct t ht

theorem fiveGram_actual_variation (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt (fun s ↦ cdf (normalizedAdd fiveGram 1 s) t)
      ((1 / 2 : ℝ) * Matrix.trace (stress fiveGram t)) (Set.Ici 0) 0 := by
  simpa only [Matrix.mul_one] using FSC.hasDerivWithinAt_normalizedAdd
    fiveGram 1 fiveGram_isCorrelation fiveGram_distinct Matrix.PosSemidef.one t ht

/-- Duplicate scores really fail the internal distinctness condition. -/
theorem duplicate_scores_excluded : ¬DistinctScores (fun _ _ : Fin 2 ↦ (1 : ℝ)) := by
  intro h
  have := h 0 1 (by decide)
  norm_num at this

/-- The positive tied-support reference really is nondifferentiable. -/
theorem duplicate_support_not_differentiable (t : ℝ) :
    ¬DifferentiableAt ℝ
      (fun b : ℝ ↦ capMass SingularTriangle.redundantNormals ![t, b]) t :=
  SingularTriangle.not_differentiableAt_tied_support t

/-- Positive-threshold regularity cannot extend to the antipodal corner at zero. -/
theorem antipodal_zero_not_differentiable :
    ¬DifferentiableAt ℝ (cdf (simplex 2)) 0 := by
  intro hf
  have hleft : HasDerivWithinAt (cdf (simplex 2)) 0 (Set.Iic 0) 0 := by
    apply ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt
      (s := Set.Iic 0)).congr_of_mem
    · intro b hb
      exact simplex_cdf_nonpos (by norm_num) b hb
    · exact Set.self_mem_Iic
  have hright : HasDerivWithinAt (cdf (simplex 2))
      (2 * WeakSimplex.normalPDF 0) (Set.Ici 0) 0 := by
    apply ((((WeakSimplex.hasDerivAt_normalCDF 0).const_mul 2).sub_const 1).hasDerivWithinAt
      (s := Set.Ici 0)).congr_of_mem
    · intro b hb
      exact simplex_two_cdf b hb
    · exact Set.self_mem_Ici
  have hl := hleft.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))
  have hr := hright.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
  rw [hf.derivWithin (uniqueDiffWithinAt_Iic (0 : ℝ))] at hl
  rw [hf.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))] at hr
  have hpos := WeakSimplex.normalPDF_pos 0
  linarith

end FSCProbes.UniversalAnalyticAdverses
