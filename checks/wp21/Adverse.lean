import FSC.Simplex.BaseCases
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace FSCChecks

def duplicatedTwo : FSC.Mat 2 := fun _ _ ↦ 1

theorem duplicatedTwo_corr : WeakSimplex.IsCorrelation duplicatedTwo := by
  have heq : duplicatedTwo = Matrix.vecMulVec (fun _ : Fin 2 ↦ (1 : ℝ))
      (star (fun _ : Fin 2 ↦ (1 : ℝ))) := by ext i j; simp [duplicatedTwo, Matrix.vecMulVec_apply]
  exact ⟨heq ▸ Matrix.posSemidef_vecMulVec_self_star _, fun _ ↦ rfl⟩

theorem duplicatedTwo_strict (t : ℝ) (ht : 0 < t) :
    FSC.cdf (FSC.simplex 2) t < FSC.cdf duplicatedTwo t := by
  apply FSC.two_site_strict duplicatedTwo duplicatedTwo_corr _ t ht
  intro heq
  have hc := (FSC.two_eq_simplex_iff duplicatedTwo duplicatedTwo_corr).mp heq
  norm_num [duplicatedTwo] at hc

def antipodalRepeatedColumn : Matrix (Fin 3) (Fin 1) ℝ := fun i _ ↦ (![1, -1, 1] : Fin 3 → ℝ) i

def antipodalRepeated : FSC.Mat 3 := antipodalRepeatedColumn * antipodalRepeatedColumn.transpose

theorem antipodalRepeated_corr : WeakSimplex.IsCorrelation antipodalRepeated := by
  constructor
  · simpa only [Matrix.mul_one, antipodalRepeated] using FSC.posSemidef_congruence (1 : FSC.Mat 1)
      Matrix.PosSemidef.one antipodalRepeatedColumn
  · intro i
    fin_cases i <;> norm_num [antipodalRepeated, antipodalRepeatedColumn, Matrix.mul_apply]

theorem antipodalRepeated_not_simplex : antipodalRepeated ≠ FSC.simplex 3 := by
  intro heq
  have h := congrFun (congrFun heq 0) 2
  norm_num [antipodalRepeated, antipodalRepeatedColumn, Matrix.mul_apply,
    FSC.simplex_apply (by norm_num : 2 ≤ 3)] at h
  change (1 : ℝ) = -(1 / 2) at h
  linarith

/-- Equality at every nonpositive threshold can occur at a nonsimplex correlation. -/
theorem antipodalRepeated_cdf_nonpos (t : ℝ) (ht : t ≤ 0) : FSC.cdf antipodalRepeated t = 0 := by
  have hlaw : Measure.map (FSC.lin antipodalRepeatedColumn) (stdGaussian (FSC.Coord 1)) =
      multivariateGaussian (0 : FSC.Coord 3) antipodalRepeated := by
    simpa only [map_zero, Matrix.mul_one, multivariateGaussian_zero_one, antipodalRepeated] using
      FSC.map_lin_multivariateGaussian (0 : FSC.Coord 1) (1 : FSC.Mat 1)
        Matrix.PosSemidef.one antipodalRepeatedColumn
  have hnull : stdGaussian (FSC.Coord 1) {z : FSC.Coord 1 | z 0 = 0} = 0 := by
    simpa only [multivariateGaussian_zero_one] using
      FSC.gaussian_coordinate_hyperplane_null (0 : FSC.Coord 1) (1 : FSC.Mat 1)
        Matrix.PosSemidef.one 0 (by norm_num) 0
  unfold FSC.cdf
  rw [← hlaw, Measure.map_apply (FSC.lin antipodalRepeatedColumn).measurable
    (WeakSimplex.measurableSet_lowerOrthant t)]
  have hsub : (FSC.lin antipodalRepeatedColumn) ⁻¹' WeakSimplex.lowerOrthant t ⊆
      {z : FSC.Coord 1 | z 0 = 0} := by
    intro z hz
    have h0 := hz 0
    have h1 := hz 1
    simp [FSC.lin_apply, antipodalRepeatedColumn, Matrix.mulVec, dotProduct] at h0 h1
    change z 0 = 0
    linarith
  rw [measure_mono_null hsub hnull, ENNReal.toReal_zero]

theorem nonpositive_equality_without_simplex (t : ℝ) (ht : t ≤ 0) :
    FSC.cdf antipodalRepeated t = FSC.cdf (FSC.simplex 3) t ∧ antipodalRepeated ≠ FSC.simplex 3 := by
  rw [antipodalRepeated_cdf_nonpos t ht, FSC.simplex_cdf_nonpos (by norm_num) t ht]
  exact ⟨rfl, antipodalRepeated_not_simplex⟩

#print axioms FSCChecks.duplicatedTwo_corr
#print axioms FSCChecks.duplicatedTwo_strict
#print axioms FSCChecks.antipodalRepeated_corr
#print axioms FSCChecks.antipodalRepeated_not_simplex
#print axioms FSCChecks.antipodalRepeated_cdf_nonpos
#print axioms FSCChecks.nonpositive_equality_without_simplex

end FSCChecks
