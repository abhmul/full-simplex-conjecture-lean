import FSC.Gaussian.SinglePin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace FSCChecks

/-- Duplicated scores remain within the canonical one-pin interface. -/
theorem duplicateCorrelation : WeakSimplex.IsCorrelation (fun _ _ : Fin 2 ↦ (1 : ℝ)) := by
  constructor
  · have hm : Matrix.vecMulVec (fun _ : Fin 2 ↦ (1 : ℝ))
        (star (fun _ : Fin 2 ↦ (1 : ℝ))) = (fun _ _ : Fin 2 ↦ (1 : ℝ)) := by
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [← hm]
    exact Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 2 ↦ (1 : ℝ))
  · intro i
    rfl

theorem duplicateSingleLaw (t : ℝ) :
    FSC.singleLaw (fun _ _ : Fin 2 ↦ (1 : ℝ)) 0 t =
      Measure.dirac (WeakSimplex.Coord.ofFun fun _ : Fin 2 ↦ t) := by
  have hc : FSC.singleCov (fun _ _ : Fin 2 ↦ (1 : ℝ)) 0 = 0 := by
    ext k l
    simp [FSC.singleCov]
  rw [FSC.singleLaw, hc, FSC.multivariateGaussian_zero_cov]
  simp [FSC.singleMean]

/-- The antipodal rank-one Gram matrix also has a deterministic residual. -/
theorem antipodalCorrelation : WeakSimplex.IsCorrelation
    (Matrix.vecMulVec (![1, -1] : Fin 2 → ℝ) ![1, -1]) := by
  constructor
  · simpa only [Pi.star_apply, star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star (![1, -1] : Fin 2 → ℝ)
  · intro i
    fin_cases i <;> norm_num [Matrix.vecMulVec_apply]

theorem antipodalSingleLaw (t : ℝ) :
    FSC.singleLaw (Matrix.vecMulVec (![1, -1] : Fin 2 → ℝ) ![1, -1]) 0 t =
      Measure.dirac (WeakSimplex.Coord.ofFun ![t, -t]) := by
  have hc : FSC.singleCov
      (Matrix.vecMulVec (![1, -1] : Fin 2 → ℝ) ![1, -1]) 0 = 0 := by
    ext k l
    fin_cases k <;> fin_cases l <;> norm_num [FSC.singleCov, Matrix.vecMulVec_apply]
  rw [FSC.singleLaw, hc, FSC.multivariateGaussian_zero_cov]
  congr 1
  ext k
  fin_cases k <;> simp [FSC.singleMean, Matrix.vecMulVec_apply]

#print axioms FSCChecks.duplicateCorrelation
#print axioms FSCChecks.duplicateSingleLaw
#print axioms FSCChecks.antipodalCorrelation
#print axioms FSCChecks.antipodalSingleLaw

end FSCChecks
