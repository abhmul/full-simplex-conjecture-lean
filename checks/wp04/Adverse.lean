import FSC.Gaussian.PairWeights
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace FSCChecks

/-- Pinning both independent scores leaves a zero-dimensional residual, for all real pins. -/
theorem fullPairPinDirac (r s : ℝ) :
    FSC.pairLaw (1 : FSC.Mat 2) 0 1 r s =
      Measure.dirac (WeakSimplex.Coord.ofFun ![r, s]) := by
  have hres : FSC.pairResidual (1 : FSC.Mat 2) 0 1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [FSC.pairResidual, FSC.pairAlpha, FSC.pairBeta, Matrix.vecMulVec_apply,
        Matrix.one_apply]
  rw [FSC.pairLaw, FSC.pairCov, hres, Matrix.zero_mul, Matrix.zero_mul,
    FSC.multivariateGaussian_zero_cov]
  congr 1
  ext i
  fin_cases i <;> simp [FSC.pairMean, FSC.pairAlpha, FSC.pairBeta]

/-- The remaining event is vacuous when both of two scores are pinned. -/
theorem fullPairSuccess (t : ℝ) : FSC.pairSuccess (1 : FSC.Mat 2) 0 1 t = 1 := by
  have hev : FSC.pairEvent (0 : Fin 2) 1 t = Set.univ := by
    ext x
    simp only [FSC.pairEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro k hk0 hk1
    fin_cases k <;> contradiction
  rw [FSC.pairSuccess, fullPairPinDirac, hev]
  simp

/-- The total canonical definition assigns zero to duplicate and antipodal pairs. -/
theorem duplicatePairWeight (t : ℝ) : FSC.q (fun _ _ : Fin 2 ↦ 1) t 0 1 = 0 := by
  simp [FSC.q]

theorem antipodalPairWeight (t : ℝ) :
    FSC.q (Matrix.vecMulVec (![1, -1] : Fin 2 → ℝ) ![1, -1]) t 0 1 = 0 := by
  norm_num [FSC.q, Matrix.vecMulVec_apply]

/-- The n≥3 restriction in row positivity cannot be removed: the antipodal two-score row is zero. -/
theorem antipodalTwoRowZero (t : ℝ) :
    FSC.rowK (Matrix.vecMulVec (![1, -1] : Fin 2 → ℝ) ![1, -1]) t 0 = 0 := by
  simp [FSC.rowK, Fin.sum_univ_two, FSC.q, Matrix.vecMulVec_apply]

#print axioms FSCChecks.fullPairPinDirac
#print axioms FSCChecks.fullPairSuccess
#print axioms FSCChecks.duplicatePairWeight
#print axioms FSCChecks.antipodalPairWeight
#print axioms FSCChecks.antipodalTwoRowZero

end FSCChecks
