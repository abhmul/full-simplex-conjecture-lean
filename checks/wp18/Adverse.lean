import FSC.Minimizers.Exclusions
import Mathlib.Tactic.FinCases

noncomputable section
open MeasureTheory ProbabilityTheory
namespace FSCProbes.MinimizerExclusions
open FSC

def duplicate : Mat 2 := fun _ _ ↦ 1

theorem duplicate_correlation : WeakSimplex.IsCorrelation duplicate := by
  refine ⟨?_, fun _ ↦ rfl⟩
  convert! Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 2 ↦ (1 : ℝ)) using 1
  ext i j
  simp [duplicate, Matrix.vecMulVec_apply]

theorem replace_duplicate_iid : replacementCov duplicate 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [replacementCov, eraseCoordinate, keepCoordinate, Matrix.diagonal_mul,
      Matrix.mul_diagonal, duplicate]

theorem replacement_actual_iid_cdf (t : ℝ) :
    cdf (replacementCov duplicate 0) t = WeakSimplex.normalCDF t ^ 2 := by
  have he : singleEvent (0 : Fin 2) t = {x : Coord 2 | x 1 ≤ t} := by
    ext x
    constructor
    · intro hx
      exact hx 1 (by decide)
    · intro hx k hk
      fin_cases k
      · exact False.elim (hk rfl)
      · exact hx
  rw [cdf_replacementCov duplicate duplicate_correlation, he,
    gaussian_coordinate_le_toReal duplicate duplicate_correlation]
  ring

theorem positive_identity_not_minimum (t : ℝ) (ht : 0 < t) :
    ¬(∀ H : Mat 3, WeakSimplex.IsCorrelation H → cdf (1 : Mat 3) t ≤ cdf H t) := by
  intro hmin
  exact not_posDef_of_cdf_minimum (by norm_num) (1 : Mat 3)
    ⟨Matrix.PosSemidef.one, fun i ↦ Matrix.one_apply_eq i⟩ t ht hmin Matrix.PosDef.one

theorem positive_duplicate_not_minimum (t : ℝ) (ht : 0 < t) :
    ¬(∀ H : Mat 2, WeakSimplex.IsCorrelation H → cdf duplicate t ≤ cdf H t) := by
  intro hmin
  have hd := distinctScores_of_cdf_minimum (by norm_num) duplicate duplicate_correlation t ht hmin
  have h := hd 0 1 (by decide)
  norm_num [duplicate] at h

end FSCProbes.MinimizerExclusions

#print axioms FSCProbes.MinimizerExclusions.replace_duplicate_iid
#print axioms FSCProbes.MinimizerExclusions.replacement_actual_iid_cdf
#print axioms FSCProbes.MinimizerExclusions.positive_identity_not_minimum
#print axioms FSCProbes.MinimizerExclusions.positive_duplicate_not_minimum
