import FSC.Equality
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section

open Matrix

namespace FSCChecks.WP23

theorem identity_corr : WeakSimplex.IsCorrelation (1 : FSC.Mat 3) :=
  ⟨Matrix.PosSemidef.one, fun i ↦ Matrix.one_apply_eq i⟩

theorem identity_not_simplex : (1 : FSC.Mat 3) ≠ FSC.simplex 3 := by
  intro h
  have he := congrFun (congrFun h 0) 1
  rw [FSC.simplex_apply (by omega)] at he
  norm_num at he

def signedGram : FSC.Mat 3 := Matrix.vecMulVec (![1, -1, 1] : Fin 3 → ℝ) ![1, -1, 1]

theorem signedGram_corr : WeakSimplex.IsCorrelation signedGram := by
  constructor
  · simpa only [signedGram, Pi.star_apply, star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star (![1, -1, 1] : Fin 3 → ℝ)
  · intro i
    fin_cases i <;> norm_num [signedGram, Matrix.vecMulVec_apply]

theorem signedGram_not_simplex : signedGram ≠ FSC.simplex 3 := by
  intro h
  have he := congrFun (congrFun h 0) 2
  rw [FSC.simplex_apply (by omega)] at he
  norm_num [signedGram, Matrix.vecMulVec_apply] at he
  change (1 : ℝ) = -(1 / 2) at he
  linarith

def squareRows : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; 0, 1; -1, 0; 0, -1]

def squareGram : FSC.Mat 4 := squareRows * squareRows.transpose

theorem squareGram_corr : WeakSimplex.IsCorrelation squareGram := by
  constructor
  · simpa only [Matrix.mul_one, squareGram] using
      FSC.posSemidef_congruence (1 : FSC.Mat 2) Matrix.PosSemidef.one squareRows
  · intro i
    fin_cases i <;> norm_num [squareGram, squareRows, Matrix.mul_apply, Fin.sum_univ_two]

theorem squareGram_not_simplex : squareGram ≠ FSC.simplex 4 := by
  intro h
  have he := congrFun (congrFun h 0) 1
  rw [FSC.simplex_apply (by omega)] at he
  norm_num [squareGram, squareRows, Matrix.mul_apply, Fin.sum_univ_two] at he

/-- Full-rank competitors are covered by the closed public theorem. -/
theorem identity_strict (t : ℝ) (ht : 0 < t) :
    FSC.cdf (FSC.simplex 3) t < FSC.cdf (1 : FSC.Mat 3) t :=
  FSC.cdf_simplex_lt (by omega) _ identity_corr t ht identity_not_simplex

/-- This rank-one competitor contains both duplicates and antipodes. -/
theorem signedGram_strict (t : ℝ) (ht : 0 < t) :
    FSC.cdf (FSC.simplex 3) t < FSC.cdf signedGram t :=
  FSC.cdf_simplex_lt (by omega) _ signedGram_corr t ht signedGram_not_simplex

/-- The singular square competitor has antipodal pairs and unused padded directions. -/
theorem squareGram_strict (t : ℝ) (ht : 0 < t) :
    FSC.cdf (FSC.simplex 4) t < FSC.cdf squareGram t :=
  FSC.cdf_simplex_lt (by omega) _ squareGram_corr t ht squareGram_not_simplex

theorem simplex_equality {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) :
    FSC.cdf (FSC.simplex n) t = FSC.cdf (FSC.simplex n) t :=
  (FSC.cdf_eq_simplex_iff hn _ (FSC.simplex_isCorrelation hn) t ht).mpr rfl

/-- The public iff includes the antipodal two-site base law. -/
theorem two_site_public_equality (G : FSC.Mat 2) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (ht : 0 < t) :
    FSC.cdf G t = FSC.cdf (FSC.simplex 2) t ↔ G 0 1 = -1 := by
  rw [FSC.cdf_eq_simplex_iff (by omega) G hG t ht, FSC.two_eq_simplex_iff G hG]

end FSCChecks.WP23

#print axioms FSCChecks.WP23.identity_strict
#print axioms FSCChecks.WP23.signedGram_strict
#print axioms FSCChecks.WP23.squareGram_strict
#print axioms FSCChecks.WP23.simplex_equality
#print axioms FSCChecks.WP23.two_site_public_equality
