import FSC.Gaussian.ThresholdExpansion
import FSC.Simplex.Definitions
import FSC.Gaussian.CDFContinuity
import FSC.Gaussian.Replacement
import FSC.Minimizers.FiniteDirections
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Duplicate and positive-definite exclusions for actual positive-threshold global minima. -/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace MatrixOrder BigOperators

namespace FSC

theorem allOnes_le_smul_one {n : ℕ} (hn : 2 ≤ n) :
    WeakSimplex.allOnesMatrix n ≤ (n : ℝ) • (1 : Mat n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := (simplex_isCorrelation hn).1.smul (by linarith : 0 ≤ (n : ℝ) - 1)
  rw [simplex_eq_scaled_matrix hn, smul_smul,
    mul_one_div_cancel (by linarith : (n : ℝ) - 1 ≠ 0), one_smul] at hp
  exact hp

/-- A positive-definite matrix admits a genuine PSD subtraction in the all-ones direction. -/
theorem exists_pos_sub_allOnes_posSemidef {n : ℕ} (hn : 2 ≤ n) (G : Mat n)
    (hG : G.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ (G - δ • WeakSimplex.allOnesMatrix n).PosSemidef := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  obtain ⟨a, ha, hle⟩ := (CFC.exists_pos_algebraMap_le_iff hG.isStrictlyPositive.isSelfAdjoint).mpr
    (fun x hx ↦ hG.isStrictlyPositive.spectrum_pos hx)
  refine ⟨a / (n : ℝ), div_pos ha (by linarith), ?_⟩
  apply Matrix.le_iff.mp
  have hJ := smul_le_smul_of_nonneg_left (allOnes_le_smul_one hn)
    (div_nonneg ha.le (by positivity))
  have heq : (a / (n : ℝ)) • ((n : ℝ) • (1 : Mat n)) = algebraMap ℝ (Mat n) a := by
    rw [smul_smul, div_mul_cancel₀ a hn0, Algebra.algebraMap_eq_smul_one]
  rw [heq] at hJ
  exact hJ.trans hle

/-- A duplicate coordinate can be replaced by independent noise with strictly smaller CDF. -/
theorem exists_cdf_lt_of_duplicate {n : ℕ} (hn : 1 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i j : Fin n) (hij : i ≠ j) (hc : G i j = 1)
    (t : ℝ) (ht : 0 < t) :
    ∃ H : Mat n, WeakSimplex.IsCorrelation H ∧ cdf H t < cdf G t := by
  refine ⟨replacementCov G i, replacementCov_isCorrelation G hG i, ?_⟩
  rw [cdf_replacementCov_of_duplicate G hG i j hij hc t]
  exact mul_lt_of_lt_one_left (cdf_pos hn G hG t ht) (WeakSimplex.normalCDF_lt_one t)

/-- Positive-threshold global minimizers have no duplicate scores. -/
theorem distinctScores_of_cdf_minimum {n : ℕ} (hn : 1 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (t : ℝ) (ht : 0 < t)
    (hmin : ∀ H : Mat n, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t) : DistinctScores G := by
  intro i j hij
  have hle := (correlation_entry_bounds G hG i j).2
  by_contra h
  have hc : G i j = 1 := le_antisymm hle (le_of_not_gt h)
  obtain ⟨H, hH, hlt⟩ := exists_cdf_lt_of_duplicate hn G hG i j hij hc t ht
  exact (not_lt_of_ge (hmin H hH)) hlt

/-- The same normalized PSD-addition calculus excludes positive-definite minima. -/
theorem not_posDef_of_cdf_minimum {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (t : ℝ) (ht : 0 < t)
    (hmin : ∀ H : Mat n, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t) : ¬G.PosDef := by
  intro hpd
  have hd := distinctScores_of_cdf_minimum (by omega) G hG t ht hmin
  obtain ⟨δ, hδ, hL⟩ := exists_pos_sub_allOnes_posSemidef (by omega) G hpd
  have htrace := trace_nonneg_of_minimum G (G - δ • WeakSimplex.allOnesMatrix n)
    hG hd hL t ht hmin
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    trace_stress_mul_self G hG] at htrace
  have hJ : Matrix.trace (stress G t * WeakSimplex.allOnesMatrix n) = kappa G t :=
    trace_stress_mul_allOnes G t
  rw [hJ] at htrace
  have hκ := kappa_pos hn G hG hd t ht
  have hneg := mul_pos hδ hκ
  simp only [smul_eq_mul] at htrace
  linarith

theorem cdf_minimum_distinct_not_posDef {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (t : ℝ) (ht : 0 < t)
    (hmin : ∀ H : Mat n, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t) :
    DistinctScores G ∧ ¬G.PosDef :=
  ⟨distinctScores_of_cdf_minimum (by omega) G hG t ht hmin,
    not_posDef_of_cdf_minimum hn G hG t ht hmin⟩

end FSC
