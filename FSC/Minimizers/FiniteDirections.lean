import FSC.Scalar.RowLoss
import FSC.Gaussian.ThresholdExpansion
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Frozen finite rank-one feasible tests at a correlation minimizer. -/

noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace FSC

theorem stress_symm {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i j : Fin n) : stress G t i j = stress G t j i := by
  by_cases hij : i = j
  · subst j; rfl
  · simp only [stress, if_neg hij, if_neg (Ne.symm hij)]
    exact q_symm G hG i j t

theorem stress_row_sum {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) :
    ∑ j, stress G t i j = rowK G t i := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [stress, if_true]
  have heq : (∑ j ∈ Finset.univ.erase i,
      if i = j then -∑ k ∈ Finset.univ.erase i, G i k * q G t i k else q G t i j) =
      ∑ j ∈ Finset.univ.erase i, q G t i j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj).symm]
  rw [heq]
  simp only [rowK, sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

theorem stress_column_sum {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i : Fin n) : ∑ j, stress G t j i = rowK G t i := by
  simp_rw [stress_symm G hG t _ i]
  exact stress_row_sum G t i

theorem stress_sum {n : ℕ} (G : Mat n) (t : ℝ) :
    ∑ i, ∑ j, stress G t i j = kappa G t := by
  simp only [stress_row_sum, kappa]

theorem trace_stress_mul_allOnes {n : ℕ} (G : Mat n) (t : ℝ) :
    Matrix.trace (stress G t * Matrix.of (fun _ _ ↦ (1 : ℝ))) = kappa G t := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, mul_one, stress_sum]

theorem trace_stress_mul_self {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) : Matrix.trace (stress G t * G) = 0 := by
  classical
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_eq_zero
  intro i _
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [stress, if_true, hG.2 i, mul_one]
  have heq : (∑ j ∈ Finset.univ.erase i,
      (if i = j then -∑ k ∈ Finset.univ.erase i, G i k * q G t i k else q G t i j) * G j i) =
      ∑ j ∈ Finset.univ.erase i, G i j * q G t i j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj).symm]
    have hsym : G j i = G i j := by simpa using hG.1.isHermitian.apply i j
    rw [hsym, mul_comm]
  rw [heq]
  ring

theorem trace_mul_rankOne {n : ℕ} (S : Mat n) (z : Fin n → ℝ) :
    Matrix.trace (S * Matrix.vecMulVec z z) = z ⬝ᵥ (S *ᵥ z) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- The scalar in this vector is evaluated at the base matrix and stays fixed along the path. -/
def finiteTestVector {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) : Fin n → ℝ :=
  Pi.single i 1 - fun _ ↦ rowWeight G t i

theorem stress_constant_test {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t a : ℝ) (i : Fin n) :
    let z : Fin n → ℝ := Pi.single i 1 - fun _ ↦ a
    z ⬝ᵥ (stress G t *ᵥ z) =
      stress G t i i - 2 * a * rowK G t i + a ^ 2 * kappa G t := by
  change (Pi.single i 1 - fun _ ↦ a) ⬝ᵥ
    (stress G t *ᵥ (Pi.single i 1 - fun _ ↦ a)) = _
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
  simp only [single_dotProduct, one_mul, Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [Matrix.mulVec, dotProduct]
  change stress G t i i - (∑ j, a * stress G t j i) -
    ((∑ j, stress G t i j * a) - ∑ j, a * ∑ k, stress G t j k * a) = _
  simp only [← Finset.mul_sum, ← Finset.sum_mul, stress_column_sum G hG,
    stress_row_sum]
  change stress G t i i - a * rowK G t i - (rowK G t i * a - a * (kappa G t * a)) = _
  ring

theorem trace_stress_finiteTest {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i : Fin n) (hκ : kappa G t ≠ 0) :
    Matrix.trace (stress G t * Matrix.vecMulVec (finiteTestVector G t i) (finiteTestVector G t i)) =
      stress G t i i - rowK G t i ^ 2 / kappa G t := by
  rw [trace_mul_rankOne]
  unfold finiteTestVector
  rw [stress_constant_test G hG]
  unfold rowWeight
  field_simp
  ring

theorem rankOne_posSemidef {n : ℕ} (z : Fin n → ℝ) :
    (Matrix.vecMulVec z z).PosSemidef := by
  simpa only [Pi.star_apply, star_trivial] using Matrix.posSemidef_vecMulVec_self_star z

theorem right_derivative_nonneg_of_minimum {f : ℝ → ℝ} {d : ℝ}
    (hD : HasDerivWithinAt f d (Ici 0) 0) (hMin : ∀ s, 0 ≤ s → f 0 ≤ f s) : 0 ≤ d := by
  have hD' := hD.mono (Ioi_subset_Ici_self : Ioi (0 : ℝ) ⊆ Ici 0)
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp hD'
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [slope_def_field, sub_zero]
  exact div_nonneg (sub_nonneg.mpr (hMin s (le_of_lt hs))) (le_of_lt hs)

theorem half_trace_nonneg_of_minimum {n : ℕ} (G L : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (hL : L.PosSemidef)
    (t : ℝ) (ht : 0 < t)
    (hMin : ∀ H : Mat n, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t) :
    0 ≤ (1 / 2 : ℝ) * Matrix.trace (stress G t * L) := by
  apply right_derivative_nonneg_of_minimum (hasDerivWithinAt_normalizedAdd G L hG hd hL t ht)
  intro s hs
  simpa only [normalizedAdd_zero] using hMin (normalizedAdd G L s)
    (normalizedAdd_isCorrelation hG hL hs)

theorem trace_nonneg_of_minimum {n : ℕ} (G L : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (hL : L.PosSemidef)
    (t : ℝ) (ht : 0 < t)
    (hMin : ∀ H : Mat n, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t) :
    0 ≤ Matrix.trace (stress G t * L) := by
  have h := half_trace_nonneg_of_minimum G L hG hd hL t ht hMin
  linarith

/-- Exactly the n frozen rank-one tests, with the actual Gaussian variation discharged. -/
theorem finite_row_test_bound {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t)
    (hMin : ∀ H : Mat n, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t) (i : Fin n) :
    rowK G t i ^ 2 / kappa G t ≤ stress G t i i := by
  have h := trace_nonneg_of_minimum G
    (Matrix.vecMulVec (finiteTestVector G t i) (finiteTestVector G t i)) hG hd
    (rankOne_posSemidef _) t ht hMin
  rw [trace_stress_finiteTest G hG t i (kappa_pos hn G hG hd t ht).ne'] at h
  linarith

end FSC
