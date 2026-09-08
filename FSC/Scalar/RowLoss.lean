import FSC.Gaussian.PairWeights
import FSC.Simplex.Definitions
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Exact signed-row loss and canonical weighted Cauchy, preserving equality. -/

noncomputable section

open Matrix
open scoped BigOperators

namespace FSC

def rowWeight {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) : ℝ := rowK G t i / kappa G t

def rowRatio {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) : ℝ := rowC G t i / rowK G t i

def referenceRatio (n : ℕ) : ℝ := Real.sqrt (((n : ℝ) - 2) / n)

def rowX {n : ℕ} (G : Mat n) (t : ℝ) (i j : Fin n) : ℝ :=
  Real.sqrt ((1 - G i j) * q G t i j)

def rowY {n : ℕ} (G : Mat n) (t : ℝ) (i j : Fin n) : ℝ :=
  Real.sqrt ((1 + G i j) * q G t i j)

theorem rowX_sq {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i j : Fin n) : rowX G t i j ^ 2 = (1 - G i j) * q G t i j := by
  apply Real.sq_sqrt
  exact mul_nonneg (sub_nonneg.mpr (abs_le.mp (corr_entry_abs_le_one G hG i j)).2) (q_nonneg G t i j)

theorem rowY_sq {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i j : Fin n) : rowY G t i j ^ 2 = (1 + G i j) * q G t i j := by
  apply Real.sq_sqrt
  exact mul_nonneg (by linarith [(abs_le.mp (corr_entry_abs_le_one G hG i j)).1]) (q_nonneg G t i j)

theorem rowX_mul_rowY {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i j : Fin n) : rowX G t i j * rowY G t i j = pairSigma G i j * q G t i j := by
  have hb := abs_le.mp (corr_entry_abs_le_one G hG i j)
  have hx : 0 ≤ (1 - G i j) * q G t i j := mul_nonneg (by linarith) (q_nonneg G t i j)
  have hc : 0 ≤ 1 - G i j ^ 2 := by nlinarith [sq_nonneg (G i j)]
  unfold rowX rowY pairSigma
  rw [← Real.sqrt_mul hx]
  have heq : ((1 - G i j) * q G t i j) * ((1 + G i j) * q G t i j) =
      (1 - G i j ^ 2) * q G t i j ^ 2 := by ring
  rw [heq, Real.sqrt_mul hc, Real.sqrt_sq_eq_abs, abs_of_nonneg (q_nonneg G t i j)]

theorem sum_rowX_sq {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i : Fin n) : ∑ j ∈ Finset.univ.erase i, rowX G t i j ^ 2 = rowK G t i := by
  simp only [rowX_sq G hG, rowK]

theorem sum_rowY_sq {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, rowY G t i j ^ 2 = rowK G t i - 2 * stress G t i i := by
  simp only [rowY_sq G hG, rowK, stress, if_true, sub_mul, add_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

theorem sum_rowX_mul_rowY {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, rowX G t i j * rowY G t i j = rowC G t i := by
  simp only [rowX_mul_rowY G hG, rowC]

theorem row_cauchy {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i : Fin n) : rowC G t i ^ 2 ≤ rowK G t i * (rowK G t i - 2 * stress G t i i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i) (rowX G t i) (rowY G t i)
  simpa only [sum_rowX_sq G hG, sum_rowY_sq G hG, sum_rowX_mul_rowY G hG] using h

/-- The exact weighted Cauchy deficit retains each individual positive edge. -/
theorem row_cauchy_remainder {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i : Fin n) (hk : rowK G t i ≠ 0) :
    (∑ j ∈ Finset.univ.erase i, (rowY G t i j - rowRatio G t i * rowX G t i j) ^ 2) =
      rowK G t i - 2 * stress G t i i - rowC G t i ^ 2 / rowK G t i := by
  have heq (j : Fin n) : (rowY G t i j - rowRatio G t i * rowX G t i j) ^ 2 =
      rowY G t i j ^ 2 - (2 * rowRatio G t i) * (rowX G t i j * rowY G t i j) +
        rowRatio G t i ^ 2 * rowX G t i j ^ 2 := by ring
  simp_rw [heq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_rowX_sq G hG, sum_rowY_sq G hG, sum_rowX_mul_rowY G hG]
  unfold rowRatio
  field_simp
  ring

theorem referenceRatio_pos {n : ℕ} (hn : 3 ≤ n) : 0 < referenceRatio n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  apply Real.sqrt_pos.mpr
  exact div_pos (by linarith) (by linarith)

theorem referenceRatio_sq {n : ℕ} (hn : 3 ≤ n) :
    referenceRatio n ^ 2 = ((n : ℝ) - 2) / n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.sq_sqrt (div_nonneg (by linarith) (by positivity))

/-- The signed loss is exactly a covariance slack plus a square. -/
theorem signed_row_remainder (n A a R : ℝ) (hn : n ≠ 0) (hR : R ≠ 0)
    (hsq : R ^ 2 = (n - 2) / n) :
    (n - 2) * (1 - A / R) - (n * a - 1) =
      n / 2 * (1 - 2 * a - A ^ 2) + (n - 2) / 2 * (1 - A / R) ^ 2 := by
  have hcancel : ((n - 2) / n) * (A / R) ^ 2 = A ^ 2 := by
    rw [← hsq, div_pow]
    field_simp
  calc
    _ = n / 2 * (1 - 2 * a - ((n - 2) / n) * (A / R) ^ 2) +
        (n - 2) / 2 * (1 - A / R) ^ 2 := by
      field_simp [hn]
      ring
    _ = _ := by rw [hcancel]

theorem signed_row_le {n : ℕ} (hn : 3 ≤ n) (A a : ℝ) (hA : A ^ 2 ≤ 1 - 2 * a) :
    (n : ℝ) * a - 1 ≤ ((n : ℝ) - 2) * (1 - A / referenceRatio n) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hid := signed_row_remainder n A a (referenceRatio n) (by positivity)
    (referenceRatio_pos hn).ne' (referenceRatio_sq hn)
  have hfirst : 0 ≤ (n : ℝ) / 2 * (1 - 2 * a - A ^ 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hA)
  have hsecond : 0 ≤ ((n : ℝ) - 2) / 2 * (1 - A / referenceRatio n) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  linarith

theorem signed_row_equality {n : ℕ} (hn : 3 ≤ n) (A a : ℝ) (hA : A ^ 2 ≤ 1 - 2 * a) :
    ((n : ℝ) - 2) * (1 - A / referenceRatio n) = (n : ℝ) * a - 1 ↔
      A = referenceRatio n ∧ a = 1 / n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hR := referenceRatio_pos hn
  constructor
  · intro heq
    have hid := signed_row_remainder n A a (referenceRatio n) hn0 hR.ne' (referenceRatio_sq hn)
    have hfirst : 0 ≤ (n : ℝ) / 2 * (1 - 2 * a - A ^ 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hA)
    have hz : (1 - A / referenceRatio n) ^ 2 = 0 := by nlinarith [sq_nonneg (1 - A / referenceRatio n)]
    have hr : A / referenceRatio n = 1 := by nlinarith
    have hAr : A = referenceRatio n := (div_eq_one_iff_eq hR.ne').mp hr
    refine ⟨hAr, ?_⟩
    rw [hr, sub_self, mul_zero] at heq
    apply (eq_div_iff hn0).mpr
    nlinarith
  · rintro ⟨rfl, rfl⟩
    simp [hR.ne', hn0]

theorem rowWeight_pos {n : ℕ} (hn : 3 ≤ n) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hd : DistinctScores G) (t : ℝ) (ht : 0 < t) (i : Fin n) : 0 < rowWeight G t i :=
  div_pos (rowK_pos hn G hG hd t ht i) (kappa_pos hn G hG hd t ht)

theorem sum_rowWeight {n : ℕ} (G : Mat n) (t : ℝ) (hκ : kappa G t ≠ 0) :
    ∑ i, rowWeight G t i = 1 := by
  simp only [rowWeight, ← Finset.sum_div]
  exact div_self hκ

theorem rowRatio_pos {n : ℕ} (hn : 3 ≤ n) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hd : DistinctScores G) (t : ℝ) (ht : 0 < t) (i : Fin n) : 0 < rowRatio G t i :=
  div_pos (rowC_pos hn G hG hd t ht i) (rowK_pos hn G hG hd t ht i)

theorem rowRatio_sq_le {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i : Fin n) (hk : 0 < rowK G t i)
    (hTest : rowK G t i ^ 2 / kappa G t ≤ stress G t i i) :
    rowRatio G t i ^ 2 ≤ 1 - 2 * rowWeight G t i := by
  have htest : rowK G t i * rowWeight G t i ≤ stress G t i i := by
    simpa only [rowWeight, sq, mul_div_assoc] using hTest
  have hm := mul_le_mul_of_nonneg_left htest hk.le
  have hc := row_cauchy G hG t i
  unfold rowRatio
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hk)]
  nlinarith

theorem rowWeight_lt_half {n : ℕ} (hn : 3 ≤ n) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hd : DistinctScores G) (t : ℝ) (ht : 0 < t) (i : Fin n)
    (hTest : rowK G t i ^ 2 / kappa G t ≤ stress G t i i) : rowWeight G t i < 1 / 2 := by
  have hbound := rowRatio_sq_le G hG t i (rowK_pos hn G hG hd t ht i) hTest
  have hp := rowRatio_pos hn G hG hd t ht i
  nlinarith

theorem canonical_signed_row_le {n : ℕ} (hn : 3 ≤ n) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hd : DistinctScores G) (t : ℝ) (ht : 0 < t) (i : Fin n)
    (hTest : rowK G t i ^ 2 / kappa G t ≤ stress G t i i) :
    (n : ℝ) * rowWeight G t i - 1 ≤ ((n : ℝ) - 2) * (1 - rowRatio G t i / referenceRatio n) :=
  signed_row_le hn _ _ (rowRatio_sq_le G hG t i (rowK_pos hn G hG hd t ht i) hTest)

/-- Equality in weighted Cauchy determines every edge with positive canonical weight. -/
theorem positive_edge_of_row_cauchy_eq {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i j : Fin n) (hji : j ≠ i) (hk : rowK G t i ≠ 0) (hq : 0 < q G t i j)
    (hEq : rowC G t i ^ 2 = rowK G t i * (rowK G t i - 2 * stress G t i i)) :
    G i j = (rowRatio G t i ^ 2 - 1) / (rowRatio G t i ^ 2 + 1) := by
  have hsum : (∑ j ∈ Finset.univ.erase i,
      (rowY G t i j - rowRatio G t i * rowX G t i j) ^ 2) = 0 := by
    rw [row_cauchy_remainder G hG t i hk, hEq]
    field_simp
    ring
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg
    (rowY G t i j - rowRatio G t i * rowX G t i j))).mp hsum j
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  have hY : rowY G t i j = rowRatio G t i * rowX G t i j := by nlinarith
  have hs := congrArg (fun x : ℝ ↦ x ^ 2) hY
  rw [rowY_sq G hG, mul_pow, rowX_sq G hG] at hs
  have hg : 1 + G i j = rowRatio G t i ^ 2 * (1 - G i j) := by
    apply mul_right_cancel₀ hq.ne'
    nlinarith only [hs]
  apply (eq_div_iff (by positivity : rowRatio G t i ^ 2 + 1 ≠ 0)).mpr
  nlinarith only [hg]

theorem row_cauchy_eq_of_ratio_saturation {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (i : Fin n) (hk : 0 < rowK G t i)
    (hTest : rowK G t i ^ 2 / kappa G t ≤ stress G t i i)
    (hsat : rowRatio G t i ^ 2 = 1 - 2 * rowWeight G t i) :
    rowC G t i ^ 2 = rowK G t i * (rowK G t i - 2 * stress G t i i) := by
  have htest : rowK G t i * rowWeight G t i ≤ stress G t i i := by
    simpa only [rowWeight, sq, mul_div_assoc] using hTest
  have hm := mul_le_mul_of_nonneg_left htest hk.le
  have hc := row_cauchy G hG t i
  unfold rowRatio at hsat
  rw [div_pow, div_eq_iff (ne_of_gt (sq_pos_of_pos hk))] at hsat
  nlinarith

theorem positive_edge_simplex_of_uniform {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (t : ℝ) (i j : Fin n) (hji : j ≠ i)
    (hk : 0 < rowK G t i) (hq : 0 < q G t i j)
    (hTest : rowK G t i ^ 2 / kappa G t ≤ stress G t i i)
    (ha : rowWeight G t i = 1 / n) (hA : rowRatio G t i = referenceRatio n) :
    G i j = -1 / ((n : ℝ) - 1) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hsat : rowRatio G t i ^ 2 = 1 - 2 * rowWeight G t i := by
    rw [hA, referenceRatio_sq hn, ha]
    field_simp
  rw [positive_edge_of_row_cauchy_eq G hG t i j hji hk.ne' hq
    (row_cauchy_eq_of_ratio_saturation G hG t i hk hTest hsat), hA, referenceRatio_sq hn]
  have hsum : ((n : ℝ) - 2) / n + 1 ≠ 0 := by
    have hp : 0 < ((n : ℝ) - 2) / n := div_pos (by linarith) (by positivity)
    linarith
  apply (div_eq_div_iff hsum hn1).mpr
  field_simp
  ring

/-- PSD forces equality when every off-diagonal entry is no larger than the simplex entry. -/
theorem correlation_eq_simplex_of_offdiag_le {n : ℕ} (hn : 2 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G)
    (hoff : ∀ i j : Fin n, i ≠ j → G i j ≤ -1 / ((n : ℝ) - 1)) : G = simplex n := by
  have hentry (i j : Fin n) : G i j ≤ simplex n i j := by
    by_cases hij : i = j
    · subst j
      rw [hG.2 i, (simplex_isCorrelation hn).2 i]
    · rw [simplex_apply hn, if_neg hij]
      exact hoff i j hij
  have hpos : 0 ≤ ∑ i, ∑ j, G i j := by
    simpa [dotProduct, Matrix.mulVec] using hG.1.dotProduct_mulVec_nonneg (fun _ ↦ 1)
  have hsum : (∑ i, ∑ j, G i j) = ∑ i, ∑ j, simplex n i j := by
    apply le_antisymm (Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hentry i j)))
    simpa only [simplex_sum_row hn, Finset.sum_const_zero] using hpos
  have hrow := (Finset.sum_eq_sum_iff_of_le
    (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hentry i j))).mp hsum
  ext i j
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ hentry i j)).mp
    (hrow i (Finset.mem_univ i)) j (Finset.mem_univ j)

theorem correlation_eq_simplex_of_positive_edges {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t)
    (hedge : ∀ i j : Fin n, i ≠ j → 0 < q G t i j → G i j = -1 / ((n : ℝ) - 1)) :
    G = simplex n := by
  apply correlation_eq_simplex_of_offdiag_le (by omega) G hG
  intro i j hij
  obtain ⟨k, hki, hlo, hmax⟩ := exists_row_max_nonantipodal hn G hG hd i
  have hq := q_pos_of_row_max G hG hd t ht i k hki.symm hlo hmax
  exact (hmax j hij.symm).trans (hedge i k hki.symm hq).le

theorem correlation_eq_simplex_of_uniform_rows {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t)
    (hTest : ∀ i, rowK G t i ^ 2 / kappa G t ≤ stress G t i i)
    (ha : ∀ i, rowWeight G t i = 1 / n) (hA : ∀ i, rowRatio G t i = referenceRatio n) :
    G = simplex n := by
  apply correlation_eq_simplex_of_positive_edges hn G hG hd t ht
  intro i j hij hq
  exact positive_edge_simplex_of_uniform hn G hG t i j hij.symm
    (rowK_pos hn G hG hd t ht i) hq (hTest i) (ha i) (hA i)

end FSC
