import FSC.Facet.Compatibility
import FSC.Support.QuadraticTangent
import FSC.Scalar.Componentwise
import FSC.Scalar.RowLoss
import FSC.Simplex.Recursion
import FSC.Gaussian.CDFContinuity

/-! Actual conditional geometry, scalar mass comparison and boundary rigidity.
Source: reviewed DOSSIER section 2 and CORE_PROOF sections 1-4. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace FSC

theorem retainedPair_nonempty {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (i : Fin n) :
    Nonempty (RetainedPair G i) := by
  obtain ⟨j, hji, hlo, _⟩ := exists_row_max_nonantipodal hn G hG hd i
  exact ⟨⟨j, hji, hlo, hd i j hji.symm⟩⟩

theorem card_retainedPair_le {n : ℕ} (G : Mat n) (i : Fin n) :
    Fintype.card (RetainedPair G i) ≤ n - 1 := by
  have h := Fintype.card_subtype_lt (p := fun j ↦ j ≠ i ∧ -1 < G i j ∧ G i j < 1)
    (x := i) (by simp)
  simpa only [Fintype.card_fin] using Nat.le_sub_one_of_lt h

theorem reference_threshold_eq (n : ℕ) (t : ℝ) :
    t / referenceRatio n = t * Real.sqrt ((n : ℝ) / ((n : ℝ) - 2)) := by
  rw [div_eq_mul_inv, referenceRatio, ← Real.sqrt_inv, inv_div]

theorem projected_reference_floor {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (i : Fin n) (r : ℝ)
    (hcompare : ∀ H : Mat (n - 1), WeakSimplex.IsCorrelation H →
      cdf (simplex (n - 1)) r ≤ cdf H r) :
    cdf (simplex (n - 1)) r ≤ capMass (projectedNormal G i) (fun _ ↦ r) := by
  letI := retainedPair_nonempty hn G hG hd i
  exact reference_floor_of_comparison _ (norm_projectedNormal G hG i)
    (card_retainedPair_le G i) r hcompare

theorem canonical_quadratic_support {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G)
    (t : ℝ) (ht : 0 < t) (i : Fin n) (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hfloor : p ≤ capMass (projectedNormal G i) (fun _ ↦ r)) :
    (t * rowK G t i - r * rowC G t i) / WeakSimplex.normalPDF t ≤
      singlePinMass G t i ^ 2 / p - singlePinMass G t i := by
  have htan := quadratic_support_tangent (projectedNormal G i) (norm_projectedNormal G hG i)
    (fun j ↦ pairSupport G t i j) (fun _ ↦ r)
    (retained_support_pos G i t ht) (fun _ ↦ hr) (noCoincident_projectedNormals G hG hd i t ht)
  have hs := supportGradient_projected_reference G hG hd i t ht r
  have he : ((fun j : RetainedPair G i ↦ pairSupport G t i j) -
      (fun _ : RetainedPair G i ↦ r)) =
      -(fun j : RetainedPair G i ↦ r - pairSupport G t i j) := by ext j; simp
  rw [he, map_neg, hs, capMass_projected_common G hG hd i t ht] at htan
  calc
    _ = -(r * rowC G t i - t * rowK G t i) / WeakSimplex.normalPDF t := by ring
    _ ≤ singlePinMass G t i ^ 2 / capMass (projectedNormal G i) (fun _ ↦ r) -
        singlePinMass G t i := by simpa only [neg_div] using htan
    _ ≤ _ := sub_le_sub_right (div_le_div_of_nonneg_left (sq_nonneg _) hp hfloor) _

theorem pressure_signed_identity {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (t : ℝ) (i : Fin n) (hk : rowK G t i ≠ 0) :
    (t * rowK G t i - (t / referenceRatio n) * rowC G t i) / WeakSimplex.normalPDF t =
      facetPressure G t i * ((n : ℝ) - 2) * (1 - rowRatio G t i / referenceRatio n) := by
  unfold facetPressure rowRatio
  rw [cast_facetDimension (by omega)]
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  field_simp [hk, (referenceRatio_pos hn).ne', (WeakSimplex.normalPDF_pos t).ne',
    (show (n : ℝ) - 2 ≠ 0 by linarith)]

theorem canonical_support_signed {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t)
    (i : Fin n) (p : ℝ) (hp : 0 < p)
    (hfloor : p ≤ capMass (projectedNormal G i) (fun _ ↦ t / referenceRatio n))
    (hTest : rowK G t i ^ 2 / kappa G t ≤ stress G t i i) :
    facetPressure G t i * ((n : ℝ) * rowWeight G t i - 1) ≤
      singlePinMass G t i ^ 2 / p - singlePinMass G t i := by
  have hs := canonical_quadratic_support G hG hd t ht i (t / referenceRatio n) p
    (div_pos ht (referenceRatio_pos hn)) hp hfloor
  rw [pressure_signed_identity hn G t i (rowK_pos hn G hG hd t ht i).ne'] at hs
  have hb := mul_le_mul_of_nonneg_left
    (canonical_signed_row_le hn G hG hd t ht i hTest)
    (facetPressure_pos hn G hG hd t ht i).le
  apply le_trans ?_ hs
  simpa only [mul_assoc] using hb

theorem quadratic_component_from_signed (N p u e U : ℝ)
    (hN : 0 < N) (hp : 0 < p) (hU : 0 < U)
    (h : u * (N * (u / U) - 1) ≤ (u + e) ^ 2 / p - (u + e)) :
    (1 / N) * e ≤ (u + e) ^ 2 / (N * p) - u ^ 2 / U := by
  apply (mul_le_mul_iff_right₀ hN).mp
  have he : N * ((u + e) ^ 2 / (N * p) - u ^ 2 / U) =
      (u + e) ^ 2 / p - N * u ^ 2 / U := by
    field_simp [hN.ne', hp.ne', hU.ne']
  have heL : N * ((1 / N) * e) = e := by field_simp
  rw [heL, he]
  have hh : u * (N * (u / U) - 1) = N * u ^ 2 / U - u := by ring
  rw [hh] at h
  linarith

/-- This remainder is strictly positive because it is the physical padded cap energy. -/
def facetRemainder {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) : ℝ :=
  singlePinMass G t i - facetPressure G t i

theorem facetRemainder_pos {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (hnotPD : ¬G.PosDef)
    (t : ℝ) (ht : 0 < t) (i : Fin n) : 0 < facetRemainder G t i :=
  singlePinMass_sub_pressure_pos hn G hG hd hnotPD t ht i

@[simp] theorem pressure_add_remainder {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) :
    facetPressure G t i + facetRemainder G t i = singlePinMass G t i := by
  simp [facetRemainder]

theorem canonical_componentwise_inequality {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t)
    (i : Fin n) (p : ℝ) (hp : 0 < p)
    (hfloor : p ≤ capMass (projectedNormal G i) (fun _ ↦ t / referenceRatio n))
    (hTest : rowK G t i ^ 2 / kappa G t ≤ stress G t i i) :
    (1 / (n : ℝ)) * facetRemainder G t i ≤
      (facetPressure G t i + facetRemainder G t i) ^ 2 / ((n : ℝ) * p) -
        facetPressure G t i ^ 2 / (∑ j, facetPressure G t j) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hU : 0 < ∑ j, facetPressure G t j :=
    Finset.sum_pos (fun j _ ↦ facetPressure_pos hn G hG hd t ht j) Finset.univ_nonempty
  apply quadratic_component_from_signed _ _ _ _ _ hnR hp hU
  rw [pressure_add_remainder, normalized_facetPressure hn G t ht i]
  exact canonical_support_signed hn G hG hd t ht i p hp hfloor hTest

theorem reference_mass_pos {n : ℕ} (hn : 3 ≤ n) (t : ℝ) (ht : 0 < t) :
    0 < cdf (simplex (n - 1)) (t / referenceRatio n) :=
  cdf_pos (by omega) _ (simplex_isCorrelation (by omega)) _
    (div_pos ht (referenceRatio_pos hn))

theorem simplex_boundarySlope_recursion {n : ℕ} (hn : 3 ≤ n) (t : ℝ) (ht : 0 < t) :
    boundarySlope (simplex n) t =
      (n : ℝ) * WeakSimplex.normalPDF t * cdf (simplex (n - 1)) (t / referenceRatio n) := by
  rw [reference_threshold_eq]
  exact (hasDerivAt_cdf _ (simplex_isCorrelation (by omega)) (simplex_distinct (by omega)) t ht).unique
    (hasDerivAt_simplex_cdf hn t ht)

/-- Scalar comparison applied to actual one-pin masses and their physical energy remainder. -/
theorem sum_singlePinMass_ge_reference {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (hnotPD : ¬G.PosDef)
    (t : ℝ) (ht : 0 < t)
    (hTest : ∀ i, rowK G t i ^ 2 / kappa G t ≤ stress G t i i)
    (hcompare : ∀ H : Mat (n - 1), WeakSimplex.IsCorrelation H →
      cdf (simplex (n - 1)) (t / referenceRatio n) ≤ cdf H (t / referenceRatio n)) :
    (n : ℝ) * cdf (simplex (n - 1)) (t / referenceRatio n) ≤ ∑ i, singlePinMass G t i := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp := reference_mass_pos hn t ht
  have h := componentwise_compare (facetPressure G t) (facetRemainder G t)
    (fun _ ↦ 1 / (n : ℝ)) ((n : ℝ) * cdf (simplex (n - 1)) (t / referenceRatio n))
    (facetPressure_pos hn G hG hd t ht) (facetRemainder_pos hn G hG hd hnotPD t ht)
    (fun _ ↦ div_pos zero_lt_one hnR) (mul_pos hnR hp)
    (by simp [hnR.ne']) (fun i ↦ canonical_componentwise_inequality hn G hG hd t ht i _
      hp (projected_reference_floor hn G hG hd i _ hcompare) (hTest i))
  simpa only [pressure_add_remainder] using h

theorem boundarySlope_simplex_le_of_tests {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (hnotPD : ¬G.PosDef)
    (t : ℝ) (ht : 0 < t)
    (hTest : ∀ i, rowK G t i ^ 2 / kappa G t ≤ stress G t i i)
    (hcompare : ∀ H : Mat (n - 1), WeakSimplex.IsCorrelation H →
      cdf (simplex (n - 1)) (t / referenceRatio n) ≤ cdf H (t / referenceRatio n)) :
    boundarySlope (simplex n) t ≤ boundarySlope G t := by
  rw [simplex_boundarySlope_recursion hn t ht, boundarySlope]
  have h := mul_le_mul_of_nonneg_left
    (sum_singlePinMass_ge_reference hn G hG hd hnotPD t ht hTest hcompare)
    (WeakSimplex.normalPDF_pos t).le
  simpa only [mul_left_comm, mul_assoc] using h

theorem singlePinMass_uniform_of_sum_eq {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (hnotPD : ¬G.PosDef)
    (t : ℝ) (ht : 0 < t) (p : ℝ) (hp : 0 < p)
    (hTest : ∀ i, rowK G t i ^ 2 / kappa G t ≤ stress G t i i)
    (hfloor : ∀ i, p ≤ capMass (projectedNormal G i) (fun _ ↦ t / referenceRatio n))
    (heq : ∑ i, singlePinMass G t i = (n : ℝ) * p) :
    ∀ i, rowWeight G t i = 1 / n ∧ singlePinMass G t i = p := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := componentwise_equality (facetPressure G t) (facetRemainder G t)
    (fun _ ↦ 1 / (n : ℝ)) ((n : ℝ) * p)
    (facetPressure_pos hn G hG hd t ht) (facetRemainder_pos hn G hG hd hnotPD t ht)
    (fun _ ↦ div_pos zero_lt_one hnR) (mul_pos hnR hp)
    (by simp [hnR.ne']) (fun i ↦ canonical_componentwise_inequality hn G hG hd t ht i _
      hp (hfloor i) (hTest i)) (by simpa only [pressure_add_remainder] using heq)
  intro i
  refine ⟨?_, ?_⟩
  · simpa only [normalized_facetPressure hn G t ht i, rowWeight] using (h i).1
  · calc
      _ = (n : ℝ) * p * (1 / n) := by simpa only [pressure_add_remainder] using (h i).2.2
      _ = p := by field_simp

theorem rowRatio_eq_reference_of_uniform {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G)
    (t : ℝ) (ht : 0 < t) (i : Fin n) (p : ℝ) (hp : 0 < p)
    (hTest : rowK G t i ^ 2 / kappa G t ≤ stress G t i i)
    (hfloor : p ≤ capMass (projectedNormal G i) (fun _ ↦ t / referenceRatio n))
    (ha : rowWeight G t i = 1 / n) (hMass : singlePinMass G t i = p) :
    rowRatio G t i = referenceRatio n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs := canonical_quadratic_support G hG hd t ht i (t / referenceRatio n) p
    (div_pos ht (referenceRatio_pos hn)) hp hfloor
  rw [pressure_signed_identity hn G t i (rowK_pos hn G hG hd t ht i).ne', hMass] at hs
  have hz : p ^ 2 / p - p = 0 := by field_simp; ring
  rw [hz] at hs
  have hle : ((n : ℝ) - 2) * (1 - rowRatio G t i / referenceRatio n) ≤ 0 := by
    nlinarith [facetPressure_pos hn G hG hd t ht i]
  have hrow := canonical_signed_row_le hn G hG hd t ht i hTest
  have hzero : (n : ℝ) * rowWeight G t i - 1 = 0 := by rw [ha]; field_simp; ring
  rw [hzero] at hrow
  exact ((signed_row_equality hn _ _
    (rowRatio_sq_le G hG t i (rowK_pos hn G hG hd t ht i) hTest)).mp
    (by rw [hzero]; exact le_antisymm hle hrow)).1

theorem boundarySlope_eq_simplex_of_tests {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (hnotPD : ¬G.PosDef)
    (t : ℝ) (ht : 0 < t)
    (hTest : ∀ i, rowK G t i ^ 2 / kappa G t ≤ stress G t i i)
    (hcompare : ∀ H : Mat (n - 1), WeakSimplex.IsCorrelation H →
      cdf (simplex (n - 1)) (t / referenceRatio n) ≤ cdf H (t / referenceRatio n))
    (hslope : boundarySlope G t = boundarySlope (simplex n) t) :
    G = simplex n := by
  have hp := reference_mass_pos hn t ht
  have hfloor := fun i ↦ projected_reference_floor hn G hG hd i _ hcompare
  have heq : ∑ i, singlePinMass G t i =
      (n : ℝ) * cdf (simplex (n - 1)) (t / referenceRatio n) := by
    apply mul_left_cancel₀ (WeakSimplex.normalPDF_pos t).ne'
    rw [simplex_boundarySlope_recursion hn t ht, boundarySlope] at hslope
    calc
      _ = _ := hslope
      _ = _ := by ring
  have hu := singlePinMass_uniform_of_sum_eq hn G hG hd hnotPD t ht _ hp hTest hfloor heq
  exact correlation_eq_simplex_of_uniform_rows hn G hG hd t ht hTest (fun i ↦ (hu i).1)
    (fun i ↦ rowRatio_eq_reference_of_uniform hn G hG hd t ht i _ hp (hTest i)
      (hfloor i) (hu i).1 (hu i).2)

end FSC
