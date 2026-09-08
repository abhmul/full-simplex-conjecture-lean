import FSC.Facet.PaddedNormals
import FSC.Gaussian.ThresholdExpansion
import FSC.Support.Dilation

/-! Canonical pair weights, physical padded caps, pressure and Gaussian energy. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace FSC

theorem cast_facetDimension {n : ℕ} (hn : 2 ≤ n) :
    ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
  rw [Nat.cast_sub hn]
  norm_num

theorem facetDimension_pos {n : ℕ} (hn : 3 ≤ n) : 0 < ((n - 2 : ℕ) : ℝ) := by
  exact_mod_cast (show 0 < n - 2 by omega)

theorem sum_retained_rowK {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) :
    (∑ j : RetainedPair G i, (1 - G i j) * q G t i j) = rowK G t i := by
  calc
    _ = ∑ j : Fin n, (1 - G i j) * q G t i j := by
      simpa only [mul_comm] using sum_retained_q G t i (fun j ↦ 1 - G i j)
    _ = _ := by rw [rowK, Finset.sum_erase_eq_sub (Finset.mem_univ i)]; simp

theorem sum_retained_rowC {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) :
    (∑ j : RetainedPair G i, pairSigma G i j * q G t i j) = rowC G t i := by
  calc
    _ = ∑ j : Fin n, pairSigma G i j * q G t i j := by
      simpa only [mul_comm] using sum_retained_q G t i (fun j ↦ pairSigma G i j)
    _ = _ := by rw [rowC, Finset.sum_erase_eq_sub (Finset.mem_univ i)]; simp

theorem projected_sliceCoefficient {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (j : RetainedPair G i)
    (t : ℝ) (ht : 0 < t) :
    WeakSimplex.normalPDF (pairSupport G t i j) *
      sliceMass (projectedNormal G i) (fun k ↦ pairSupport G t i k) j =
      pairSigma G i j * q G t i j / WeakSimplex.normalPDF t := by
  rw [q_eq_projected_slice G hG hDistinct i j t ht]
  field_simp [(retained_sigma_pos G i j).ne', (WeakSimplex.normalPDF_pos t).ne']

theorem supportGradient_projected_q {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (t : ℝ) (ht : 0 < t)
    (h : RetainedPair G i → ℝ) :
    supportGradient (projectedNormal G i) (fun j ↦ pairSupport G t i j) h =
      (∑ j, h j * pairSigma G i j * q G t i j) / WeakSimplex.normalPDF t := by
  simp only [supportGradient, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp_rw [projected_sliceCoefficient G hG hDistinct i _ t ht]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem supportGradient_projected_support {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hDistinct : DistinctScores G)
    (i : Fin n) (t : ℝ) (ht : 0 < t) :
    supportGradient (projectedNormal G i) (fun j ↦ pairSupport G t i j)
      (fun j ↦ pairSupport G t i j) = t * rowK G t i / WeakSimplex.normalPDF t := by
  rw [supportGradient_projected_q G hG hDistinct i t ht]
  congr 1
  rw [← sum_retained_rowK, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold pairSupport
  field_simp [(retained_sigma_pos G i j).ne']

theorem supportGradient_projected_one {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hDistinct : DistinctScores G)
    (i : Fin n) (t : ℝ) (ht : 0 < t) :
    supportGradient (projectedNormal G i) (fun j ↦ pairSupport G t i j) (fun _ ↦ 1) =
      rowC G t i / WeakSimplex.normalPDF t := by
  rw [supportGradient_projected_q G hG hDistinct i t ht]
  simp only [one_mul, sum_retained_rowC]

/-- The dimension-normalized pressure of the same canonical pinned cap. -/
def facetPressure {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) : ℝ :=
  t * rowK G t i / (((n - 2 : ℕ) : ℝ) * WeakSimplex.normalPDF t)

/-- The actual second-moment integral in the full padded tangent dimension, divided by that dimension. -/
def facetEnergy {n : ℕ} (hn : 3 ≤ n) (v : Fin n → Coord (n - 1))
    (hv : ∀ k, ‖v k‖ = 1) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hgram : Matrix.gram ℝ v = G) (t : ℝ) (i : Fin n) : ℝ :=
  capEnergy (paddedFacetNormal hn v hv G hG hgram i) (fun j ↦ pairSupport G t i j) /
    ((n - 2 : ℕ) : ℝ)

theorem facetPressure_pos {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hDistinct : DistinctScores G)
    (t : ℝ) (ht : 0 < t) (i : Fin n) : 0 < facetPressure G t i :=
  div_pos (mul_pos ht (rowK_pos hn G hG hDistinct t ht i))
    (mul_pos (facetDimension_pos hn) (WeakSimplex.normalPDF_pos t))

theorem facetEnergy_pos {n : ℕ} (hn : 3 ≤ n) (v : Fin n → Coord (n - 1))
    (hv : ∀ k, ‖v k‖ = 1) (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hgram : Matrix.gram ℝ v = G) (t : ℝ) (ht : 0 < t) (i : Fin n) :
    0 < facetEnergy hn v hv G hG hgram t i :=
  div_pos (capEnergy_pos _ _ (by omega) (retained_support_pos G i t ht))
    (facetDimension_pos hn)

theorem capMass_padded_eq_singlePinMass {n : ℕ} (hn : 3 ≤ n)
    (v : Fin n → Coord (n - 1)) (hv : ∀ k, ‖v k‖ = 1) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hgram : Matrix.gram ℝ v = G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) (i : Fin n) :
    capMass (paddedFacetNormal hn v hv G hG hgram i) (fun j ↦ pairSupport G t i j) =
      singlePinMass G t i := by
  rw [capMass_paddedFacetNormal, capMass_projected_common G hG hDistinct i t ht]

theorem capEnergy_padded_eq {n : ℕ} (hn : 3 ≤ n)
    (v : Fin n → Coord (n - 1)) (hv : ∀ k, ‖v k‖ = 1) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hgram : Matrix.gram ℝ v = G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) (i : Fin n) :
    capEnergy (paddedFacetNormal hn v hv G hG hgram i) (fun j ↦ pairSupport G t i j) =
      ((n - 2 : ℕ) : ℝ) * singlePinMass G t i -
        t * rowK G t i / WeakSimplex.normalPDF t := by
  have hs : (∑ j : RetainedPair G i, pairSupport G t i j * WeakSimplex.normalPDF (pairSupport G t i j) *
      sliceMass (paddedFacetNormal hn v hv G hG hgram i) (fun k ↦ pairSupport G t i k) j) =
      t * rowK G t i / WeakSimplex.normalPDF t := by
    calc
      _ = supportGradient (paddedFacetNormal hn v hv G hG hgram i)
          (fun j ↦ pairSupport G t i j) (fun j ↦ pairSupport G t i j) := by
        simp [supportGradient, mul_assoc]
      _ = _ := by
        rw [supportGradient_paddedFacetNormal hn v hv G hG hgram hDistinct i t ht,
          supportGradient_projected_support G hG hDistinct i t ht]
  rw [capEnergy_eq_of_hasFDerivAt _ _
    (hasFDerivAt_capMass _ (norm_paddedFacetNormal hn v hv G hG hgram i) _
      (noCoincident_paddedFacetNormal hn v hv G hG hgram hDistinct i t ht)),
    capMass_padded_eq_singlePinMass hn v hv G hG hgram hDistinct t ht i, hs]

/-- Both components come from the same actual cap and the same canonical pair weights. -/
theorem singlePinMass_eq_pressure_add_energy {n : ℕ} (hn : 3 ≤ n)
    (v : Fin n → Coord (n - 1)) (hv : ∀ k, ‖v k‖ = 1) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hgram : Matrix.gram ℝ v = G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) (i : Fin n) :
    singlePinMass G t i = facetPressure G t i + facetEnergy hn v hv G hG hgram t i := by
  unfold facetPressure facetEnergy
  rw [capEnergy_padded_eq hn v hv G hG hgram hDistinct t ht i]
  field_simp [(facetDimension_pos hn).ne', (WeakSimplex.normalPDF_pos t).ne']
  ring

/-- A realization-free positivity consequence, discharged using an actual padded Gaussian integral. -/
theorem singlePinMass_sub_pressure_pos {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hDistinct : DistinctScores G) (hnotPD : ¬G.PosDef)
    (t : ℝ) (ht : 0 < t) (i : Fin n) : 0 < singlePinMass G t i - facetPressure G t i := by
  obtain ⟨v, hv, hgram⟩ := exists_padded_unit_gram (by omega : 1 ≤ n) G hG hnotPD
  rw [singlePinMass_eq_pressure_add_energy hn v hv G hG hgram hDistinct t ht i]
  simpa only [add_sub_cancel_left] using facetEnergy_pos hn v hv G hG hgram t ht i

theorem sum_facetPressure {n : ℕ} (G : Mat n) (t : ℝ) :
    (∑ i, facetPressure G t i) =
      t * kappa G t / (((n - 2 : ℕ) : ℝ) * WeakSimplex.normalPDF t) := by
  simp only [facetPressure, ← Finset.sum_div, ← Finset.mul_sum, kappa]

theorem normalized_facetPressure {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (t : ℝ) (ht : 0 < t) (i : Fin n) :
    facetPressure G t i / (∑ k, facetPressure G t k) = rowK G t i / kappa G t := by
  rw [sum_facetPressure, facetPressure]
  have hc : t / (((n - 2 : ℕ) : ℝ) * WeakSimplex.normalPDF t) ≠ 0 :=
    div_ne_zero ht.ne' (mul_ne_zero (facetDimension_pos hn).ne' (WeakSimplex.normalPDF_pos t).ne')
  calc
    _ = (t / (((n - 2 : ℕ) : ℝ) * WeakSimplex.normalPDF t) * rowK G t i) /
        (t / (((n - 2 : ℕ) : ℝ) * WeakSimplex.normalPDF t) * kappa G t) := by ring
    _ = _ := mul_div_mul_left _ _ hc

theorem supportGradient_projected_reference {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hDistinct : DistinctScores G)
    (i : Fin n) (t : ℝ) (ht : 0 < t) (s : ℝ) :
    supportGradient (projectedNormal G i) (fun j ↦ pairSupport G t i j)
      (fun j ↦ s - pairSupport G t i j) =
      (s * rowC G t i - t * rowK G t i) / WeakSimplex.normalPDF t := by
  have he : (fun j : RetainedPair G i ↦ s - pairSupport G t i j) =
      s • (fun _ : RetainedPair G i ↦ (1 : ℝ)) -
        (fun j : RetainedPair G i ↦ pairSupport G t i j) := by ext j; simp
  rw [he, map_sub, map_smul, supportGradient_projected_one G hG hDistinct i t ht,
    supportGradient_projected_support G hG hDistinct i t ht]
  simp only [smul_eq_mul]
  ring

theorem supportGradient_padded_reference {n : ℕ} (hn : 3 ≤ n)
    (v : Fin n → Coord (n - 1)) (hv : ∀ k, ‖v k‖ = 1) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hgram : Matrix.gram ℝ v = G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) (i : Fin n) (s : ℝ) :
    supportGradient (paddedFacetNormal hn v hv G hG hgram i) (fun j ↦ pairSupport G t i j)
      (fun j ↦ s - pairSupport G t i j) =
      (s * rowC G t i - t * rowK G t i) / WeakSimplex.normalPDF t := by
  rw [supportGradient_paddedFacetNormal hn v hv G hG hgram hDistinct i t ht,
    supportGradient_projected_reference G hG hDistinct i t ht]

end FSC
