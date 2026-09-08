import FSC.Gaussian.PairLaw
import FSC.LinearAlgebra.Gram
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.Pi

/-! Canonical pair-weight symmetry and row positivity on general correlations. No singular facet or padded Gram construction is used. -/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace BigOperators ENNReal

namespace FSC

theorem pairAlpha_swap {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j k : Fin n) : pairAlpha G j i k = pairBeta G i j k := by
  have hsym : G j i = G i j := by simpa only [star_trivial] using hG.1.isHermitian.apply i j
  simp only [pairAlpha, pairBeta, hsym]

theorem pairBeta_swap {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j k : Fin n) : pairBeta G j i k = pairAlpha G i j k := by
  have hsym : G j i = G i j := by simpa only [star_trivial] using hG.1.isHermitian.apply i j
  simp only [pairAlpha, pairBeta, hsym]

theorem pairResidual_swap {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) : pairResidual G j i = pairResidual G i j := by
  ext k l
  simp only [pairResidual, pairAlpha_swap G hG i j k, pairBeta_swap G hG i j k]
  ring

theorem pairLaw_swap {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) (r s : ℝ) : pairLaw G j i s r = pairLaw G i j r s := by
  have hmean : pairMean G j i s r = pairMean G i j r s := by
    ext k
    simp only [pairMean, WeakSimplex.Coord.ofFun_apply,
      pairAlpha_swap G hG i j k, pairBeta_swap G hG i j k]
    ring
  simp only [pairLaw, pairCov, pairResidual_swap G hG i j, hmean]

theorem pairSuccess_swap {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) (t : ℝ) : pairSuccess G j i t = pairSuccess G i j t := by
  have hevent : pairEvent j i t = pairEvent i j t := by
    ext x
    exact ⟨fun h k hki hkj ↦ h k hkj hki, fun h k hkj hki ↦ h k hki hkj⟩
  rw [pairSuccess, pairSuccess, pairLaw_swap G hG i j t t, hevent]

theorem q_symm {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) (t : ℝ) : q G t i j = q G t j i := by
  have hsym : G j i = G i j := by simpa only [star_trivial] using hG.1.isHermitian.apply i j
  simp only [q, ne_comm, hsym, pairSuccess_swap G hG i j t, pairSupport, pairSigma]

theorem q_nonneg {n : ℕ} (G : Mat n) (t : ℝ) (i j : Fin n) : 0 ≤ q G t i j := by
  unfold q
  split_ifs
  · exact mul_nonneg (div_nonneg
      (mul_nonneg (WeakSimplex.normalPDF_pos t).le
        (WeakSimplex.normalPDF_pos (pairSupport G t i j)).le)
      (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg
  · exact le_rfl

/-- Standard Gaussian measure gives positive mass to every nonempty open set, in every dimension. -/
theorem stdGaussian_isOpenPosMeasure (n : ℕ) : Measure.IsOpenPosMeasure (stdGaussian (Coord n)) := by
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure
  rw [← map_pi_eq_stdGaussian]
  exact Continuous.isOpenPosMeasure_map (by fun_prop) (WithLp.toLp_surjective 2)

/-- Every open neighborhood of the mean has positive mass, even for a singular Gaussian. -/
theorem multivariateGaussian_pos_of_mem_open {n : ℕ} (μ : Coord n) (G : Mat n)
    (s : Set (Coord n)) (hs : IsOpen s) (hμ : μ ∈ s) : 0 < multivariateGaussian μ G s := by
  letI := stdGaussian_isOpenPosMeasure n
  rw [multivariateGaussian, Measure.map_apply (by fun_prop) hs.measurableSet]
  exact (hs.preimage (by fun_prop)).measure_pos (stdGaussian (Coord n))
    ⟨0, by simpa using hμ⟩

/-- Strict remaining-coordinate mean feasibility is sufficient for positive pair success. -/
theorem pairSuccess_pos_of_mean_lt {n : ℕ} (G : Mat n) (i j : Fin n) (t : ℝ)
    (hmean : ∀ k, k ≠ i → k ≠ j → pairMean G i j t t k < t) : 0 < pairSuccess G i j t := by
  let s : Set (Coord n) := {x | ∀ k, k ≠ i → k ≠ j → x k < t}
  have hs : IsOpen s := by
    simp only [s, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun k ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_iInter_of_finite fun _ ↦ ?_
    exact isOpen_lt (by fun_prop) continuous_const
  have hpos := multivariateGaussian_pos_of_mem_open (pairMean G i j t t) (pairCov G i j) s hs hmean
  have hle : s ⊆ pairEvent i j t := fun _ hx k hki hkj ↦ (hx k hki hkj).le
  have hmass : 0 < pairLaw G i j t t (pairEvent i j t) :=
    lt_of_lt_of_le hpos (measure_mono hle)
  exact ENNReal.toReal_pos hmass.ne' (by unfold pairLaw; exact measure_ne_top _ _)

/-- A nonantipodal maximal row pair has positive weight without any singularity hypothesis. -/
theorem q_pos_of_row_max {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hd : DistinctScores G) (t : ℝ) (ht : 0 < t) (i j : Fin n) (hij : i ≠ j)
    (hlo : -1 < G i j) (hmax : ∀ k, k ≠ i → G i k ≤ G i j) : 0 < q G t i j := by
  have hhi := hd i j hij
  have hc := pair_regression_denominator G i j hlo hhi
  have hmean : ∀ k, k ≠ i → k ≠ j → pairMean G i j t t k < t := by
    intro k hki hkj
    have hsymi : G k i = G i k := by simpa only [star_trivial] using hG.1.isHermitian.apply i k
    have hsymj : G k j = G j k := by simpa only [star_trivial] using hG.1.isHermitian.apply j k
    rw [pairMean_common G i j k t hc, div_lt_iff₀ (by linarith : 0 < 1 + G i j), hsymi, hsymj]
    have hlt : G i k + G j k < 1 + G i j := by
      linarith [hmax k hki, hd j k hkj.symm]
    nlinarith [mul_pos ht (sub_pos.mpr hlt)]
  have hs : 0 < pairSigma G i j := by
    apply Real.sqrt_pos.2
    have hprod := mul_pos (sub_pos.mpr hhi) (show 0 < 1 + G i j by linarith)
    nlinarith
  rw [q, if_pos ⟨hij, hlo, hhi⟩]
  exact mul_pos (div_pos (mul_pos (WeakSimplex.normalPDF_pos t)
    (WeakSimplex.normalPDF_pos (pairSupport G t i j))) hs) (pairSuccess_pos_of_mean_lt G i j t hmean)

theorem corr_entry_abs_le_one {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) : |G i j| ≤ 1 := by
  have hij := congrFun (congrFun (gram_gramVectors G hG.1) i) j
  simp only [Matrix.gram_apply] at hij
  simpa only [hij, norm_gramVectors G hG, one_mul] using
    abs_real_inner_le_norm (gramVectors G i) (gramVectors G j)

/-- Antipodal score vectors are negatives in the ordinary Gram realization. -/
theorem gramVectors_antipodal {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) (hc : G i j = -1) : gramVectors G j = -gramVectors G i := by
  have hij := congrFun (congrFun (gram_gramVectors G hG.1) i) j
  have hnorm := norm_add_sq_real (gramVectors G i) (gramVectors G j)
  simp only [Matrix.gram_apply] at hij
  rw [norm_gramVectors G hG, norm_gramVectors G hG, hij, hc] at hnorm
  have hz : gramVectors G i + gramVectors G j = 0 := norm_eq_zero.mp (by nlinarith)
  exact eq_neg_of_add_eq_zero_left (by rwa [add_comm])

/-- Three distinct scores ensure that a maximal off-diagonal row entry is nonantipodal. -/
theorem exists_row_max_nonantipodal {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (i : Fin n) :
    ∃ j, j ≠ i ∧ -1 < G i j ∧ ∀ k, k ≠ i → G i k ≤ G i j := by
  classical
  have hne : (Finset.univ.erase i).Nonempty := by
    apply Finset.card_pos.mp
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.univ.erase i) (G i) hne
  have hji := (Finset.mem_erase.mp hj).1
  refine ⟨j, hji, ?_, fun k hk ↦ hmax k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)⟩
  by_contra hbad
  have hc : G i j = -1 := le_antisymm (le_of_not_gt hbad) (abs_le.mp (corr_entry_abs_le_one G hG i j)).1
  have hne' : ((Finset.univ.erase i).erase j).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, hk⟩ := hne'
  have hkj := (Finset.mem_erase.mp hk).1
  have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hck : G i k = -1 := le_antisymm
    ((hmax k (Finset.mem_erase.mp hk).2).trans hc.le)
    (abs_le.mp (corr_entry_abs_le_one G hG i k)).1
  have hv : gramVectors G j = gramVectors G k := by
    rw [gramVectors_antipodal G hG i j hc, gramVectors_antipodal G hG i k hck]
  have hjk := congrFun (congrFun (gram_gramVectors G hG.1) j) k
  simp only [Matrix.gram_apply, hv, real_inner_self_eq_norm_sq, norm_gramVectors G hG, one_pow] at hjk
  have hlt := hd j k hkj.symm
  linarith

theorem exists_row_q_pos {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t)
    (i : Fin n) : ∃ j, j ≠ i ∧ -1 < G i j ∧ 0 < q G t i j := by
  obtain ⟨j, hji, hlo, hmax⟩ := exists_row_max_nonantipodal hn G hG hd i
  exact ⟨j, hji, hlo, q_pos_of_row_max G hG hd t ht i j hji.symm hlo hmax⟩

theorem rowK_pos {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t)
    (i : Fin n) : 0 < rowK G t i := by
  obtain ⟨j, hji, _, hq⟩ := exists_row_q_pos hn G hG hd t ht i
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (sub_nonneg.mpr (hd i k (Finset.mem_erase.mp hk).1.symm).le)
      (q_nonneg G t i k)
  · exact ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩,
      mul_pos (sub_pos.mpr (hd i j hji.symm)) hq⟩

theorem rowC_pos {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t)
    (i : Fin n) : 0 < rowC G t i := by
  obtain ⟨j, hji, hlo, hq⟩ := exists_row_q_pos hn G hG hd t ht i
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (Real.sqrt_nonneg _) (q_nonneg G t i k)
  · refine ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, mul_pos ?_ hq⟩
    apply Real.sqrt_pos.mpr
    have hprod := mul_pos (sub_pos.mpr (hd i j hji.symm)) (show 0 < 1 + G i j by linarith)
    nlinarith

theorem kappa_pos {n : ℕ} (hn : 3 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t) :
    0 < kappa G t := by
  apply Finset.sum_pos'
  · exact fun i _ ↦ (rowK_pos hn G hG hd t ht i).le
  · exact ⟨⟨0, by omega⟩, Finset.mem_univ _, rowK_pos hn G hG hd t ht _⟩

end FSC
