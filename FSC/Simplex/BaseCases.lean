import FSC.Simplex.Definitions
import FSC.Gaussian.CDFContinuity
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FinCases

/-! All-dimensional nonpositive thresholds and the exact two-coordinate comparison. -/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology BigOperators InnerProductSpace

namespace FSC

def sumProjection (n : ℕ) : Matrix (Fin 1) (Fin n) ℝ := fun _ _ ↦ 1

@[simp] theorem lin_sumProjection_apply {n : ℕ} (x : Coord n) (i : Fin 1) :
    lin (sumProjection n) x i = ∑ j, x j := by
  simp [lin_apply, sumProjection, Matrix.mulVec, dotProduct]

theorem map_sum_simplex {n : ℕ} (hn : 2 ≤ n) :
    Measure.map (lin (sumProjection n)) (multivariateGaussian (0 : Coord n) (simplex n)) =
      Measure.dirac (0 : Coord 1) := by
  have hzero : sumProjection n * simplex n = 0 := by
    ext i j
    simp [Matrix.mul_apply, sumProjection, simplex_sum_column hn]
  have h := map_lin_multivariateGaussian (0 : Coord n) (simplex n)
    (simplex_isCorrelation hn).1 (sumProjection n)
  simpa only [map_zero, hzero, Matrix.zero_mul, multivariateGaussian_zero_cov] using h

theorem simplex_sum_ae {n : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ x ∂multivariateGaussian (0 : Coord n) (simplex n), ∑ i, x i = 0 := by
  have h : ∀ᵐ y ∂Measure.map (lin (sumProjection n))
      (multivariateGaussian (0 : Coord n) (simplex n)), y 0 = 0 := by
    rw [map_sum_simplex hn]
    simp
  simpa only [lin_sumProjection_apply] using
    ae_of_ae_map (lin (sumProjection n)).measurable.aemeasurable h

theorem simplex_cdf_nonpos {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (ht : t ≤ 0) :
    cdf (simplex n) t = 0 := by
  let i : Fin n := ⟨0, by omega⟩
  have hnull := gaussian_coordinate_hyperplane_null (0 : Coord n) (simplex n)
    (simplex_isCorrelation hn).1 i (by rw [(simplex_isCorrelation hn).2 i]; norm_num) 0
  have hsub : WeakSimplex.lowerOrthant t ≤ᵐ[multivariateGaussian (0 : Coord n) (simplex n)]
      {x : Coord n | x i = 0} := by
    filter_upwards [simplex_sum_ae hn] with x hx hxt
    exact ((Finset.sum_eq_zero_iff_of_nonpos (fun j _ ↦ (hxt j).trans ht)).mp hx) i (Finset.mem_univ i)
  unfold cdf
  rw [measure_mono_null_ae hsub hnull, ENNReal.toReal_zero]

theorem comparison_nonpos {n : ℕ} (hn : 2 ≤ n) (G : Mat n) (t : ℝ) (ht : t ≤ 0) :
    cdf (simplex n) t ≤ cdf G t := by
  rw [simplex_cdf_nonpos hn t ht]
  exact cdf_nonneg G t

theorem gaussian_coordinate_le_toReal {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) (t : ℝ) :
    (multivariateGaussian (0 : Coord n) G {x : Coord n | x i ≤ t}).toReal =
      WeakSimplex.normalCDF t := by
  have h := congrArg (fun m : Measure ℝ ↦ (m (Set.Iic t)).toReal) (map_pin G hG i)
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
    ← WeakSimplex.normalCDF_eq_measure_Iic, ENNReal.toReal_ofReal (WeakSimplex.normalCDF_pos t).le] at h
  exact h

def twoExceed (t : ℝ) : Set (Coord 2) := {x | t < x 0 ∧ t < x 1}

theorem measurableSet_twoExceed (t : ℝ) : MeasurableSet (twoExceed t) := by
  change MeasurableSet ({x : Coord 2 | t < x 0} ∩ {x : Coord 2 | t < x 1})
  exact (measurableSet_lt measurable_const (by fun_prop)).inter
    (measurableSet_lt measurable_const (by fun_prop))

theorem two_site_cdf_formula (G : Mat 2) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    cdf G t = 2 * WeakSimplex.normalCDF t - 1 +
      (multivariateGaussian (0 : Coord 2) G (twoExceed t)).toReal := by
  let μ := multivariateGaussian (0 : Coord 2) G
  let A : Set (Coord 2) := {x | x 0 ≤ t}
  let B : Set (Coord 2) := {x | x 1 ≤ t}
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hB : MeasurableSet B := measurableSet_le (by fun_prop) measurable_const
  have hcap : A ∩ B = WeakSimplex.lowerOrthant t := by
    ext x
    constructor
    · rintro ⟨hx0, hx1⟩ i
      fin_cases i <;> assumption
    · intro hx
      exact ⟨hx 0, hx 1⟩
  have hexc : (A ∪ B)ᶜ = twoExceed t := by
    ext x
    simp [A, B, twoExceed]
  have hsum := measureReal_union_add_inter (μ := μ) (s := A) hB
  have hcompl := measureReal_add_measureReal_compl (μ := μ) (hA.union hB)
  rw [hcap] at hsum
  rw [hexc] at hcompl
  have hmA : μ.real A = WeakSimplex.normalCDF t := gaussian_coordinate_le_toReal G hG 0 t
  have hmB : μ.real B = WeakSimplex.normalCDF t := gaussian_coordinate_le_toReal G hG 1 t
  rw [hmA, hmB] at hsum
  simp only [probReal_univ] at hcompl
  change cdf G t = _
  change μ.real (A ∪ B) + cdf G t = _ at hsum
  change μ.real (A ∪ B) + (μ (twoExceed t)).toReal = 1 at hcompl
  linarith

/-- A nonantipodal two-score law gives positive mass to joint exceedance, including the duplicate law. -/
theorem two_exceed_pos (G : Mat 2) (hG : WeakSimplex.IsCorrelation G)
    (hc : -1 < G 0 1) (t : ℝ) :
    0 < multivariateGaussian (0 : Coord 2) G (twoExceed t) := by
  let v := gramVectors G
  have hin (i j : Fin 2) : inner ℝ (v i) (v j) = G i j := by
    exact congrFun (congrFun (gram_gramVectors G hG.1) i) j
  have hsym : G 1 0 = G 0 1 := by simpa only [star_trivial] using hG.1.isHermitian.apply 0 1
  have hden : 1 + G 0 1 ≠ 0 := by linarith
  let z : Coord 2 := ((t + 1) / (1 + G 0 1)) • (v 0 + v 1)
  have hz0 : inner ℝ (v 0) z = t + 1 := by
    simp only [z, real_inner_smul_right, inner_add_right, hin, hG.2 0]
    field_simp
  have hz1 : inner ℝ (v 1) z = t + 1 := by
    simp only [z, real_inner_smul_right, inner_add_right, hin, hG.2 1, hsym]
    field_simp
    ring
  rw [← map_gramVectors_stdGaussian G hG.1,
    Measure.map_apply (by unfold WeakSimplex.Coord.ofFun; fun_prop) (measurableSet_twoExceed t)]
  letI := stdGaussian_isOpenPosMeasure 2
  have hopen : IsOpen {y : Coord 2 | t < inner ℝ (v 0) y ∧ t < inner ℝ (v 1) y} := by
    change IsOpen ({y : Coord 2 | t < inner ℝ (v 0) y} ∩ {y : Coord 2 | t < inner ℝ (v 1) y})
    exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))
  exact hopen.measure_pos (stdGaussian (Coord 2)) ⟨z, by
    change t < inner ℝ (v 0) z ∧ t < inner ℝ (v 1) z
    rw [hz0, hz1]
    constructor <;> linarith⟩

theorem simplex_two_exceed_null (t : ℝ) (ht : 0 ≤ t) :
    multivariateGaussian (0 : Coord 2) (simplex 2) (twoExceed t) = 0 := by
  apply measure_mono_null_ae (t := ∅) _ (measure_empty)
  filter_upwards [simplex_sum_ae (by norm_num : 2 ≤ 2)] with x hx hexc
  have h0 := hexc.1
  have h1 := hexc.2
  simp only [Fin.sum_univ_two] at hx
  exfalso
  linarith

theorem simplex_two_cdf (t : ℝ) (ht : 0 ≤ t) :
    cdf (simplex 2) t = 2 * WeakSimplex.normalCDF t - 1 := by
  rw [two_site_cdf_formula _ (simplex_isCorrelation (by norm_num)), simplex_two_exceed_null t ht]
  simp

theorem two_eq_simplex_iff (G : Mat 2) (hG : WeakSimplex.IsCorrelation G) :
    G = simplex 2 ↔ G 0 1 = -1 := by
  constructor
  · intro h
    rw [h, simplex_apply (by norm_num)]
    norm_num
  · intro hc
    have hsym : G 1 0 = G 0 1 := by simpa only [star_trivial] using hG.1.isHermitian.apply 0 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [simplex_apply (by norm_num : 2 ≤ 2), hG.2, hc, hsym]

theorem two_site_compare (G : Mat 2) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    cdf (simplex 2) t ≤ cdf G t := by
  by_cases ht : t ≤ 0
  · exact comparison_nonpos (by norm_num) G t ht
  · rw [simplex_two_cdf t (le_of_not_ge ht), two_site_cdf_formula G hG t]
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg

theorem two_site_strict (G : Mat 2) (hG : WeakSimplex.IsCorrelation G)
    (hne : G ≠ simplex 2) (t : ℝ) (ht : 0 < t) : cdf (simplex 2) t < cdf G t := by
  have hcne : G 0 1 ≠ -1 := fun hc ↦ hne ((two_eq_simplex_iff G hG).mpr hc)
  have hc : -1 < G 0 1 := lt_of_le_of_ne (abs_le.mp (corr_entry_abs_le_one G hG 0 1)).1 hcne.symm
  have hpos : 0 < (multivariateGaussian (0 : Coord 2) G (twoExceed t)).toReal :=
    ENNReal.toReal_pos (two_exceed_pos G hG hc t).ne' (measure_ne_top _ _)
  rw [simplex_two_cdf t ht.le, two_site_cdf_formula G hG t]
  linarith

theorem two_site_equality (G : Mat 2) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (ht : 0 < t) : cdf G t = cdf (simplex 2) t ↔ G = simplex 2 := by
  constructor
  · intro heq
    by_contra hne
    exact (ne_of_lt (two_site_strict G hG hne t ht)) heq.symm
  · intro heq
    rw [heq]

end FSC
