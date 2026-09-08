import FSC.Support.Padding
import FSCProbes.SingularTriangle
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FSCChecks.WP11

open FSC

theorem normalPDF_neg (t : ℝ) : WeakSimplex.normalPDF (-t) = WeakSimplex.normalPDF t := by
  simp [WeakSimplex.normalPDF, gaussianPDFReal]

theorem normalCDF_neg (t : ℝ) :
    WeakSimplex.normalCDF (-t) = 1 - WeakSimplex.normalCDF t := by
  have hp : Integrable WeakSimplex.normalPDF := integrable_gaussianPDFReal 0 1
  have hsum := intervalIntegral.integral_Iic_add_Ioi
    (b := t) hp.integrableOn hp.integrableOn
  have hneg := integral_comp_neg_Iic (-t) WeakSimplex.normalPDF
  simp only [normalPDF_neg, neg_neg] at hneg
  have htotal : (∫ x : ℝ, WeakSimplex.normalPDF x) = 1 :=
    integral_gaussianPDFReal_eq_one 0 one_ne_zero
  rw [htotal] at hsum
  change (∫ x in Set.Iic t, WeakSimplex.normalPDF x) +
    (∫ x in Set.Ioi t, WeakSimplex.normalPDF x) = 1 at hsum
  dsimp [WeakSimplex.normalCDF]
  linarith

theorem gaussian_Icc_mass (t : ℝ) (ht : 0 ≤ t) :
    (gaussianReal 0 1 (Set.Icc (-t) t)).toReal = 2 * WeakSimplex.normalCDF t - 1 := by
  have hp : Integrable WeakSimplex.normalPDF := integrable_gaussianPDFReal 0 1
  have h := intervalIntegral.integral_Iic_sub_Iic
    (a := -t) (b := t) hp.integrableOn hp.integrableOn
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc] at h
  rw [← WeakSimplex.normalCDF, ← WeakSimplex.normalCDF, normalCDF_neg] at h
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun x ↦
    (gaussianPDFReal_pos 0 1 x one_ne_zero).le)]
  change (∫ x in Set.Icc (-t) t, WeakSimplex.normalPDF x) = _
  linarith

theorem gaussian_Icc_secondMoment (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in Set.Icc (-t) t, x ^ 2 ∂gaussianReal 0 1) =
      (2 * WeakSimplex.normalCDF t - 1) - 2 * t * WeakSimplex.normalPDF t := by
  have hp : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hpdf : Integrable (fun x : ℝ ↦ x ^ 2 * WeakSimplex.normalPDF x) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integrable_withDensity_iff (measurable_gaussianPDF 0 1)
        (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)] at hp
    simpa only [toReal_gaussianPDF, WeakSimplex.normalPDF] using hp
  have h := intervalIntegral.integral_Iic_sub_Iic
    (a := -t) (b := t) hpdf.integrableOn hpdf.integrableOn
  rw [WeakSimplex.truncated_second_moment, WeakSimplex.truncated_second_moment,
    normalCDF_neg, normalPDF_neg, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    setIntegral_withDensity_eq_setIntegral_toReal_smul' _ (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  simp_rw [toReal_gaussianPDF, smul_eq_mul, mul_comm (gaussianPDFReal 0 1 _)]
  change (∫ x in Set.Icc (-t) t, x ^ 2 * WeakSimplex.normalPDF x) = _
  linarith

def intervalNormals : Fin 2 → Coord 1 :=
  ![WeakSimplex.Coord.ofFun (fun _ ↦ 1), WeakSimplex.Coord.ofFun (fun _ ↦ -1)]

theorem interval_cap (t : ℝ) :
    cap intervalNormals (fun _ ↦ t) = (fun y : Coord 1 ↦ y 0) ⁻¹' Set.Icc (-t) t := by
  ext y
  simp [cap, intervalNormals, Fin.forall_fin_two, PiLp.inner_apply]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem map_eval_stdGaussian_one :
    (stdGaussian (Coord 1)).map (fun y : Coord 1 ↦ y 0) = gaussianReal 0 1 := by
  simpa using (measurePreserving_eval_multivariateGaussian
    (μ := (0 : Coord 1)) (S := (1 : Mat 1)) Matrix.PosSemidef.one (i := (0 : Fin 1))).map_eq

theorem interval_mass (t : ℝ) (ht : 0 ≤ t) :
    capMass intervalNormals (fun _ ↦ t) = 2 * WeakSimplex.normalCDF t - 1 := by
  rw [capMass, interval_cap, ← Measure.map_apply (by fun_prop) measurableSet_Icc,
    map_eval_stdGaussian_one, gaussian_Icc_mass t ht]

theorem interval_energy (t : ℝ) (ht : 0 ≤ t) :
    capEnergy intervalNormals (fun _ ↦ t) =
      (2 * WeakSimplex.normalCDF t - 1) - 2 * t * WeakSimplex.normalPDF t := by
  have h := setIntegral_map (μ := stdGaussian (Coord 1))
    (g := fun y : Coord 1 ↦ y 0) (f := fun x : ℝ ↦ x ^ 2)
    (s := Set.Icc (-t) t)
    measurableSet_Icc (by fun_prop) (by fun_prop)
  rw [map_eval_stdGaussian_one] at h
  rw [capEnergy, interval_cap]
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]
  rw [← h, gaussian_Icc_secondMoment t ht]

theorem square_strip_energy (t : ℝ) (ht : 0 ≤ t) :
    capEnergy (padNormals 1 intervalNormals) (fun _ ↦ t) =
      2 * (2 * WeakSimplex.normalCDF t - 1) - 2 * t * WeakSimplex.normalPDF t := by
  rw [capEnergy_padNormals, interval_energy t ht, interval_mass t ht]
  norm_num
  ring

theorem square_strip_normalized_energy_pos (t : ℝ) (ht : 0 < t) :
    0 < (2 * WeakSimplex.normalCDF t - 1) - t * WeakSimplex.normalPDF t := by
  have he := capEnergy_pos (padNormals 1 intervalNormals) (fun _ ↦ t) (by norm_num)
    (fun _ ↦ ht)
  rw [square_strip_energy t ht.le] at he
  linarith

theorem square_strip_shape (t : ℝ) :
    cap (padNormals 1 intervalNormals) (fun _ ↦ t) =
      {y : Coord 2 | -t ≤ y 0 ∧ y 0 ≤ t} := by
  rw [cap_padNormals, interval_cap]
  ext y
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true,
    splitCoords_fst, Set.mem_setOf_eq]
  rfl

theorem square_strip_dilation_flux (t : ℝ) (ht : 0 ≤ t) :
    ((2 : ℝ) * capMass (padNormals 1 intervalNormals) (fun _ ↦ t) -
      capEnergy (padNormals 1 intervalNormals) (fun _ ↦ t)) / 2 =
      t * WeakSimplex.normalPDF t := by
  rw [capMass_padNormals, interval_mass t ht, square_strip_energy t ht]
  ring

theorem hasDerivAt_redundant_cap_dilation (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ capMass FSCProbes.SingularTriangle.redundantNormals
      (s • ![t, 2 * t])) (t * WeakSimplex.normalPDF t) 1 := by
  have hpath : HasDerivAt (fun s : ℝ ↦ s * t) t 1 := by
    simpa only [id_eq, one_mul] using! ((hasDerivAt_id (1 : ℝ)).mul_const t)
  have hpdf : HasDerivAt WeakSimplex.normalCDF (WeakSimplex.normalPDF t)
      ((fun s : ℝ ↦ s * t) 1) := by
    simpa only [one_mul] using! WeakSimplex.hasDerivAt_normalCDF t
  have h := hpdf.comp 1 hpath
  apply (h.congr_deriv (mul_comm _ _)).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
  have heq : s • ![t, 2 * t] = ![s * t, s * (2 * t)] := by ext i; fin_cases i <;> rfl
  rw [heq, FSCProbes.SingularTriangle.redundant_capMass]
  rw [min_eq_left (by nlinarith [mul_pos hs ht])]
  rfl

theorem redundant_halfLine_energy (t : ℝ) (ht : 0 < t) :
    capEnergy FSCProbes.SingularTriangle.redundantNormals ![t, 2 * t] =
      WeakSimplex.normalCDF t - t * WeakSimplex.normalPDF t := by
  have h := (hasDerivAt_capMass_dilate FSCProbes.SingularTriangle.redundantNormals
    ![t, 2 * t]).unique (hasDerivAt_redundant_cap_dilation t ht)
  rw [FSCProbes.SingularTriangle.redundant_capMass, min_eq_left (by linarith)] at h
  norm_num at h
  linarith

end FSCChecks.WP11

#print axioms FSCChecks.WP11.gaussian_Icc_secondMoment
#print axioms FSCChecks.WP11.interval_energy
#print axioms FSCChecks.WP11.square_strip_energy
#print axioms FSCChecks.WP11.square_strip_normalized_energy_pos
#print axioms FSCChecks.WP11.square_strip_shape
#print axioms FSCChecks.WP11.square_strip_dilation_flux
#print axioms FSCChecks.WP11.hasDerivAt_redundant_cap_dilation
#print axioms FSCChecks.WP11.redundant_halfLine_energy
