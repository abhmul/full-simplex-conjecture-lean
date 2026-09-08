import FSCProbes.SingularTriangle
import FSC.Analysis.PartialDerivatives
import FSC.Analysis.PeanoTaylor
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Actual threshold expansion for the singular triangle

Owned by analytic_preflight. The open active-support region permits an exact
event decomposition into an independent rectangle and a nonsingular bivariate cap.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace Topology ContDiff

namespace FSCProbes.TriangleThreshold

open FSC FSCProbes.SingularTriangle

def rectangle (a b : ℝ) : Set (Coord 2) := {y | y 0 ≤ a ∧ y 1 ≤ b}

def secondHalfspace (a : ℝ) : Set (Coord 2) := {y | y 1 ≤ a}

def bivariateCap (a b : ℝ) : Set (Coord 2) :=
  {y | y 1 ≤ a ∧ -(3 / 5) * y 0 + (4 / 5) * y 1 ≤ b}

def bivariateCDF (a b : ℝ) : ℝ :=
  (stdGaussian (Coord 2) (bivariateCap a b)).toReal

def triangleEvent (b : Coord 3) : Set (Coord 2) :=
  {y | y 0 ≤ b 0 ∧ y 1 ≤ b 1 ∧ -(3 / 5) * y 0 + (4 / 5) * y 1 ≤ b 2}

def activeRegion : Set (Coord 3) := {b | 4 * b 1 - 5 * b 2 < 3 * b 0}

theorem isOpen_activeRegion : IsOpen activeRegion := by
  exact isOpen_lt (by fun_prop) (by fun_prop)

theorem commonThreshold_mem_activeRegion (t : ℝ) (ht : 0 < t) :
    WeakSimplex.Coord.ofFun (fun _ : Fin 3 ↦ t) ∈ activeRegion := by
  change 4 * t - 5 * t < 3 * t
  linarith

theorem measurableSet_rectangle (a b : ℝ) : MeasurableSet (rectangle a b) := by
  change MeasurableSet ({y : Coord 2 | y 0 ≤ a} ∩ {y | y 1 ≤ b})
  apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) measurable_const

theorem measurableSet_bivariateCap (a b : ℝ) : MeasurableSet (bivariateCap a b) := by
  change MeasurableSet ({y : Coord 2 | y 1 ≤ a} ∩
    {y | -(3 / 5) * y 0 + (4 / 5) * y 1 ≤ b})
  apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) measurable_const

theorem rectangle_measure (a b : ℝ) :
    (stdGaussian (Coord 2) (rectangle a b)).toReal =
      WeakSimplex.normalCDF a * WeakSimplex.normalCDF b := by
  rw [← map_pi_eq_stdGaussian,
    Measure.map_apply (by fun_prop) (measurableSet_rectangle a b)]
  have hpre : (WithLp.toLp 2) ⁻¹' rectangle a b =
      Set.pi Set.univ ![Set.Iic a, Set.Iic b] := by
    ext y
    simp [rectangle, Set.mem_pi, Fin.forall_fin_two]
  rw [hpre, Measure.pi_pi]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ENNReal.toReal_mul, ← WeakSimplex.normalCDF_eq_measure_Iic]
  rw [ENNReal.toReal_ofReal (WeakSimplex.normalCDF_pos a).le,
    ENNReal.toReal_ofReal (WeakSimplex.normalCDF_pos b).le]

theorem secondHalfspace_measure (a : ℝ) :
    (stdGaussian (Coord 2) (secondHalfspace a)).toReal = WeakSimplex.normalCDF a := by
  have hmap : Measure.map (fun y : Coord 2 ↦ y 1) (stdGaussian (Coord 2)) =
      gaussianReal 0 1 := by
    simpa using (measurePreserving_eval_multivariateGaussian
      (μ := (0 : Coord 2)) (S := (1 : Mat 2)) Matrix.PosSemidef.one
      (i := (1 : Fin 2))).map_eq
  have hmeasure : stdGaussian (Coord 2) (secondHalfspace a) =
      gaussianReal 0 1 (Set.Iic a) := by
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  rw [hmeasure, ← WeakSimplex.normalCDF_eq_measure_Iic]
  exact ENNReal.toReal_ofReal (WeakSimplex.normalCDF_pos a).le

theorem thresholdCDF_eq_triangleEvent (b : Coord 3) :
    thresholdCDF gram b = (stdGaussian (Coord 2) (triangleEvent b)).toReal := by
  rw [thresholdCDF, ← map_normals_stdGaussian,
    Measure.map_apply (by unfold WeakSimplex.Coord.ofFun; fun_prop)
      (measurableSet_thresholdEvent b)]
  congr 2
  ext y
  simp [thresholdEvent, triangleEvent, normals, PiLp.inner_apply,
    Fin.forall_fin_succ, Fin.sum_univ_succ, Matrix.cons_val_two, mul_comm]

theorem rectangle_union_bivariateCap (b : Coord 3) (hb : b ∈ activeRegion) :
    rectangle (b 0) (b 1) ∪ bivariateCap (b 1) (b 2) = secondHalfspace (b 1) := by
  ext y
  change (y 0 ≤ b 0 ∧ y 1 ≤ b 1) ∨
      (y 1 ≤ b 1 ∧ -(3 / 5) * y 0 + (4 / 5) * y 1 ≤ b 2) ↔ y 1 ≤ b 1
  constructor
  · rintro (h | h)
    · exact h.2
    · exact h.1
  · intro h1
    by_cases h0 : y 0 ≤ b 0
    · exact Or.inl ⟨h0, h1⟩
    · refine Or.inr ⟨h1, ?_⟩
      change 4 * b 1 - 5 * b 2 < 3 * b 0 at hb
      linarith

theorem rectangle_inter_bivariateCap (b : Coord 3) :
    rectangle (b 0) (b 1) ∩ bivariateCap (b 1) (b 2) = triangleEvent b := by
  ext y
  simp [rectangle, bivariateCap, triangleEvent, and_assoc, and_left_comm]

theorem thresholdCDF_activeRegion (b : Coord 3) (hb : b ∈ activeRegion) :
    thresholdCDF gram b =
      WeakSimplex.normalCDF (b 0) * WeakSimplex.normalCDF (b 1) -
        WeakSimplex.normalCDF (b 1) + bivariateCDF (b 1) (b 2) := by
  have h := measureReal_union_add_inter
    (μ := stdGaussian (Coord 2))
    (s := rectangle (b 0) (b 1)) (measurableSet_bivariateCap (b 1) (b 2))
  rw [rectangle_union_bivariateCap b hb, rectangle_inter_bivariateCap] at h
  change (stdGaussian (Coord 2) (secondHalfspace (b 1))).toReal +
      (stdGaussian (Coord 2) (triangleEvent b)).toReal =
      (stdGaussian (Coord 2) (rectangle (b 0) (b 1))).toReal +
        bivariateCDF (b 1) (b 2) at h
  rw [secondHalfspace_measure, rectangle_measure, ← thresholdCDF_eq_triangleEvent] at h
  linarith

theorem map_stdGaussian_orthogonal (A : Mat 2)
    (hA : A * (1 : Mat 2) * A.transpose = 1) :
    (stdGaussian (Coord 2)).map (lin A) = stdGaussian (Coord 2) := by
  simpa only [multivariateGaussian_zero_one, map_zero, hA] using
    map_lin_multivariateGaussian (0 : Coord 2) (1 : Mat 2) Matrix.PosSemidef.one A

def positiveRotation : Mat 2 := !![0, -1; 1, 0]

theorem positiveRotation_orthogonal :
    positiveRotation * (1 : Mat 2) * positiveRotation.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveRotation, Matrix.mul_apply, Fin.sum_univ_two]

theorem bivariateCDF_positiveCap (a b : ℝ) :
    bivariateCDF a b =
      (stdGaussian (Coord 2) {y | y 0 ≤ a ∧ (4 / 5) * y 0 + (3 / 5) * y 1 ≤ b}).toReal := by
  conv_lhs =>
    rw [bivariateCDF, ← map_stdGaussian_orthogonal positiveRotation positiveRotation_orthogonal]
  rw [Measure.map_apply (lin positiveRotation).measurable (measurableSet_bivariateCap a b)]
  congr 2
  ext y
  simp [bivariateCap, lin_apply, positiveRotation, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, add_comm]

def swapReflection : Mat 2 := !![-(4 / 5), -(3 / 5); -(3 / 5), 4 / 5]

theorem swapReflection_orthogonal :
    swapReflection * (1 : Mat 2) * swapReflection.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapReflection, Matrix.mul_apply, Fin.sum_univ_two]

theorem bivariateCDF_symm (a b : ℝ) : bivariateCDF a b = bivariateCDF b a := by
  rw [bivariateCDF, ← map_stdGaussian_orthogonal swapReflection swapReflection_orthogonal,
    Measure.map_apply (lin swapReflection).measurable (measurableSet_bivariateCap a b)]
  change (stdGaussian (Coord 2) _).toReal =
    (stdGaussian (Coord 2) (bivariateCap b a)).toReal
  congr 2
  ext y
  simp only [Set.mem_preimage, bivariateCap, Set.mem_setOf_eq, lin_apply,
    swapReflection, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

def pairCoords (p : ℝ × ℝ) : Coord 2 := WeakSimplex.Coord.ofFun ![p.1, p.2]

theorem map_pairCoords_gaussian :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map pairCoords =
      stdGaussian (Coord 2) := by
  have hPi : ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (MeasurableEquiv.finTwoArrow (α := ℝ)).symm =
      Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 1) :=
    (MeasurePreserving.symm MeasurableEquiv.finTwoArrow
      (measurePreserving_finTwoArrow (gaussianReal 0 1))).map_eq
  change Measure.map
    ((WithLp.toLp 2) ∘ (MeasurableEquiv.finTwoArrow (α := ℝ)).symm) _ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hPi, map_pi_eq_stdGaussian]

def positiveProductEvent (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ a ∧ (4 / 5) * p.1 + (3 / 5) * p.2 ≤ b}

theorem measurableSet_positiveProductEvent (a b : ℝ) :
    MeasurableSet (positiveProductEvent a b) := by
  change MeasurableSet ({p : ℝ × ℝ | p.1 ≤ a} ∩
    {p | (4 / 5) * p.1 + (3 / 5) * p.2 ≤ b})
  apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) measurable_const

theorem bivariateCDF_product (a b : ℝ) :
    bivariateCDF a b =
      (((gaussianReal 0 1).prod (gaussianReal 0 1)) (positiveProductEvent a b)).toReal := by
  rw [bivariateCDF_positiveCap, ← map_pairCoords_gaussian]
  rw [Measure.map_apply (by unfold pairCoords WeakSimplex.Coord.ofFun; fun_prop) (by
    change MeasurableSet ({y : Coord 2 | y 0 ≤ a} ∩
      {y | (4 / 5) * y 0 + (3 / 5) * y 1 ≤ b})
    apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) measurable_const)]
  rfl

theorem bivariateCDF_slicing_gaussian (a b : ℝ) :
    bivariateCDF a b =
      ∫ x in Set.Iic a, WeakSimplex.normalCDF ((5 * b - 4 * x) / 3) ∂gaussianReal 0 1 := by
  classical
  rw [bivariateCDF_product]
  change (((gaussianReal 0 1).prod (gaussianReal 0 1)).real (positiveProductEvent a b)) = _
  have hInt : Integrable ((positiveProductEvent a b).indicator (1 : ℝ × ℝ → ℝ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_positiveProductEvent a b)
  rw [← integral_indicator_one (measurableSet_positiveProductEvent a b),
    integral_prod _ hInt, ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ≤ a
  · have heq : (fun y : ℝ ↦ (positiveProductEvent a b).indicator (1 : ℝ × ℝ → ℝ) (x, y)) =
        (Set.Iic ((5 * b - 4 * x) / 3)).indicator (1 : ℝ → ℝ) := by
      funext y
      have hxy : (x, y) ∈ positiveProductEvent a b ↔
          y ∈ Set.Iic ((5 * b - 4 * x) / 3) := by
        change (x ≤ a ∧ (4 / 5) * x + (3 / 5) * y ≤ b) ↔ y ≤ (5 * b - 4 * x) / 3
        constructor
        · intro h
          linarith
        · intro h
          exact ⟨hx, by linarith⟩
      simp only [Set.indicator_apply, hxy, Pi.one_apply]
    rw [heq, integral_indicator_one measurableSet_Iic, measureReal_def,
      ← WeakSimplex.normalCDF_eq_measure_Iic,
      ENNReal.toReal_ofReal (WeakSimplex.normalCDF_pos _).le]
    simp [hx]
  · have heq : (fun y : ℝ ↦ (positiveProductEvent a b).indicator (1 : ℝ × ℝ → ℝ) (x, y)) =
        fun _ ↦ (0 : ℝ) := by
      funext y
      simp [positiveProductEvent, hx]
    rw [heq]
    simp [hx]

theorem bivariateCDF_slicing (a b : ℝ) :
    bivariateCDF a b =
      ∫ x in Set.Iic a, WeakSimplex.normalPDF x *
        WeakSimplex.normalCDF ((5 * b - 4 * x) / 3) := by
  classical
  conv_lhs =>
    rw [bivariateCDF_slicing_gaussian, ← integral_indicator measurableSet_Iic,
      integral_gaussianReal_eq_integral_smul (by norm_num)]
  rw [← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Iic a <;>
    simp [hx, WeakSimplex.normalPDF, smul_eq_mul]

/-- Scalar FTC for an integrable continuous density on a moving lower half-line. -/
theorem hasDerivAt_Iic_integral_of_continuous (g : ℝ → ℝ)
    (hg : Integrable g) (hc : Continuous g) (a : ℝ) :
    HasDerivAt (fun z : ℝ ↦ ∫ x in Set.Iic z, g x) (g a) a := by
  have hFTC : HasDerivAt (fun u ↦ ∫ x in a..u, g x) (g a) a :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a a)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have heq : (fun z : ℝ ↦ ∫ x in Set.Iic z, g x) =
      fun z ↦ (∫ x in Set.Iic a, g x) + ∫ x in a..z, g x := by
    funext z
    have h := intervalIntegral.integral_Iic_sub_Iic (a := a) (b := z)
      hg.integrableOn hg.integrableOn
    linarith
  rw [heq]
  simpa only [zero_add] using! (hasDerivAt_const a (∫ x in Set.Iic a, g x)).add hFTC

theorem integrable_sliceDensity (b : ℝ) :
    Integrable (fun x : ℝ ↦ WeakSimplex.normalPDF x *
      WeakSimplex.normalCDF ((5 * b - 4 * x) / 3)) := by
  have hp : Integrable WeakSimplex.normalPDF := integrable_gaussianPDFReal 0 1
  have hcp : Continuous WeakSimplex.normalPDF :=
    continuous_iff_continuousAt.mpr fun x ↦ (WeakSimplex.hasDerivAt_normalPDF x).continuousAt
  have hcc : Continuous WeakSimplex.normalCDF := contDiff_one_normalCDF.continuous
  refine hp.mono' ((hcp.mul (hcc.comp (by fun_prop))).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (WeakSimplex.normalPDF_pos x).le (WeakSimplex.normalCDF_pos _).le)]
  exact mul_le_of_le_one_right (WeakSimplex.normalPDF_pos x).le
    (WeakSimplex.normalCDF_lt_one _).le

theorem hasDerivAt_bivariateCDF_left (a b : ℝ) :
    HasDerivAt (fun x : ℝ ↦ bivariateCDF x b)
      (WeakSimplex.normalPDF a * WeakSimplex.normalCDF ((5 * b - 4 * a) / 3)) a := by
  have heq : (fun x : ℝ ↦ bivariateCDF x b) =
      fun z ↦ ∫ x in Set.Iic z, WeakSimplex.normalPDF x *
        WeakSimplex.normalCDF ((5 * b - 4 * x) / 3) :=
    funext fun z ↦ bivariateCDF_slicing z b
  rw [heq]
  apply hasDerivAt_Iic_integral_of_continuous _ (integrable_sliceDensity b)
  exact (continuous_iff_continuousAt.mpr fun x ↦
    (WeakSimplex.hasDerivAt_normalPDF x).continuousAt).mul
      (contDiff_one_normalCDF.continuous.comp (by fun_prop))

theorem hasDerivAt_bivariateCDF_right (a b : ℝ) :
    HasDerivAt (fun x : ℝ ↦ bivariateCDF a x)
      (WeakSimplex.normalPDF b * WeakSimplex.normalCDF ((5 * a - 4 * b) / 3)) b := by
  have heq : (fun x : ℝ ↦ bivariateCDF a x) = fun x ↦ bivariateCDF x a :=
    funext fun x ↦ bivariateCDF_symm a x
  rw [heq]
  exact hasDerivAt_bivariateCDF_left b a

theorem contDiff_normalPDF (k : ℕ∞ω) : ContDiff ℝ k WeakSimplex.normalPDF := by
  unfold WeakSimplex.normalPDF gaussianPDFReal
  fun_prop

theorem contDiff_two_normalCDF : ContDiff ℝ 2 WeakSimplex.normalCDF := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨fun x ↦ WeakSimplex.normalPDF x • ContinuousLinearMap.id ℝ ℝ, ?_, ?_⟩
  · exact (contDiff_normalPDF 1).smul contDiff_const
  · intro x
    convert! (WeakSimplex.hasDerivAt_normalCDF x).hasFDerivAt using 1
    ext
    simp [mul_comm]

theorem contDiff_bivariateCDF : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ bivariateCDF p.1 p.2) := by
  apply contDiff_two_prod_of_partials
    (p := fun p ↦ WeakSimplex.normalPDF p.1 *
      WeakSimplex.normalCDF ((5 * p.2 - 4 * p.1) / 3))
    (q := fun p ↦ WeakSimplex.normalPDF p.2 *
      WeakSimplex.normalCDF ((5 * p.1 - 4 * p.2) / 3))
  · intro p
    exact hasDerivAt_bivariateCDF_left p.1 p.2
  · intro p
    exact hasDerivAt_bivariateCDF_right p.1 p.2
  · exact ((contDiff_normalPDF 1).comp contDiff_fst).mul
      (contDiff_one_normalCDF.comp (by fun_prop))
  · exact ((contDiff_normalPDF 1).comp contDiff_snd).mul
      (contDiff_one_normalCDF.comp (by fun_prop))

theorem contDiffAt_thresholdCDF (b : Coord 3) (hb : b ∈ activeRegion) :
    ContDiffAt ℝ 2 (thresholdCDF gram) b := by
  have hPair : ContDiff ℝ 2 (fun c : Coord 3 ↦ (c 1, c 2)) := by fun_prop
  have hB : ContDiff ℝ 2 (fun c : Coord 3 ↦ bivariateCDF (c 1) (c 2)) :=
    contDiff_bivariateCDF.comp hPair
  have hregular : ContDiff ℝ 2 (fun c : Coord 3 ↦
      WeakSimplex.normalCDF (c 0) * WeakSimplex.normalCDF (c 1) -
        WeakSimplex.normalCDF (c 1) + bivariateCDF (c 1) (c 2)) :=
    (((contDiff_two_normalCDF.comp (by fun_prop)).mul
      (contDiff_two_normalCDF.comp (by fun_prop))).sub
      (contDiff_two_normalCDF.comp (by fun_prop))).add
      hB
  apply hregular.contDiffAt.congr_of_eventuallyEq
  filter_upwards [isOpen_activeRegion.mem_nhds hb] with c hc
  exact thresholdCDF_activeRegion c hc

/-- Full vector-domain Peano expansion of the actual singular Gaussian threshold CDF. -/
theorem peano2_thresholdCDF (t : ℝ) (ht : 0 < t) :
    Peano2 (thresholdCDF gram) (WeakSimplex.Coord.ofFun (fun _ : Fin 3 ↦ t))
      (fderiv ℝ (thresholdCDF gram) (WeakSimplex.Coord.ofFun (fun _ : Fin 3 ↦ t)))
      (fderiv ℝ (fderiv ℝ (thresholdCDF gram))
        (WeakSimplex.Coord.ofFun (fun _ : Fin 3 ↦ t))) := by
  exact peano2_of_contDiffAt
    (contDiffAt_thresholdCDF _ (commonThreshold_mem_activeRegion t ht))

end FSCProbes.TriangleThreshold
