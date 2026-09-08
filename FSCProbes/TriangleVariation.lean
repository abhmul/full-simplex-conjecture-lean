import FSCProbes.TriangleThreshold
import FSC.Analysis.NoiseAveraging
import FSC.Gaussian.IndependentSum
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Actual rank-increasing Gaussian noise at the singular triangle. -/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology InnerProductSpace

namespace FSCProbes.TriangleVariation

open FSC FSCProbes.SingularTriangle FSCProbes.TriangleThreshold

def thresholdLine (t r : ℝ) : Coord 3 :=
  WeakSimplex.Coord.ofFun ![t, t, t + r]

def lineCDF (t r : ℝ) : ℝ := thresholdCDF gram (thresholdLine t r)

def lineSlope (t r : ℝ) : ℝ :=
  WeakSimplex.normalPDF (t + r) * WeakSimplex.normalCDF ((t - 4 * r) / 3)

def lineCurvature (t : ℝ) : ℝ :=
  -t * WeakSimplex.normalPDF t * WeakSimplex.normalCDF (t / 3) -
    (4 / 3 : ℝ) * WeakSimplex.normalPDF t * WeakSimplex.normalPDF (t / 3)

theorem thresholdLine_mem_activeRegion (t r : ℝ) (hr : -4 * t / 5 < r) :
    thresholdLine t r ∈ activeRegion := by
  simp [activeRegion, Set.mem_setOf_eq, thresholdLine,
    WeakSimplex.Coord.ofFun_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  linarith

theorem hasDerivAt_lineCDF (t r : ℝ) (hr : -4 * t / 5 < r) :
    HasDerivAt (lineCDF t) (lineSlope t r) r := by
  have h : HasDerivAt (fun z : ℝ ↦
      WeakSimplex.normalCDF t * WeakSimplex.normalCDF t - WeakSimplex.normalCDF t +
        bivariateCDF t (t + z)) (lineSlope t r) r := by
    convert! ((hasDerivAt_bivariateCDF_right t (t + r)).comp r
      ((hasDerivAt_id r).const_add t)).const_add
      (WeakSimplex.normalCDF t * WeakSimplex.normalCDF t - WeakSimplex.normalCDF t) using 1
    simp only [lineSlope, mul_one]
    congr 2
    ring
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hr] with z hz
  simpa [lineCDF, thresholdLine] using
    thresholdCDF_activeRegion (thresholdLine t z) (thresholdLine_mem_activeRegion t z hz)

theorem hasDerivAt_lineSlope_zero (t : ℝ) :
    HasDerivAt (lineSlope t) (lineCurvature t) 0 := by
  have hp := (WeakSimplex.hasDerivAt_normalPDF (t + 0)).comp 0
    ((hasDerivAt_id (0 : ℝ)).const_add t)
  have hc := (WeakSimplex.hasDerivAt_normalCDF ((t - 4 * 0) / 3)).comp 0
    (((hasDerivAt_id (0 : ℝ)).const_mul 4).const_sub t |>.div_const 3)
  convert! hp.mul hc using 1
  simp [lineCurvature]
  ring

def scalarHessian (t : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    (lineCurvature t • ContinuousLinearMap.id ℝ ℝ)

@[simp] theorem scalarHessian_apply (t y z : ℝ) :
    scalarHessian t y z = lineCurvature t * y * z := by
  simp [scalarHessian]
  ring

theorem peano2_lineCDF (t : ℝ) (ht : 0 < t) :
    Peano2 (lineCDF t) 0 (lineSlope t 0 • ContinuousLinearMap.id ℝ ℝ)
      (scalarHessian t) := by
  apply peano2_of_hasFDerivAt_derivative
    (f' := fun r ↦ lineSlope t r • ContinuousLinearMap.id ℝ ℝ)
  · filter_upwards [lt_mem_nhds (show -4 * t / 5 < (0 : ℝ) by linarith)] with r hr
    convert! (hasDerivAt_lineCDF t r hr).hasFDerivAt using 1
    ext
    simp [mul_comm]
  · convert! ((hasDerivAt_lineSlope_zero t).smul_const
      (ContinuousLinearMap.id ℝ ℝ)).hasFDerivAt using 1

theorem measurable_lineCDF (t : ℝ) : Measurable (lineCDF t) :=
  (measurable_thresholdCDF gram).comp (by
    apply Continuous.measurable
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop)

theorem bounded_lineCDF (t : ℝ) : ∃ M : ℝ, ∀ r, ‖lineCDF t r‖ ≤ M := by
  refine ⟨1, fun r ↦ ?_⟩
  unfold lineCDF
  rw [Real.norm_eq_abs, abs_of_nonneg (thresholdCDF_nonneg gram _)]
  exact thresholdCDF_le_one gram _

def drift (t s : ℝ) : ℝ := t * (Real.sqrt (1 + s) - 1)

@[simp] theorem drift_zero (t : ℝ) : drift t 0 = 0 := by simp [drift]

theorem hasDerivAt_drift_zero (t : ℝ) : HasDerivAt (drift t) (t / 2) 0 := by
  convert! ((((hasDerivAt_id (0 : ℝ)).const_add 1).sqrt (by norm_num)).sub_const 1).const_mul t using 1
  simp
  ring

theorem integral_sq_stdGaussianReal : ∫ y : ℝ, y ^ 2 ∂gaussianReal 0 1 = 1 := by
  rw [← variance_of_integral_eq_zero (by fun_prop) (by simp)]
  exact variance_fun_id_gaussianReal

theorem integrable_sq_stdGaussianReal :
    Integrable (fun y : ℝ ↦ ‖y‖ ^ 2) (gaussianReal 0 1) := by
  simpa only [Real.norm_eq_abs, sq_abs, id_eq] using
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq

theorem integral_scalarHessian (t : ℝ) :
    ∫ y : ℝ, scalarHessian t y y ∂gaussianReal 0 1 = lineCurvature t := by
  simp_rw [scalarHessian_apply, mul_assoc, ← pow_two]
  rw [integral_const_mul, integral_sq_stdGaussianReal, mul_one]

theorem hasDerivWithinAt_noiseAverage (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt
      (fun s ↦ ∫ y : ℝ, lineCDF t (drift t s + Real.sqrt s * y) ∂gaussianReal 0 1)
      (-(2 / 5 : ℝ) * q gram t 1 2) (Set.Ici 0) 0 := by
  have h := (peano2_lineCDF t ht).hasDerivWithinAt_noiseAverage
    (measurable_lineCDF t) (bounded_lineCDF t) (gaussianReal 0 1)
    (by simp) integrable_sq_stdGaussianReal (drift_zero t)
    (by simpa using (hasDerivAt_drift_zero t).tendsto_slope_zero_right)
  convert! h using 1
  · simp
  · rw [integral_scalarHessian, q_12 t ht]
    simp [lineSlope, lineCurvature]
    ring

def noiseCov : Mat 3 := !![0, 0, 0; 0, 0, 0; 0, 0, 1]

def noiseLoading : Matrix (Fin 3) (Fin 1) ℝ := !![0; 0; 1]

def noiseVector (z : ℝ) : Coord 3 := WeakSimplex.Coord.ofFun ![0, 0, z]

theorem noiseLoading_cov : noiseLoading * (1 : Mat 1) * noiseLoading.transpose = noiseCov := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [noiseLoading, noiseCov, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

theorem noiseCov_posSemidef : noiseCov.PosSemidef := by
  rw [← noiseLoading_cov]
  exact posSemidef_congruence 1 Matrix.PosSemidef.one noiseLoading

theorem map_real_to_coordOne :
    Measure.map (fun z : ℝ ↦ WeakSimplex.Coord.ofFun (fun _ : Fin 1 ↦ z))
      (gaussianReal 0 1) = stdGaussian (Coord 1) := by
  have heval : (stdGaussian (Coord 1)).map (fun x : Coord 1 ↦ x 0) =
      gaussianReal 0 1 := by
    simpa using (measurePreserving_eval_multivariateGaussian
      (μ := (0 : Coord 1)) (S := (1 : Mat 1)) Matrix.PosSemidef.one
      (i := (0 : Fin 1))).map_eq
  have hmeas : Measurable (fun z : ℝ ↦ WeakSimplex.Coord.ofFun (fun _ : Fin 1 ↦ z)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).measurable.comp
      (measurable_pi_lambda _ fun _ ↦ measurable_id)
  rw [← heval, Measure.map_map hmeas (by fun_prop)]
  have hid : (fun z : ℝ ↦ WeakSimplex.Coord.ofFun (fun _ : Fin 1 ↦ z)) ∘
      (fun x : Coord 1 ↦ x 0) = id := by
    funext x
    ext i
    change x 0 = x i
    rw [Subsingleton.elim (0 : Fin 1) i]
  rw [hid, Measure.map_id]

theorem map_noiseVector : (gaussianReal 0 1).map noiseVector =
    multivariateGaussian (0 : Coord 3) noiseCov := by
  have hcomp : noiseVector = (lin noiseLoading) ∘
      (fun z : ℝ ↦ WeakSimplex.Coord.ofFun (fun _ : Fin 1 ↦ z)) := by
    funext z
    ext i
    fin_cases i <;>
      simp [noiseVector, lin_apply, noiseLoading, Matrix.mulVec, dotProduct]
  have hmeas : Measurable (fun z : ℝ ↦ WeakSimplex.Coord.ofFun (fun _ : Fin 1 ↦ z)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).measurable.comp
      (measurable_pi_lambda _ fun _ ↦ measurable_id)
  rw [hcomp, ← Measure.map_map (lin noiseLoading).measurable hmeas, map_real_to_coordOne]
  simpa only [multivariateGaussian_zero_one, map_zero, noiseLoading_cov] using
    map_lin_multivariateGaussian (0 : Coord 1) 1 Matrix.PosSemidef.one noiseLoading

theorem continuous_noiseVector : Continuous noiseVector := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem map_add_scalarNoise (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (fun p : Coord 3 × ℝ ↦ p.1 - Real.sqrt s • noiseVector p.2)
      ((multivariateGaussian (0 : Coord 3) gram).prod (gaussianReal 0 1)) =
    multivariateGaussian (0 : Coord 3) (gram + s • noiseCov) := by
  have hcomp : (fun p : Coord 3 × ℝ ↦ p.1 - Real.sqrt s • noiseVector p.2) =
      (fun p : Coord 3 × Coord 3 ↦ (1 : ℝ) • p.1 + (-Real.sqrt s) • p.2) ∘
        Prod.map id noiseVector := by
    funext p
    simp [sub_eq_add_neg]
  rw [hcomp, ← Measure.map_map (by fun_prop)
    (measurable_id.prodMap continuous_noiseVector.measurable),
    ← Measure.map_prod_map _ _ measurable_id continuous_noiseVector.measurable,
    Measure.map_id, map_noiseVector,
    map_weighted_multivariateGaussian _ _ _ _ gram_isCorrelation.1 noiseCov_posSemidef]
  simp [Real.sq_sqrt hs]

def normalizer (s : ℝ) : Mat 3 :=
  !![1, 0, 0; 0, 1, 0; 0, 0, 1 / Real.sqrt (1 + s)]

theorem normalizer_cov (s : ℝ) :
    normalizer s * (gram + s • noiseCov) * (normalizer s).transpose =
      normalizedAdd gram noiseCov s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizer, normalizedAdd, gram, noiseCov, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ, div_eq_mul_inv] <;> ring

theorem map_normalizedNoise (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (fun p : Coord 3 × ℝ ↦
      lin (normalizer s) (p.1 - Real.sqrt s • noiseVector p.2))
      ((multivariateGaussian (0 : Coord 3) gram).prod (gaussianReal 0 1)) =
      multivariateGaussian (0 : Coord 3) (normalizedAdd gram noiseCov s) := by
  change Measure.map ((lin (normalizer s)) ∘
    (fun p : Coord 3 × ℝ ↦ p.1 - Real.sqrt s • noiseVector p.2)) _ = _
  have hmeas : Measurable (fun p : Coord 3 × ℝ ↦ p.1 - Real.sqrt s • noiseVector p.2) :=
    measurable_fst.sub (measurable_const.smul
      (continuous_noiseVector.measurable.comp measurable_snd))
  rw [← Measure.map_map (lin (normalizer s)).measurable hmeas,
    map_add_scalarNoise s hs]
  simpa only [map_zero, normalizer_cov] using map_lin_multivariateGaussian
    (0 : Coord 3) (gram + s • noiseCov)
    (gram_isCorrelation.1.add (noiseCov_posSemidef.smul hs)) (normalizer s)

theorem normalizedNoise_event (t s : ℝ) (hs : 0 ≤ s) (x : Coord 3) (y : ℝ) :
    lin (normalizer s) (x - Real.sqrt s • noiseVector y) ∈
      WeakSimplex.lowerOrthant t ↔
    x ∈ thresholdEvent (thresholdLine t (drift t s + Real.sqrt s * y)) := by
  have hpos : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.2 (by linarith)
  simp [WeakSimplex.lowerOrthant, thresholdEvent, Set.mem_setOf_eq, thresholdLine,
    lin_apply, normalizer, noiseVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Fin.forall_fin_succ]
  intro _ _
  rw [← mul_le_mul_iff_right₀ hpos]
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  rw [show Real.sqrt (1 + s) * Real.sqrt s * (Real.sqrt (1 + s))⁻¹ = Real.sqrt s by
    field_simp]
  unfold drift
  constructor <;> intro h <;> nlinarith

theorem cdf_normalizedAdd_eq_noiseAverage (t s : ℝ) (hs : 0 ≤ s) :
    cdf (normalizedAdd gram noiseCov s) t =
      ∫ y : ℝ, lineCDF t (drift t s + Real.sqrt s * y) ∂gaussianReal 0 1 := by
  classical
  let T : Coord 3 × ℝ → Coord 3 :=
    fun p ↦ lin (normalizer s) (p.1 - Real.sqrt s • noiseVector p.2)
  have hT : Measurable T := (lin (normalizer s)).measurable.comp
    (measurable_fst.sub (measurable_const.smul
      (continuous_noiseVector.measurable.comp measurable_snd)))
  let E := T ⁻¹' WeakSimplex.lowerOrthant t
  have hE : MeasurableSet E := (WeakSimplex.measurableSet_lowerOrthant t).preimage hT
  have hInt : Integrable (E.indicator (1 : Coord 3 × ℝ → ℝ))
      ((multivariateGaussian (0 : Coord 3) gram).prod (gaussianReal 0 1)) :=
    (integrable_const (1 : ℝ)).indicator hE
  rw [FSC.cdf, ← map_normalizedNoise s hs, Measure.map_apply hT
    (WeakSimplex.measurableSet_lowerOrthant t)]
  change (((multivariateGaussian (0 : Coord 3) gram).prod (gaussianReal 0 1)).real E) = _
  rw [← integral_indicator_one hE, integral_prod_symm _ hInt]
  apply integral_congr_ae
  filter_upwards with y
  have heq : (fun x : Coord 3 ↦ E.indicator (1 : Coord 3 × ℝ → ℝ) (x, y)) =
      (thresholdEvent (thresholdLine t (drift t s + Real.sqrt s * y))).indicator
        (1 : Coord 3 → ℝ) := by
    funext x
    have he : (x, y) ∈ E ↔
        x ∈ thresholdEvent (thresholdLine t (drift t s + Real.sqrt s * y)) :=
      normalizedNoise_event t s hs x y
    simp only [Set.indicator_apply, he, Pi.one_apply]
  rw [heq, integral_indicator_one (measurableSet_thresholdEvent _)]
  rfl

/-- Right derivative of the actual normalized PSD-addition CDF, with the canonical pair weight. -/
theorem hasDerivWithinAt_normalizedAdd (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt (fun s ↦ cdf (normalizedAdd gram noiseCov s) t)
      (-(2 / 5 : ℝ) * q gram t 1 2) (Set.Ici 0) 0 := by
  apply (hasDerivWithinAt_noiseAverage t ht).congr
  · intro s hs
    exact cdf_normalizedAdd_eq_noiseAverage t s hs
  · exact cdf_normalizedAdd_eq_noiseAverage t 0 le_rfl

theorem normalizedAdd_derivative_neg (t : ℝ) (ht : 0 < t) :
    -(2 / 5 : ℝ) * q gram t 1 2 < 0 :=
  mul_neg_of_neg_of_pos (by norm_num) (q_12_pos t ht)

theorem normalizedAdd_isCorrelation (s : ℝ) (hs : 0 ≤ s) :
    WeakSimplex.IsCorrelation (normalizedAdd gram noiseCov s) := by
  refine ⟨?_, fun i ↦ ?_⟩
  · rw [← normalizer_cov]
    exact posSemidef_congruence (gram + s • noiseCov)
      (gram_isCorrelation.1.add (noiseCov_posSemidef.smul hs)) (normalizer s)
  · have hsq : Real.sqrt (1 + s) * Real.sqrt (1 + s) = 1 + s :=
      Real.mul_self_sqrt (by linarith)
    fin_cases i <;> simp [normalizedAdd, gram, noiseCov, hsq, ne_of_gt (show 0 < 1 + s by linarith)]

theorem normalizedAdd_det (s : ℝ) (hs : 0 ≤ s) :
    (normalizedAdd gram noiseCov s).det = s / (1 + s) := by
  rw [← normalizer_cov, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hsq : Real.sqrt (1 + s) ^ 2 = 1 + s := Real.sq_sqrt (by linarith)
  norm_num [normalizer, gram, noiseCov, Matrix.det_fin_three, Matrix.cons_val_two]
  field_simp
  nlinarith

theorem normalizedAdd_rank (s : ℝ) (hs : 0 < s) :
    (normalizedAdd gram noiseCov s).rank = 3 := by
  have hdet : (normalizedAdd gram noiseCov s).det ≠ 0 := by
    rw [normalizedAdd_det s hs.le]
    positivity
  simpa using Matrix.rank_of_isUnit (normalizedAdd gram noiseCov s)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))

def triangleLoading : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; -3 / 5, 4 / 5]

theorem triangleLoading_cov : triangleLoading * triangleLoading.transpose = gram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleLoading, gram, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

theorem gram_rank_le_two : gram.rank ≤ 2 := by
  rw [← triangleLoading_cov]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width triangleLoading)

theorem gram_rank : gram.rank = 2 := by
  apply le_antisymm gram_rank_le_two
  have hsub : gram.submatrix Fin.castSucc Fin.castSucc = (1 : Mat 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [gram, Matrix.submatrix]
  have hr := Matrix.rank_submatrix_le gram (Fin.castSucc : Fin 2 → Fin 3) Fin.castSucc
  rw [hsub, Matrix.rank_one] at hr
  exact hr

theorem noiseCov_eq_outer :
    noiseCov = Matrix.vecMulVec (noiseVector 1) (noiseVector 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [noiseCov, noiseVector, Matrix.vecMulVec]

theorem noiseCov_rank : noiseCov.rank = 1 := by
  apply le_antisymm
  · rw [noiseCov_eq_outer]
    exact Matrix.rank_vecMulVec_le _ _
  · have hsub : noiseCov.submatrix (fun _ : Fin 1 ↦ 2) (fun _ : Fin 1 ↦ 2) =
        (1 : Mat 1) := by
      ext i j
      fin_cases i
      fin_cases j
      norm_num [noiseCov, Matrix.submatrix, Matrix.cons_val_two]
    have hr := Matrix.rank_submatrix_le noiseCov (fun _ : Fin 1 ↦ 2) (fun _ : Fin 1 ↦ 2)
    rw [hsub, Matrix.rank_one] at hr
    exact hr

@[simp] theorem normalizedAdd_zero : normalizedAdd gram noiseCov 0 = gram := by
  ext i j
  simp [normalizedAdd]

theorem normalizedAdd_rank_increases (s : ℝ) (hs : 0 < s) :
    gram.rank < (normalizedAdd gram noiseCov s).rank := by
  rw [normalizedAdd_rank s hs]
  exact lt_of_le_of_lt gram_rank_le_two (by norm_num)

end FSCProbes.TriangleVariation
