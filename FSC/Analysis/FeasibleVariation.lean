import FSC.Gaussian.NormalizedAddition
import FSC.Gaussian.PinDefinitions
import FSC.Analysis.NoiseAveraging
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Generic normalized-addition derivatives from a genuine explicit threshold Peano expansion.
This module does not assert that every threshold CDF has that expansion.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

namespace FSC

def normalizationVelocity {n : ℕ} (L : Mat n) (t : ℝ) : Coord n :=
  WeakSimplex.Coord.ofFun (fun i ↦ t * L i i / 2)

theorem hasDerivAt_normalizationShift_zero {n : ℕ} (L : Mat n) (t : ℝ) :
    HasDerivAt (normalizationShift L t) (normalizationVelocity L t) 0 := by
  have hp : HasDerivAt (fun s : ℝ ↦ fun i : Fin n ↦
      t * (Real.sqrt (1 + s * L i i) - 1)) (fun i : Fin n ↦ t * L i i / 2) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    convert! (((((hasDerivAt_id (0 : ℝ)).mul_const (L i i)).const_add 1).sqrt
      (by simp)).sub_const 1).const_mul t using 1
    simp
    ring
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0 hp

theorem integrable_sq_norm_multivariateGaussian {n : ℕ} (μ : Coord n) (L : Mat n) :
    Integrable (fun y : Coord n ↦ ‖y‖ ^ 2) (multivariateGaussian μ L) := by
  exact (memLp_two_iff_integrable_sq_norm (by fun_prop)).mp IsGaussian.memLp_two_id

theorem integral_eval_multivariateGaussian_zero {n : ℕ} (L : Mat n) (i : Fin n) :
    ∫ y : Coord n, y i ∂multivariateGaussian (0 : Coord n) L = 0 := by
  simpa using (EuclideanSpace.proj i).integral_comp_id_comm
    (μ := multivariateGaussian (0 : Coord n) L) IsGaussian.integrable_id

theorem integrable_eval_mul_multivariateGaussian {n : ℕ} (L : Mat n) (i j : Fin n) :
    Integrable (fun y : Coord n ↦ y i * y j) (multivariateGaussian (0 : Coord n) L) := by
  have hi : MemLp (fun y : Coord n ↦ y i) 2 (multivariateGaussian (0 : Coord n) L) := by
    simpa only [Function.comp_def, id_eq, EuclideanSpace.coe_proj] using!
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i).comp_memLp'
        (IsGaussian.memLp_two_id (μ := multivariateGaussian (0 : Coord n) L))
  have hj : MemLp (fun y : Coord n ↦ y j) 2 (multivariateGaussian (0 : Coord n) L) := by
    simpa only [Function.comp_def, id_eq, EuclideanSpace.coe_proj] using!
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) j).comp_memLp'
        (IsGaussian.memLp_two_id (μ := multivariateGaussian (0 : Coord n) L))
  exact hi.integrable_mul hj

theorem integral_eval_mul_multivariateGaussian {n : ℕ} (L : Mat n)
    (hL : L.PosSemidef) (i j : Fin n) :
    ∫ y : Coord n, y i * y j ∂multivariateGaussian (0 : Coord n) L = L i j := by
  simpa only [covariance, integral_eval_multivariateGaussian_zero, sub_zero] using
    covariance_eval_multivariateGaussian (μ := (0 : Coord n)) hL i j

/-- Second moments contract every continuous bilinear form with the actual PSD covariance. -/
theorem integral_bilinear_multivariateGaussian {n : ℕ} (L : Mat n) (hL : L.PosSemidef)
    (B : Coord n →L[ℝ] Coord n →L[ℝ] ℝ) :
    ∫ y : Coord n, B y y ∂multivariateGaussian (0 : Coord n) L =
      ∑ i, ∑ j, L i j * B (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  have hexp (y : Coord n) : B y y =
      ∑ i, ∑ j, (y i * y j) * B (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply, Finset.mul_sum, smul_eq_mul,
      EuclideanSpace.basisFun_repr]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, integral_eval_mul_multivariateGaussian L hL i j]
    · intro j _
      exact (integrable_eval_mul_multivariateGaussian L i j).mul_const _
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact (integrable_eval_mul_multivariateGaussian L i j).mul_const _

/-- A genuine Peano expansion discharges the analytic premise of normalized Gaussian averaging.
The later threshold-calculus producer must supply `hp` before the universal FSC derivative is closed.
-/
theorem Peano2.hasDerivWithinAt_cdf_normalizedAdd {n : ℕ} {G L : Mat n} {t : ℝ}
    {l : Coord n →L[ℝ] ℝ} {B : Coord n →L[ℝ] Coord n →L[ℝ] ℝ}
    (hp : Peano2 (thresholdCDF G) (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) l B)
    (hG : G.PosSemidef) (hL : L.PosSemidef) :
    HasDerivWithinAt (fun s ↦ cdf (normalizedAdd G L s) t)
      (l (normalizationVelocity L t) +
        (1 / 2 : ℝ) * ∫ y : Coord n, B y y ∂multivariateGaussian (0 : Coord n) L)
      (Set.Ici 0) 0 := by
  have hb : ∃ M : ℝ, ∀ b, ‖thresholdCDF G b‖ ≤ M := by
    refine ⟨1, fun b ↦ ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (thresholdCDF_nonneg G b)]
    exact thresholdCDF_le_one G b
  have havg := hp.hasDerivWithinAt_noiseAverage (measurable_thresholdCDF G) hb
    (multivariateGaussian (0 : Coord n) L) (by simp)
    (integrable_sq_norm_multivariateGaussian 0 L) (normalizationShift_zero L t)
    (by simpa using (hasDerivAt_normalizationShift_zero L t).tendsto_slope_zero_right)
  apply havg.congr
  · intro s hs
    exact cdf_normalizedAdd_eq_noiseAverage G L hG hL t s hs
  · exact cdf_normalizedAdd_eq_noiseAverage G L hG hL t 0 le_rfl

theorem apply_normalizationVelocity {n : ℕ} (L : Mat n) (t : ℝ) (l : Coord n →L[ℝ] ℝ) :
    l (normalizationVelocity L t) =
      (1 / 2 : ℝ) * ∑ i, t * L i i * l (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (normalizationVelocity L t), map_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [EuclideanSpace.basisFun_repr, normalizationVelocity]
  ring

theorem sum_mul_covariance_eq_trace {n : ℕ} (L M : Mat n) (hL : L.PosSemidef) :
    (∑ i, ∑ j, L i j * M i j) = Matrix.trace (M * L) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsym : L j i = L i j := by
    simpa using congrFun (congrFun hL.isHermitian.eq i) j
  rw [hsym, mul_comm]

/-- Exact normalization cancellation once the actual threshold Hessian has been identified.
Both the Peano expansion and its displayed Hessian identity remain explicit hypotheses here.
-/
theorem Peano2.hasDerivWithinAt_cdf_normalizedAdd_of_hessian {n : ℕ} {G L : Mat n} {t : ℝ}
    {l : Coord n →L[ℝ] ℝ} {B : Coord n →L[ℝ] Coord n →L[ℝ] ℝ}
    (hp : Peano2 (thresholdCDF G) (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) l B)
    (hG : G.PosSemidef) (hL : L.PosSemidef)
    (hB : ∀ i j, B (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) = stress G t i j -
        if i = j then t * l (EuclideanSpace.basisFun (Fin n) ℝ i) else 0) :
    HasDerivWithinAt (fun s ↦ cdf (normalizedAdd G L s) t)
      ((1 / 2 : ℝ) * Matrix.trace (stress G t * L)) (Set.Ici 0) 0 := by
  convert! hp.hasDerivWithinAt_cdf_normalizedAdd hG hL using 1
  rw [apply_normalizationVelocity, integral_bilinear_multivariateGaussian L hL]
  simp_rw [hB, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sum_mul_covariance_eq_trace L (stress G t) hL]
  have heq : (∑ i, L i i * (t * l (EuclideanSpace.basisFun (Fin n) ℝ i))) =
      ∑ i, t * L i i * l (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  ring

end FSC
