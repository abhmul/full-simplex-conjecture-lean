import FSC.Gaussian.SinglePin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! Canonical pair regression with explicit full-index residuals and an actual two-coordinate Gaussian pin. The definitions of the residual, pin mean, remaining event and weights are those frozen in `PinDefinitions.lean`. -/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace BigOperators ENNReal

namespace FSC

/-- Select the two actual source coordinates, in the stated order. -/
def pairProjection {n : ℕ} (i j : Fin n) : Matrix (Fin 2) (Fin n) ℝ :=
  ![Pi.single i 1, Pi.single j 1]

@[simp] theorem lin_pairProjection_zero {n : ℕ} (i j : Fin n) (x : Coord n) :
    lin (pairProjection i j) x 0 = x i := by
  simp [lin_apply, pairProjection, Matrix.mulVec]

@[simp] theorem lin_pairProjection_one {n : ℕ} (i j : Fin n) (x : Coord n) :
    lin (pairProjection i j) x 1 = x j := by
  simp [lin_apply, pairProjection, Matrix.mulVec]

theorem pair_regression_denominator {n : ℕ} (G : Mat n) (i j : Fin n)
    (hlo : -1 < G i j) (hhi : G i j < 1) : 1 - (G i j) ^ 2 ≠ 0 := by
  have hpos : 0 < (1 - G i j) * (1 + G i j) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem pair_regression_first {n : ℕ} (G : Mat n) (i j k : Fin n)
    (hc : 1 - (G i j) ^ 2 ≠ 0) :
    pairAlpha G i j k + pairBeta G i j k * G i j = G k i := by
  unfold pairAlpha pairBeta
  field_simp [hc]
  ring

theorem pair_regression_second {n : ℕ} (G : Mat n) (i j k : Fin n)
    (hc : 1 - (G i j) ^ 2 ≠ 0) :
    pairAlpha G i j k * G i j + pairBeta G i j k = G k j := by
  unfold pairAlpha pairBeta
  field_simp [hc]
  ring

@[simp] theorem lin_pairResidual_apply {n : ℕ} (G : Mat n) (i j : Fin n)
    (x : Coord n) (k : Fin n) :
    lin (pairResidual G i j) x k =
      x k - pairAlpha G i j k * x i - pairBeta G i j k * x j := by
  simp only [lin_apply, pairResidual, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib]
  simp

theorem pair_reconstruction {n : ℕ} (G : Mat n) (i j : Fin n) (x : Coord n) :
    pairMean G i j (x i) (x j) + lin (pairResidual G i j) x = x := by
  ext k
  change pairMean G i j (x i) (x j) k + lin (pairResidual G i j) x k = x k
  rw [lin_pairResidual_apply]
  simp only [pairMean, WeakSimplex.Coord.ofFun_apply]
  ring

theorem pairResidual_mul_apply {n : ℕ} (G : Mat n) (i j k l : Fin n) :
    (pairResidual G i j * G) k l =
      G k l - pairAlpha G i j k * G i l - pairBeta G i j k * G j l := by
  simp only [Matrix.mul_apply, pairResidual, sub_mul, Finset.sum_sub_distrib]
  simp

/-- Explicit residual covariance agrees with the canonical PSD congruence. -/
theorem pairCov_apply {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j k l : Fin n) (hc : 1 - (G i j) ^ 2 ≠ 0) :
    pairCov G i j k l =
      G k l - pairAlpha G i j k * G l i - pairBeta G i j k * G l j := by
  have hsym (a b : Fin n) : G a b = G b a := by
    simpa only [star_trivial] using hG.1.isHermitian.apply b a
  have htrans : (pairResidual G i j).transpose = 1 -
      Matrix.vecMulVec (Pi.single i 1) (pairAlpha G i j) -
      Matrix.vecMulVec (Pi.single j 1) (pairBeta G i j) := by
    ext a b
    simp [pairResidual, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.single_apply, eq_comm, mul_comm]
  have hzeroi : (pairResidual G i j * G) k i = 0 := by
    rw [pairResidual_mul_apply, hG.2 i, hsym j i, mul_one]
    linarith only [pair_regression_first G i j k hc]
  have hzeroj : (pairResidual G i j * G) k j = 0 := by
    rw [pairResidual_mul_apply, hG.2 j, mul_one]
    linarith only [pair_regression_second G i j k hc]
  unfold pairCov
  rw [htrans, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  change (pairResidual G i j * G) k l - (pairResidual G i j * G) k i * pairAlpha G i j l -
    (pairResidual G i j * G) k j * pairBeta G i j l = _
  rw [hzeroi, hzeroj, zero_mul, zero_mul, sub_zero, sub_zero, pairResidual_mul_apply,
    hsym i l, hsym j l]

/-- The sequential first-pin mean uses exactly the canonical pair coefficients. -/
theorem pairMean_sequential {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) (r s : ℝ) (hc : 1 - (G i j) ^ 2 ≠ 0) :
    pairMean G i j r s = singleMean G i r +
      ((s - G i j * r) / (1 - (G i j) ^ 2)) •
        WeakSimplex.Coord.ofFun (fun k ↦ singleCov G i k j) := by
  have hsym : G j i = G i j := by simpa only [star_trivial] using hG.1.isHermitian.apply i j
  ext k
  simp only [pairMean, pairAlpha, pairBeta, singleMean, singleCov,
    WeakSimplex.Coord.ofFun_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hsym]
  field_simp [hc]
  ring

/-- The actual sequential residual map agrees pointwise with the canonical two-pin residual. -/
theorem lin_pairResidual_sequential {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) (hc : 1 - (G i j) ^ 2 ≠ 0) (x : Coord n) (k : Fin n) :
    lin (pairResidual G i j) x k = lin (singleResidual G i) x k -
      (singleCov G i k j / (1 - (G i j) ^ 2)) * lin (singleResidual G i) x j := by
  have hsym : G j i = G i j := by simpa only [star_trivial] using hG.1.isHermitian.apply i j
  rw [lin_pairResidual_apply, lin_singleResidual_apply, lin_singleResidual_apply]
  simp only [pairAlpha, pairBeta, singleCov, hsym]
  field_simp [hc]
  ring

/-- Sequential residual covariance is the same full-index covariance used by pairLaw. -/
theorem pairCov_sequential {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) (hc : 1 - (G i j) ^ 2 ≠ 0) :
    pairCov G i j = fun k l ↦ singleCov G i k l -
      singleCov G i k j * singleCov G i l j / (1 - (G i j) ^ 2) := by
  have hsym : G j i = G i j := by simpa only [star_trivial] using hG.1.isHermitian.apply i j
  ext k l
  rw [pairCov_apply G hG i j k l hc]
  simp only [pairAlpha, pairBeta, singleCov, hsym]
  field_simp [hc]
  ring

theorem pair_coefficients_pinned {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i j : Fin n) (hc : 1 - (G i j) ^ 2 ≠ 0) :
    pairAlpha G i j i = 1 ∧ pairBeta G i j i = 0 ∧
      pairAlpha G i j j = 0 ∧ pairBeta G i j j = 1 := by
  have hsym : G j i = G i j := by simpa only [star_trivial] using hG.1.isHermitian.apply i j
  have hcc : 1 - G i j * G i j ≠ 0 := by simpa only [pow_two] using hc
  simp [pairAlpha, pairBeta, hG.2 i, hG.2 j, hsym, pow_two, hcc]

theorem pairResidual_pinned {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i j : Fin n) (hc : 1 - (G i j) ^ 2 ≠ 0)
    (x : Coord n) : lin (pairResidual G i j) x i = 0 ∧ lin (pairResidual G i j) x j = 0 := by
  obtain ⟨hai, hbi, haj, hbj⟩ := pair_coefficients_pinned G hG i j hc
  simp only [lin_pairResidual_apply, hai, hbi, haj, hbj, one_mul, zero_mul,
    sub_self, sub_zero, and_self]

theorem pairMean_common {n : ℕ} (G : Mat n) (i j k : Fin n) (t : ℝ)
    (hc : 1 - (G i j) ^ 2 ≠ 0) :
    pairMean G i j t t k = t * (G k i + G k j) / (1 + G i j) := by
  have hc1 : 1 + G i j ≠ 0 := by
    intro h
    apply hc
    nlinarith
  simp only [pairMean, WeakSimplex.Coord.ofFun_apply, pairAlpha, pairBeta]
  field_simp [hc, hc1]
  ring

theorem pairCov_posSemidef {n : ℕ} (G : Mat n) (hG : G.PosSemidef)
    (i j : Fin n) : (pairCov G i j).PosSemidef :=
  posSemidef_congruence G hG (pairResidual G i j)

theorem map_pairResidual {n : ℕ} (G : Mat n) (hG : G.PosSemidef)
    (i j : Fin n) :
    Measure.map (lin (pairResidual G i j)) (multivariateGaussian (0 : Coord n) G) =
      multivariateGaussian (0 : Coord n) (pairCov G i j) := by
  simpa only [map_zero, pairCov] using
    map_lin_multivariateGaussian (0 : Coord n) G hG (pairResidual G i j)

theorem map_pairMean_add {n : ℕ} (G : Mat n) (hG : G.PosSemidef)
    (i j : Fin n) (r s : ℝ) :
    Measure.map (fun x ↦ pairMean G i j r s + x)
      (multivariateGaussian (0 : Coord n) (pairCov G i j)) = pairLaw G i j r s := by
  have hone : (lin (1 : Mat n) : Coord n → Coord n) = id := by
    funext x
    ext k
    simp
  simpa only [hone, id_eq, add_zero, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one, pairLaw] using
    map_affine_multivariateGaussian (0 : Coord n) (pairCov G i j)
      (pairCov_posSemidef G hG i j) 1 (pairMean G i j r s)

/-- Both selected coordinates are fixed at every prescribed pair of real pin values. -/
theorem pairLaw_pin_ae {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i j : Fin n)
    (hc : 1 - (G i j) ^ 2 ≠ 0) (r s : ℝ) :
    ∀ᵐ x ∂pairLaw G i j r s, x i = r ∧ x j = s := by
  obtain ⟨hai, hbi, haj, hbj⟩ := pair_coefficients_pinned G hG i j hc
  rw [← map_pairMean_add G hG.1 i j r s, ← map_pairResidual G hG.1 i j,
    Measure.map_map (measurable_const_add (pairMean G i j r s)) (lin (pairResidual G i j)).measurable]
  apply (ae_map_iff (by fun_prop) ?_).2
  · apply Filter.Eventually.of_forall
    intro x
    obtain ⟨hxi, hxj⟩ := pairResidual_pinned G hG i j hc x
    change (pairMean G i j r s i + lin (pairResidual G i j) x i = r) ∧
      (pairMean G i j r s j + lin (pairResidual G i j) x j = s)
    simp [hxi, hxj, pairMean, hai, hbi, haj, hbj]
  · exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const)

theorem covariance_pairResidual_first {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i j k : Fin n)
    (hc : 1 - (G i j) ^ 2 ≠ 0) :
    cov[fun x : Coord n ↦ lin (pairResidual G i j) x k, fun x ↦ x i;
      multivariateGaussian (0 : Coord n) G] = 0 := by
  have hmem (l : Fin n) : MemLp (fun x : Coord n ↦ x l) 2
      (multivariateGaussian (0 : Coord n) G) := by
    exact IsGaussian.memLp_dual (multivariateGaussian (0 : Coord n) G)
      (EuclideanSpace.proj l) 2 (by simp)
  have hsym : G j i = G i j := by simpa only [star_trivial] using hG.1.isHermitian.apply i j
  simp_rw [lin_pairResidual_apply]
  change cov[(fun x : Coord n ↦ x k) - (fun x ↦ pairAlpha G i j k * x i) -
      (fun x ↦ pairBeta G i j k * x j), fun x ↦ x i;
      multivariateGaussian (0 : Coord n) G] = 0
  rw [covariance_sub_left ((hmem k).sub ((hmem i).const_mul (pairAlpha G i j k)))
      ((hmem j).const_mul (pairBeta G i j k)) (hmem i),
    covariance_sub_left (hmem k) ((hmem i).const_mul (pairAlpha G i j k)) (hmem i)]
  simp only [covariance_const_mul_left, covariance_eval_multivariateGaussian hG.1,
    hG.2 i, hsym, mul_one]
  linarith only [pair_regression_first G i j k hc]

theorem covariance_pairResidual_second {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i j k : Fin n)
    (hc : 1 - (G i j) ^ 2 ≠ 0) :
    cov[fun x : Coord n ↦ lin (pairResidual G i j) x k, fun x ↦ x j;
      multivariateGaussian (0 : Coord n) G] = 0 := by
  have hmem (l : Fin n) : MemLp (fun x : Coord n ↦ x l) 2
      (multivariateGaussian (0 : Coord n) G) := by
    exact IsGaussian.memLp_dual (multivariateGaussian (0 : Coord n) G)
      (EuclideanSpace.proj l) 2 (by simp)
  simp_rw [lin_pairResidual_apply]
  change cov[(fun x : Coord n ↦ x k) - (fun x ↦ pairAlpha G i j k * x i) -
      (fun x ↦ pairBeta G i j k * x j), fun x ↦ x j;
      multivariateGaussian (0 : Coord n) G] = 0
  rw [covariance_sub_left ((hmem k).sub ((hmem i).const_mul (pairAlpha G i j k)))
      ((hmem j).const_mul (pairBeta G i j k)) (hmem j),
    covariance_sub_left (hmem k) ((hmem i).const_mul (pairAlpha G i j k)) (hmem j)]
  simp only [covariance_const_mul_left, covariance_eval_multivariateGaussian hG.1,
    hG.2 j, mul_one]
  linarith only [pair_regression_second G i j k hc]

theorem pairProjection_covariance {n : ℕ} (G : Mat n) (i j : Fin n) :
    pairProjection i j * G * (pairProjection i j).transpose = G.submatrix ![i, j] ![i, j] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [pairProjection, Matrix.mul_apply, Matrix.submatrix, Pi.single_apply]

theorem map_pairProjection {n : ℕ} (G : Mat n) (hG : G.PosSemidef) (i j : Fin n) :
    Measure.map (lin (pairProjection i j)) (multivariateGaussian (0 : Coord n) G) =
      multivariateGaussian (0 : Coord 2) (G.submatrix ![i, j] ![i, j]) := by
  simpa only [map_zero, pairProjection_covariance] using
    map_lin_multivariateGaussian (0 : Coord n) G hG (pairProjection i j)

theorem pairResidual_indep_pin {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i j : Fin n)
    (hlo : -1 < G i j) (hhi : G i j < 1) :
    IndepFun (lin (pairResidual G i j)) (lin (pairProjection i j))
      (multivariateGaussian (0 : Coord n) G) := by
  have hc := pair_regression_denominator G i j hlo hhi
  have hjoint : HasGaussianLaw
      (fun x : Coord n ↦ (lin (pairResidual G i j) x, lin (pairProjection i j) x))
      (multivariateGaussian (0 : Coord n) G) :=
    IsGaussian.hasGaussianLaw_id.map
      ((lin (pairResidual G i j)).prod (lin (pairProjection i j)))
  have hcross (k : Fin n) (a : Fin 2) :
      cov[fun x : Coord n ↦ lin (pairResidual G i j) x k,
        fun x ↦ lin (pairProjection i j) x a; multivariateGaussian (0 : Coord n) G] = 0 := by
    fin_cases a
    · simpa [lin_apply, pairProjection, Matrix.mulVec] using covariance_pairResidual_first G hG i j k hc
    · simpa [lin_apply, pairProjection, Matrix.mulVec] using covariance_pairResidual_second G hG i j k hc
  apply hjoint.indepFun_of_covariance_inner
  intro u v
  have hmemR (k : Fin n) : MemLp (fun x : Coord n ↦ lin (pairResidual G i j) x k) 2
      (multivariateGaussian (0 : Coord n) G) :=
    IsGaussian.memLp_two_id.continuousLinearMap_comp
      ((EuclideanSpace.proj k).comp (lin (pairResidual G i j)))
  have hmemQ (a : Fin 2) : MemLp (fun x : Coord n ↦ lin (pairProjection i j) x a) 2
      (multivariateGaussian (0 : Coord n) G) :=
    IsGaussian.memLp_two_id.continuousLinearMap_comp
      ((EuclideanSpace.proj a).comp (lin (pairProjection i j)))
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [covariance_fun_sum_fun_sum (fun k ↦ (hmemR k).mul_const (u k))
    (fun a ↦ (hmemQ a).mul_const (v a))]
  simp only [covariance_mul_const_left, covariance_mul_const_right, hcross,
    zero_mul, Finset.sum_const_zero]

/-- Exact product of the full-index residual law and the actual two-coordinate pin law. -/
theorem map_pairResidual_pin {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i j : Fin n)
    (hlo : -1 < G i j) (hhi : G i j < 1) :
    Measure.map (fun x : Coord n ↦ (lin (pairResidual G i j) x, lin (pairProjection i j) x))
      (multivariateGaussian (0 : Coord n) G) =
      (multivariateGaussian (0 : Coord n) (pairCov G i j)).prod
        (multivariateGaussian (0 : Coord 2) (G.submatrix ![i, j] ![i, j])) := by
  rw [(pairResidual_indep_pin G hG i j hlo hhi).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop), map_pairResidual G hG.1 i j, map_pairProjection G hG.1 i j]

/-- Fubini integrates the explicit canonical laws at arbitrary two-coordinate pin values. -/
theorem lintegral_pairPin {n : ℕ} (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (i j : Fin n)
    (hlo : -1 < G i j) (hhi : G i j < 1)
    (f : Coord n × Coord 2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Coord n, f (x, lin (pairProjection i j) x)
      ∂multivariateGaussian (0 : Coord n) G) =
      ∫⁻ t : Coord 2, ∫⁻ y : Coord n, f (y, t) ∂pairLaw G i j (t 0) (t 1)
        ∂multivariateGaussian (0 : Coord 2) (G.submatrix ![i, j] ![i, j]) := by
  let H : Coord n × Coord 2 → ℝ≥0∞ := fun p ↦ f (pairMean G i j (p.2 0) (p.2 1) + p.1, p.2)
  have hH : Measurable H := by
    apply hf.comp
    dsimp [pairMean, WeakSimplex.Coord.ofFun]
    fun_prop
  calc
    (∫⁻ x : Coord n, f (x, lin (pairProjection i j) x)
        ∂multivariateGaussian (0 : Coord n) G) =
      ∫⁻ x : Coord n, H (lin (pairResidual G i j) x, lin (pairProjection i j) x)
        ∂multivariateGaussian (0 : Coord n) G := by
      apply lintegral_congr
      intro x
      simp only [H, lin_pairProjection_zero, lin_pairProjection_one, pair_reconstruction]
    _ = ∫⁻ p, H p ∂Measure.map
        (fun x : Coord n ↦ (lin (pairResidual G i j) x, lin (pairProjection i j) x))
        (multivariateGaussian (0 : Coord n) G) := (lintegral_map hH (by fun_prop)).symm
    _ = ∫⁻ p, H p ∂(multivariateGaussian (0 : Coord n) (pairCov G i j)).prod
        (multivariateGaussian (0 : Coord 2) (G.submatrix ![i, j] ![i, j])) := by
      rw [map_pairResidual_pin G hG i j hlo hhi]
    _ = ∫⁻ t : Coord 2, ∫⁻ r : Coord n, f (pairMean G i j (t 0) (t 1) + r, t)
        ∂multivariateGaussian (0 : Coord n) (pairCov G i j)
        ∂multivariateGaussian (0 : Coord 2) (G.submatrix ![i, j] ![i, j]) :=
      lintegral_prod_symm' H hH
    _ = ∫⁻ t : Coord 2, ∫⁻ y : Coord n, f (y, t) ∂pairLaw G i j (t 0) (t 1)
        ∂multivariateGaussian (0 : Coord 2) (G.submatrix ![i, j] ![i, j]) := by
      apply lintegral_congr
      intro t
      rw [← map_pairMean_add G hG.1 i j (t 0) (t 1)]
      have hft : Measurable (fun y : Coord n ↦ f (y, t)) :=
        hf.comp (measurable_id.prodMk measurable_const)
      exact (lintegral_map hft (measurable_const_add (pairMean G i j (t 0) (t 1)))).symm

end FSC
