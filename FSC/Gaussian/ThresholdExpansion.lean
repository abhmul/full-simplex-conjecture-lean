import FSC.Gaussian.ConditionalCaps
import FSC.Gaussian.PairWeights
import FSC.Analysis.FeasibleVariation
import FSC.Analysis.PeanoTaylor

/-! Local threshold calculus at common positive thresholds for distinct PSD correlation scores. -/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Topology BigOperators ContDiff Classical

namespace FSC

def thresholdGradient {n : ℕ} (G : Mat n) (b : Coord n) : Coord n →L[ℝ] ℝ :=
  ∑ i, (WeakSimplex.normalPDF (b i) * sliceMass (gramVectors G) (fun k ↦ b k) i) •
    EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i

theorem thresholdGradient_eq_supportGradient {n : ℕ} (G : Mat n) (b : Coord n) :
    thresholdGradient G b =
      (supportGradient (gramVectors G) (fun k ↦ b k)).comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap := by
  ext h
  simp [thresholdGradient, supportGradient, mul_comm]

theorem hasFDerivAt_thresholdCDF {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (b : Coord n) (hb : NoCoincident (gramVectors G) (fun k ↦ b k)) :
    HasFDerivAt (thresholdCDF G) (thresholdGradient G b) b := by
  rw [thresholdGradient_eq_supportGradient]
  have hc := (hasFDerivAt_capMass (gramVectors G) (norm_gramVectors G hG) _ hb).comp b
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap.hasFDerivAt
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun c ↦ thresholdCDF_eq_capMass_gram G hG.1 c

theorem eventually_hasFDerivAt_thresholdCDF {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) :
    ∀ᶠ b in 𝓝 (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)),
      HasFDerivAt (thresholdCDF G) (thresholdGradient G b) b := by
  have he := (noCoincident_gramVectors G hG hDistinct t ht).eventually
  have htend := (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ)).tendsto
    (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t))
  filter_upwards [htend.eventually he] with b hb
  exact hasFDerivAt_thresholdCDF G hG b hb

theorem contDiff_normalPDF (m : ℕ∞ω) : ContDiff ℝ m WeakSimplex.normalPDF := by
  unfold WeakSimplex.normalPDF gaussianPDFReal
  fun_prop

theorem contDiffAt_thresholdGradient {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ 1 (thresholdGradient G) (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) := by
  apply ContDiffAt.sum
  intro i _
  have hc : ContDiffAt ℝ 1 (fun b : Coord n ↦ WeakSimplex.normalPDF (b i) *
      sliceMass (gramVectors G) (fun k ↦ b k) i)
      (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) :=
    ((contDiff_normalPDF 1).contDiffAt.comp _ (by fun_prop)).mul
      (contDiffAt_sliceMass_gram G hG hDistinct i t ht)
  convert! hc.smul (g := fun _ : Coord n ↦ EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)
    contDiffAt_const using 1

theorem contDiffAt_two_thresholdCDF {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ 2 (thresholdCDF G) (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨thresholdGradient G, ?_, contDiffAt_thresholdGradient G hG hDistinct t ht⟩
  exact ⟨_, eventually_hasFDerivAt_thresholdCDF G hG hDistinct t ht, fun _ h ↦ h⟩

/-- Full vector-domain Peano expansion from the two actual support-C1 applications. -/
theorem peano2_thresholdCDF {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) :
    Peano2 (thresholdCDF G) (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t))
      (thresholdGradient G (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)))
      (fderiv ℝ (thresholdGradient G) (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t))) := by
  exact peano2_of_hasFDerivAt_derivative
    (eventually_hasFDerivAt_thresholdCDF G hG hDistinct t ht)
    ((contDiffAt_thresholdGradient G hG hDistinct t ht).differentiableAt (by norm_num)).hasFDerivAt

theorem hasDerivAt_commonThreshold {n : ℕ} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ s))
      (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ (1 : ℝ))) t := by
  convert! (hasDerivAt_id t).smul_const (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ (1 : ℝ))) using 1
  · funext s
    ext i
    simp
  · simp

theorem hasDerivAt_cdf {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (cdf G) (boundarySlope G t) t := by
  have h := (hasFDerivAt_thresholdCDF G hG _ (noCoincident_gramVectors G hG hDistinct t ht)).comp_hasDerivAt t (hasDerivAt_commonThreshold t)
  convert! h using 1
  simp [thresholdGradient, boundarySlope, sliceMass_gram_eq_singlePinMass G hG, Finset.mul_sum]

theorem sum_retained_q {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) (f : Fin n → ℝ) :
    (∑ j : RetainedPair G i, q G t i j * f j) = ∑ j : Fin n, q G t i j * f j := by
  let p : Fin n → Prop := fun j ↦ j ≠ i ∧ -1 < G i j ∧ G i j < 1
  have h := Fintype.sum_subtype_add_sum_subtype p (fun j ↦ q G t i j * f j)
  have hz : (∑ j : {j // ¬p j}, q G t i j * f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [q, if_neg (by
      intro hq
      exact j.property ⟨Ne.symm hq.1, hq.2⟩), zero_mul]
  simpa only [hz, add_zero] using h

theorem supportGradient_normalized_q {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (t : ℝ) (ht : 0 < t) (h : Coord n) :
    WeakSimplex.normalPDF t *
      (supportGradient (projectedNormal G i) (fun j ↦ pairSupport G t i j))
        (conditionalSupportMap G i h) =
      ∑ j : Fin n, q G t i j * (h j - G i j * h i) := by
  rw [← sum_retained_q]
  simp only [supportGradient, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.mul_sum,
    conditionalSupportMap_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [q_eq_projected_slice G hG hDistinct i j t ht]
  unfold conditionalSupport
  ring

def thresholdRowDerivative {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) : Coord n →L[ℝ] ℝ :=
  (-t * WeakSimplex.normalPDF t * singlePinMass G t i) •
    EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i +
    ∑ j : Fin n, q G t i j • (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) j -
      G i j • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)

theorem hasFDerivAt_thresholdCoefficient {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (t : ℝ) (ht : 0 < t) :
    HasFDerivAt (fun b : Coord n ↦ WeakSimplex.normalPDF (b i) *
      sliceMass (gramVectors G) (fun k ↦ b k) i)
      (thresholdRowDerivative G t i) (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) := by
  have hp : HasFDerivAt (fun b : Coord n ↦ WeakSimplex.normalPDF (b i))
      ((-t * WeakSimplex.normalPDF t) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)
      (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) := by
    convert! (WeakSimplex.hasDerivAt_normalPDF t).comp_hasFDerivAt
      (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t))
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i).hasFDerivAt using 1
  have hs := hasFDerivAt_sliceMass_gram G hG hDistinct i t ht
  convert! hp.mul hs using 1
  ext h
  simp only [thresholdRowDerivative, add_apply, smul_apply, sum_apply,
    EuclideanSpace.coe_proj, ContinuousLinearMap.comp_apply, smul_eq_mul,
    WeakSimplex.Coord.ofFun_apply, funext (conditionalSupport_common G i t),
    sliceMass_gram_eq_singlePinMass G hG, sub_apply]
  rw [supportGradient_normalized_q G hG hDistinct i t ht]
  ring

@[simp] theorem thresholdGradient_basis {n : ℕ} (G : Mat n) (b : Coord n) (j : Fin n) :
    thresholdGradient G b (EuclideanSpace.basisFun (Fin n) ℝ j) =
      WeakSimplex.normalPDF (b j) * sliceMass (gramVectors G) (fun k ↦ b k) j := by
  simp [thresholdGradient, EuclideanSpace.basisFun_apply, PiLp.single_apply]

theorem thresholdRowDerivative_apply {n : ℕ} (G : Mat n) (t : ℝ) (i : Fin n) (h : Coord n) :
    thresholdRowDerivative G t i h =
      (-t * WeakSimplex.normalPDF t * singlePinMass G t i) * h i +
        (∑ j, q G t i j * h j) - (∑ j, G i j * q G t i j) * h i := by
  simp only [thresholdRowDerivative, add_apply, smul_apply, sum_apply, sub_apply,
    EuclideanSpace.coe_proj, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  have he : (∑ j, q G t i j * (G i j * h i)) = ∑ j, G i j * q G t i j * h i := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

theorem thresholdRowDerivative_basis {n : ℕ} (G : Mat n) (t : ℝ) (i j : Fin n) :
    thresholdRowDerivative G t i (EuclideanSpace.basisFun (Fin n) ℝ j) =
      stress G t i j - if i = j then t * WeakSimplex.normalPDF t * singlePinMass G t i else 0 := by
  rw [thresholdRowDerivative_apply]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsum : (∑ k : Fin n, G i k * q G t i k) =
      ∑ k ∈ Finset.univ.erase i, G i k * q G t i k := by
    simp
  by_cases hij : i = j
  · subst j
    simp only [ite_true, q_self, add_zero]
    rw [hsum]
    simp only [stress, ite_true]
    ring
  · simp [stress, hij]

theorem thresholdHessian_apply {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) (i j : Fin n) :
    fderiv ℝ (thresholdGradient G) (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t))
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) =
      stress G t i j - if i = j then t * thresholdGradient G
        (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) (EuclideanSpace.basisFun (Fin n) ℝ i) else 0 := by
  have hg := ((contDiffAt_thresholdGradient G hG hDistinct t ht).differentiableAt (by norm_num)).hasFDerivAt
  have he := hg.clm_apply (hasFDerivAt_const (EuclideanSpace.basisFun (Fin n) ℝ j)
    (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)))
  simp only [thresholdGradient_basis, ContinuousLinearMap.comp_zero, zero_add] at he
  have hu := he.unique (hasFDerivAt_thresholdCoefficient G hG hDistinct j t ht)
  have hv := congrArg (fun A : Coord n →L[ℝ] ℝ ↦ A (EuclideanSpace.basisFun (Fin n) ℝ i)) hu
  rw [thresholdRowDerivative_basis] at hv
  simp only [ContinuousLinearMap.flip_apply] at hv
  rw [hv]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, thresholdGradient_basis, WeakSimplex.Coord.ofFun_apply,
      sliceMass_gram_eq_singlePinMass G hG, mul_assoc]
  · simp [stress, hij, Ne.symm hij, q_symm G hG j i t]

/-- Universal singular normalized PSD-addition right derivative, with every analytic input proved. -/
theorem hasDerivWithinAt_normalizedAdd {n : ℕ} (G L : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (hL : L.PosSemidef) (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt (fun s ↦ cdf (normalizedAdd G L s) t)
      ((1 / 2 : ℝ) * Matrix.trace (stress G t * L)) (Set.Ici 0) 0 := by
  exact (peano2_thresholdCDF G hG hDistinct t ht).hasDerivWithinAt_cdf_normalizedAdd_of_hessian
    hG.1 hL (thresholdHessian_apply G hG hDistinct t ht)

end FSC
