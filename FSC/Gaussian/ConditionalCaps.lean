import FSC.Gaussian.ProjectedNormals
import FSC.Gaussian.PairLaw

/-! Actual physical Gaussian slices as retained normalized caps and canonical pair laws. -/

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Topology Classical

namespace FSC

theorem measurable_gramScore {n : ℕ} (G : Mat n) :
    Measurable (fun z : Coord n ↦ WeakSimplex.Coord.ofFun fun i ↦ inner ℝ (gramVectors G i) z) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).measurable.comp
  exact measurable_pi_lambda _ fun i ↦ (continuous_const.inner continuous_id).measurable

theorem thresholdCDF_eq_capMass_gram {n : ℕ} (G : Mat n) (hG : G.PosSemidef) (b : Coord n) :
    thresholdCDF G b = capMass (gramVectors G) (fun i ↦ b i) := by
  rw [thresholdCDF, ← map_gramVectors_stdGaussian G hG,
    Measure.map_apply (measurable_gramScore G) (measurableSet_thresholdEvent b)]
  rfl

theorem inner_gram_slice {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i k : Fin n) (r : ℝ) (y : Coord n) :
    inner ℝ (gramVectors G k) (r • gramVectors G i + normalResidual (gramVectors G i) y) =
      r * G i k + inner ℝ (gramVectors G k - G i k • gramVectors G i) y := by
  simp only [normalResidual_apply, inner_add_right, inner_sub_right, real_inner_smul_right,
    inner_sub_left, real_inner_smul_left, inner_gramVectors G hG.1,
    correlation_entry_symm G hG.1 i]
  ring

theorem inner_gram_slice_retained {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) (j : RetainedPair G i) (r : ℝ) (y : Coord n) :
    inner ℝ (gramVectors G j) (r • gramVectors G i + normalResidual (gramVectors G i) y) =
      r * G i j + pairSigma G i j * inner ℝ (projectedNormal G i j) y := by
  rw [inner_gram_slice G hG, ← projectedNormal_reconstruct G i j, real_inner_smul_left]

theorem inner_gram_slice_antipode {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i k : Fin n) (hk : G i k = -1) (r : ℝ) (y : Coord n) :
    inner ℝ (gramVectors G k) (r • gramVectors G i + normalResidual (gramVectors G i) y) = -r := by
  have hv : gramVectors G k = -gramVectors G i :=
    (gramVectors_eq_neg_iff G hG k i).mpr ((correlation_entry_symm G hG.1 i k).trans hk)
  rw [inner_gram_slice G hG, hk, hv]
  simp

def AntipodesAutomatic {n : ℕ} (G : Mat n) (i : Fin n) (b : Coord n) : Prop :=
  ∀ k, G i k = -1 → -b i ≤ b k

theorem antipodesAutomatic_eventually {n : ℕ} (G : Mat n) (i : Fin n)
    (t : ℝ) (ht : 0 < t) :
    ∀ᶠ b in 𝓝 (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)), AntipodesAutomatic G i b := by
  have he : ∀ k : Fin n, ∀ᶠ b in 𝓝 (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)), -b i < b k := by
    intro k
    apply IsOpen.mem_nhds (isOpen_lt (by fun_prop) (by fun_prop))
    change -t < t
    linarith
  filter_upwards [Filter.eventually_all.mpr he] with b hb
  exact fun k _ ↦ (hb k).le

theorem slicePreimage_gram_eq_cap {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (b : Coord n) (hb : AntipodesAutomatic G i b) :
    slicePreimage (gramVectors G) (fun k ↦ b k) i =
      cap (projectedNormal G i) (conditionalSupport G i b) := by
  ext y
  change (∀ k, k ≠ i → inner ℝ (gramVectors G k)
    (b i • gramVectors G i + normalResidual (gramVectors G i) y) ≤ b k) ↔ _
  constructor
  · intro h j
    have hj := h j j.property.1
    rw [inner_gram_slice_retained G hG i j] at hj
    rw [conditionalSupport, le_div_iff₀ (retained_sigma_pos G i j)]
    nlinarith only [hj]
  · intro h k hki
    by_cases hanti : G i k = -1
    · rw [inner_gram_slice_antipode G hG i k hanti]
      exact hb k hanti
    · have hk : -1 < G i k := lt_of_le_of_ne (correlation_entry_bounds G hG i k).1 (Ne.symm hanti)
      let j : RetainedPair G i := ⟨k, hki, hk, hDistinct i k (Ne.symm hki)⟩
      have hj := h j
      rw [conditionalSupport, le_div_iff₀ (retained_sigma_pos G i j)] at hj
      have he := inner_gram_slice_retained G hG i j (b i) y
      change inner ℝ (gramVectors G k) _ = _ at he
      rw [he]
      nlinarith only [hj]

theorem sliceMass_gram_eq_capMass {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (b : Coord n) (hb : AntipodesAutomatic G i b) :
    sliceMass (gramVectors G) (fun k ↦ b k) i =
      capMass (projectedNormal G i) (conditionalSupport G i b) := by
  rw [sliceMass_eq_stdGaussian, slicePreimage_gram_eq_cap G hG hDistinct i b hb]
  rfl

def conditionalSupportMap {n : ℕ} (G : Mat n) (i : Fin n) : Coord n →L[ℝ] (RetainedPair G i → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ (pairSigma G i j)⁻¹ •
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) j -
      G i j • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)

@[simp] theorem conditionalSupportMap_apply {n : ℕ} (G : Mat n) (i : Fin n) (b : Coord n) :
    conditionalSupportMap G i b = conditionalSupport G i b := by
  funext j
  simp [conditionalSupportMap, conditionalSupport, div_eq_mul_inv, mul_comm]

theorem conditionalSupportMap_coe {n : ℕ} (G : Mat n) (i : Fin n) :
    (conditionalSupportMap G i : Coord n → RetainedPair G i → ℝ) = conditionalSupport G i :=
  funext (conditionalSupportMap_apply G i)

theorem contDiff_conditionalSupport {n : ℕ} (G : Mat n) (i : Fin n) :
    ContDiff ℝ 1 (conditionalSupport G i) := by
  rw [← conditionalSupportMap_coe]
  exact (conditionalSupportMap G i).contDiff

theorem contDiffAt_sliceMass_gram {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ 1 (fun b : Coord n ↦ sliceMass (gramVectors G) (fun k ↦ b k) i)
      (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) := by
  have hc := (contDiffAt_one_capMass (projectedNormal G i) (norm_projectedNormal G hG i)
    _ (noCoincident_conditionalSupport G hG hDistinct i t ht)).comp
      (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) (contDiff_conditionalSupport G i).contDiffAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [antipodesAutomatic_eventually G i t ht] with b hb
  exact sliceMass_gram_eq_capMass G hG hDistinct i b hb

theorem hasFDerivAt_sliceMass_gram {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (t : ℝ) (ht : 0 < t) :
    HasFDerivAt (fun b : Coord n ↦ sliceMass (gramVectors G) (fun k ↦ b k) i)
      ((supportGradient (projectedNormal G i)
        (conditionalSupport G i (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)))).comp
        (conditionalSupportMap G i))
      (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) := by
  have hm : HasFDerivAt (conditionalSupport G i) (conditionalSupportMap G i)
      (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) := by
    rw [← conditionalSupportMap_coe]
    exact (conditionalSupportMap G i).hasFDerivAt
  have hc := (hasFDerivAt_capMass (projectedNormal G i) (norm_projectedNormal G hG i)
    _ (noCoincident_conditionalSupport G hG hDistinct i t ht)).comp
      (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) hm
  apply hc.congr_of_eventuallyEq
  filter_upwards [antipodesAutomatic_eventually G i t ht] with b hb
  exact sliceMass_gram_eq_capMass G hG hDistinct i b hb

def gramSlice {n : ℕ} (G : Mat n) (i : Fin n) (r : ℝ) (y : Coord n) : Coord n :=
  WeakSimplex.Coord.ofFun fun k ↦ inner ℝ (gramVectors G k)
    (r • gramVectors G i + normalResidual (gramVectors G i) y)

theorem measurable_gramSlice {n : ℕ} (G : Mat n) (i : Fin n) (r : ℝ) :
    Measurable (gramSlice G i r) :=
  (measurable_gramScore G).comp (by fun_prop)

theorem map_gramSlice_singleLaw {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) (r : ℝ) :
    (stdGaussian (Coord n)).map (gramSlice G i r) = singleLaw G i r := by
  have hcomp : gramSlice G i r =
      (fun x : Coord n ↦ singleMean G i r + lin (singleResidual G i) x) ∘
        (fun y : Coord n ↦ WeakSimplex.Coord.ofFun fun k ↦ inner ℝ (gramVectors G k) y) := by
    funext y
    ext k
    simp only [gramSlice, WeakSimplex.Coord.ofFun_apply, Function.comp_apply, PiLp.add_apply,
      singleMean, lin_singleResidual_apply]
    rw [inner_gram_slice G hG]
    simp only [inner_sub_left, real_inner_smul_left, correlation_entry_symm G hG.1 i]
  rw [hcomp, ← Measure.map_map (by fun_prop) (measurable_gramScore G),
    map_gramVectors_stdGaussian G hG.1]
  change Measure.map ((fun x : Coord n ↦ singleMean G i r + x) ∘ lin (singleResidual G i)) _ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), map_singleResidual G hG i,
    map_singleMean_add G hG i r]

theorem sliceMass_gram_eq_singlePinMass {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) (t : ℝ) :
    sliceMass (gramVectors G) (fun _ : Fin n ↦ t) i = singlePinMass G t i := by
  rw [sliceMass_eq_stdGaussian, singlePinMass, ← map_gramSlice_singleLaw G hG i t,
    Measure.map_apply (measurable_gramSlice G i t) (measurableSet_singleEvent i t)]
  rfl

theorem capMass_projected_common {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (t : ℝ) (ht : 0 < t) :
    capMass (projectedNormal G i) (fun j ↦ pairSupport G t i j) = singlePinMass G t i := by
  have ha : AntipodesAutomatic G i (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) := by
    intro k _
    change -t ≤ t
    linarith
  simpa only [funext (conditionalSupport_common G i t), WeakSimplex.Coord.ofFun_apply,
    sliceMass_gram_eq_singlePinMass G hG] using
    (sliceMass_gram_eq_capMass G hG hDistinct i _ ha).symm

theorem inner_gramResidual_projected {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i k : Fin n) (j : RetainedPair G i) :
    inner ℝ (gramVectors G k - G i k • gramVectors G i) (projectedNormal G i j) =
      singleCov G i k j / pairSigma G i j := by
  simp only [projectedNormal, real_inner_smul_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, inner_gramVectors G hG.1, hG.2,
    singleCov, correlation_entry_symm G hG.1 i, div_eq_mul_inv]
  ring

def gramPairSlice {n : ℕ} (G : Mat n) (i : Fin n) (j : RetainedPair G i) (t : ℝ) (y : Coord n) : Coord n :=
  gramSlice G i t (pairSupport G t i j • projectedNormal G i j + normalResidual (projectedNormal G i j) y)

theorem measurable_gramPairSlice {n : ℕ} (G : Mat n) (i : Fin n) (j : RetainedPair G i) (t : ℝ) :
    Measurable (gramPairSlice G i j t) := (measurable_gramSlice G i t).comp (by fun_prop)

theorem gramPairSlice_sequential {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) (j : RetainedPair G i) (t : ℝ) (y : Coord n) :
    gramPairSlice G i j t y = pairMean G i j t t +
      lin (pairResidual G i j) (WeakSimplex.Coord.ofFun fun k ↦ inner ℝ (gramVectors G k) y) := by
  have hc := pair_regression_denominator G i j j.property.2.1 j.property.2.2
  ext k
  rw [PiLp.add_apply, lin_pairResidual_sequential G hG i j hc,
    pairMean_sequential G hG i j t t hc]
  simp only [gramPairSlice, gramSlice, WeakSimplex.Coord.ofFun_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, singleMean]
  rw [inner_gram_slice G hG]
  simp only [normalResidual_apply, inner_add_right, inner_sub_right, real_inner_smul_right,
    inner_gramResidual_projected G hG i k j, lin_singleResidual_apply,
    WeakSimplex.Coord.ofFun_apply]
  simp only [projectedNormal, real_inner_smul_left, inner_sub_left,
    correlation_entry_symm G hG.1 i, pairSupport]
  rw [← retained_sigma_sq G i j]
  field_simp [(retained_sigma_pos G i j).ne']
  ring

theorem map_gramPairSlice_pairLaw {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) (j : RetainedPair G i) (t : ℝ) :
    (stdGaussian (Coord n)).map (gramPairSlice G i j t) = pairLaw G i j t t := by
  have hcomp : gramPairSlice G i j t =
      (fun x : Coord n ↦ pairMean G i j t t + lin (pairResidual G i j) x) ∘
        (fun y : Coord n ↦ WeakSimplex.Coord.ofFun fun k ↦ inner ℝ (gramVectors G k) y) :=
    funext (gramPairSlice_sequential G hG i j t)
  rw [hcomp, ← Measure.map_map (by fun_prop) (measurable_gramScore G),
    map_gramVectors_stdGaussian G hG.1]
  change Measure.map ((fun x : Coord n ↦ pairMean G i j t t + x) ∘ lin (pairResidual G i j)) _ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), map_pairResidual G hG.1 i j,
    map_pairMean_add G hG.1 i j t t]

theorem projectedSlice_event {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (j : RetainedPair G i) (t : ℝ) (ht : 0 < t)
    (y : Coord n) :
    y ∈ slicePreimage (projectedNormal G i) (fun k ↦ pairSupport G t i k) j ↔
      gramPairSlice G i j t y ∈ pairEvent i j t := by
  let z := pairSupport G t i j • projectedNormal G i j + normalResidual (projectedNormal G i j) y
  change (∀ k : RetainedPair G i, k ≠ j → inner ℝ (projectedNormal G i k) z ≤ pairSupport G t i k) ↔
    ∀ k : Fin n, k ≠ i → k ≠ j → gramSlice G i t z k ≤ t
  constructor
  · intro h k hki hkj
    by_cases hanti : G i k = -1
    · change inner ℝ (gramVectors G k) _ ≤ t
      rw [inner_gram_slice_antipode G hG i k hanti]
      linarith
    · have hk : -1 < G i k := lt_of_le_of_ne (correlation_entry_bounds G hG i k).1 (Ne.symm hanti)
      let a : RetainedPair G i := ⟨k, hki, hk, hDistinct i k (Ne.symm hki)⟩
      have haj : a ≠ j := fun he ↦ hkj (congrArg Subtype.val he)
      have ha := h a haj
      rw [pairSupport, le_div_iff₀ (retained_sigma_pos G i a)] at ha
      change inner ℝ (gramVectors G a) _ ≤ t
      rw [inner_gram_slice_retained G hG i a]
      nlinarith only [ha]
  · intro h k hkj
    have hne : (k : Fin n) ≠ j := fun he ↦ hkj (Subtype.ext he)
    have hk := h k k.property.1 hne
    change inner ℝ (gramVectors G k) _ ≤ t at hk
    rw [inner_gram_slice_retained G hG i k] at hk
    rw [pairSupport, le_div_iff₀ (retained_sigma_pos G i k)]
    nlinarith only [hk]

theorem sliceMass_projected_eq_pairSuccess {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (j : RetainedPair G i) (t : ℝ) (ht : 0 < t) :
    sliceMass (projectedNormal G i) (fun k ↦ pairSupport G t i k) j = pairSuccess G i j t := by
  rw [sliceMass_eq_stdGaussian, pairSuccess, ← map_gramPairSlice_pairLaw G hG i j t,
    Measure.map_apply (measurable_gramPairSlice G i j t) (measurableSet_pairEvent i j t)]
  apply congrArg ENNReal.toReal
  apply congrArg (stdGaussian (Coord n))
  ext y
  exact projectedSlice_event G hG hDistinct i j t ht y

theorem q_eq_projected_slice {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (j : RetainedPair G i) (t : ℝ) (ht : 0 < t) :
    q G t i j = WeakSimplex.normalPDF t * WeakSimplex.normalPDF (pairSupport G t i j) /
      pairSigma G i j * sliceMass (projectedNormal G i) (fun k ↦ pairSupport G t i k) j := by
  rw [q, if_pos ⟨Ne.symm j.property.1, j.property.2⟩,
    sliceMass_projected_eq_pairSuccess G hG hDistinct i j t ht]

end FSC
