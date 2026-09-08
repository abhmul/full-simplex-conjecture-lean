import FSC.Gaussian.PairWeights
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Sequences
import Mathlib.Topology.Bases

/-! Joint Gaussian CDF continuity on all correlation matrices, including duplicates and singular limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology InnerProductSpace

namespace FSC

theorem isClosed_thresholdEvent {n : ℕ} (b : Coord n) : IsClosed (thresholdEvent b) := by
  simp only [thresholdEvent, Set.setOf_forall]
  exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const

theorem frontier_thresholdEvent_subset {n : ℕ} (b : Coord n) :
    frontier (thresholdEvent b) ⊆ ⋃ i, {x : Coord n | x i = b i} := by
  intro x hx
  by_contra hnot
  have hne : ∀ i, x i ≠ b i := by simpa only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] using hnot
  have hle : x ∈ thresholdEvent b := (isClosed_thresholdEvent b).closure_eq ▸ hx.1
  have hlt : x ∈ {y : Coord n | ∀ i, y i < b i} := fun i ↦ lt_of_le_of_ne (hle i) (hne i)
  have hopen : IsOpen {y : Coord n | ∀ i, y i < b i} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (by fun_prop) continuous_const
  have hint : x ∈ interior (thresholdEvent b) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hopen.mem_nhds hlt) (fun y hy i ↦ (hy i).le))
  exact hx.2 hint

theorem gaussian_coordinate_hyperplane_null {n : ℕ} (μ : Coord n) (G : Mat n)
    (hG : G.PosSemidef) (i : Fin n) (hii : 0 < G i i) (b : ℝ) :
    multivariateGaussian μ G {x : Coord n | x i = b} = 0 := by
  letI : NoAtoms (gaussianReal (μ i) (G i i).toNNReal) :=
    noAtoms_gaussianReal (Real.toNNReal_pos.mpr hii).ne'
  have h := (measurePreserving_eval_multivariateGaussian (μ := μ) hG (i := i)).map_eq
  have heq := congrArg (fun m : Measure ℝ ↦ m {b}) h
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton b)] at heq
  simpa only [Set.preimage, Set.mem_singleton_iff, measure_singleton] using heq

/-- Only the marginal variances need be positive; the covariance itself may be singular. -/
theorem gaussian_frontier_thresholdEvent_null {n : ℕ} (μ : Coord n) (G : Mat n)
    (hG : G.PosSemidef) (hdiag : ∀ i, 0 < G i i) (b : Coord n) :
    multivariateGaussian μ G (frontier (thresholdEvent b)) = 0 := by
  apply measure_mono_null (frontier_thresholdEvent_subset b)
  exact measure_iUnion_null fun i ↦ gaussian_coordinate_hyperplane_null μ G hG i (hdiag i) (b i)

/-- Sequential Levy continuity of the actual Gaussian law for arbitrary convergent PSD covariance and mean. -/
def gaussianProbability {n : ℕ} (μ : Coord n) (G : Mat n) : ProbabilityMeasure (Coord n) :=
  ⟨multivariateGaussian μ G, inferInstance⟩

@[simp] theorem coe_gaussianProbability {n : ℕ} (μ : Coord n) (G : Mat n) :
    (gaussianProbability μ G : Measure (Coord n)) = multivariateGaussian μ G := rfl

theorem tendsto_multivariateGaussian {n : ℕ} (μs : ℕ → Coord n) (Gs : ℕ → Mat n)
    (μ : Coord n) (G : Mat n) (hGs : ∀ k, (Gs k).PosSemidef) (hG : G.PosSemidef)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hmat : Tendsto Gs atTop (𝓝 G)) :
    Tendsto (fun k ↦ gaussianProbability (μs k) (Gs k)) atTop (𝓝 (gaussianProbability μ G)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro x
  change Tendsto (fun k ↦ charFun (multivariateGaussian (μs k) (Gs k)) x)
    atTop (𝓝 (charFun (multivariateGaussian μ G) x))
  have hfun := funext fun k ↦ charFun_multivariateGaussian (μ := μs k) (hGs k) x
  rw [hfun, charFun_multivariateGaussian hG]
  have hc : Continuous (fun H : Mat n ↦ (x ⬝ᵥ H *ᵥ x : ℝ)) := by
    simp only [dotProduct, mulVec]
    fun_prop
  have hquad := (hc.tendsto G).comp hmat
  have hinner : Tendsto (fun k ↦ inner ℝ x (μs k)) atTop (𝓝 (inner ℝ x μ)) :=
    tendsto_const_nhds.inner hμ
  have hinnerC := (Complex.continuous_ofReal.tendsto (inner ℝ x μ)).comp hinner
  have hquadC := (Complex.continuous_ofReal.tendsto (x ⬝ᵥ G *ᵥ x : ℝ)).comp hquad
  exact Complex.continuous_exp.tendsto _ |>.comp
    ((hinnerC.mul_const Complex.I).sub (hquadC.div_const 2))

/-- Moving thresholds are absorbed into the mean so that Portmanteau uses one fixed orthant. -/
theorem thresholdCDF_eq_shifted_zero {n : ℕ} (G : Mat n) (hG : G.PosSemidef) (b : Coord n) :
    thresholdCDF G b =
      (multivariateGaussian (-b) G (thresholdEvent (0 : Coord n))).toReal := by
  have hlin : lin (1 : Mat n) = ContinuousLinearMap.id ℝ (Coord n) := by
    ext x i
    simp [lin_apply]
  have hm := map_affine_multivariateGaussian (0 : Coord n) G hG (1 : Mat n) (-b)
  simp only [hlin, ContinuousLinearMap.id_apply, add_zero, Matrix.one_mul,
    Matrix.transpose_one, Matrix.mul_one] at hm
  rw [← hm, Measure.map_apply (by fun_prop) (measurableSet_thresholdEvent _)]
  unfold thresholdCDF
  congr 2
  ext x
  simp only [Set.mem_preimage, thresholdEvent, Set.mem_setOf_eq,
    PiLp.add_apply, PiLp.neg_apply, PiLp.zero_apply]
  exact forall_congr' fun i ↦ by constructor <;> intro h <;> linarith

theorem continuous_thresholdCDF_on_correlations {n : ℕ} :
    Continuous (fun p : {G : Mat n // WeakSimplex.IsCorrelation G} × Coord n ↦
      thresholdCDF p.1.1 p.2) := by
  letI : FirstCountableTopology (Mat n) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℝ))
  letI : FirstCountableTopology {G : Mat n // WeakSimplex.IsCorrelation G} :=
    TopologicalSpace.Subtype.firstCountableTopology {G : Mat n | WeakSimplex.IsCorrelation G}
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have hμ : Tendsto (fun k ↦ -(ps k).2) atTop (𝓝 (-p.2)) :=
    (continuous_snd.neg.tendsto p).comp hp
  have hmat : Tendsto (fun k ↦ (ps k).1.1) atTop (𝓝 p.1.1) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto p).comp hp
  have hlaw := tendsto_multivariateGaussian (fun k ↦ -(ps k).2) (fun k ↦ (ps k).1.1)
    (-p.2) p.1.1 (fun k ↦ (ps k).1.2.1) p.1.2.1 hμ hmat
  have hnull := gaussian_frontier_thresholdEvent_null (-p.2) p.1.1 p.1.2.1
    (fun i ↦ by rw [p.1.2.2 i]; norm_num) (0 : Coord n)
  have hmass := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlaw hnull
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hmass
  simpa only [Function.comp_def, thresholdCDF_eq_shifted_zero _ p.1.2.1,
    thresholdCDF_eq_shifted_zero _ (ps _).1.2.1, coe_gaussianProbability] using hreal

theorem continuous_cdf_on_correlations {n : ℕ} :
    Continuous (fun p : {G : Mat n // WeakSimplex.IsCorrelation G} × ℝ ↦
      cdf p.1.1 p.2) := by
  have hc : Continuous (fun p : {G : Mat n // WeakSimplex.IsCorrelation G} × ℝ ↦
      (p.1, WeakSimplex.Coord.ofFun fun _ : Fin n ↦ p.2)) := by
    unfold WeakSimplex.Coord.ofFun
    fun_prop
  simpa only [Function.comp_def, thresholdCDF_const] using
    continuous_thresholdCDF_on_correlations.comp hc

theorem cdf_pos {n : ℕ} (_hn : 1 ≤ n) (G : Mat n) (_hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (ht : 0 < t) : 0 < cdf G t := by
  have hopen : IsOpen {x : Coord n | ∀ i, x i < t} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt (by fun_prop) continuous_const
  have hpos := multivariateGaussian_pos_of_mem_open (0 : Coord n) G
    {x : Coord n | ∀ i, x i < t} hopen (by simpa using fun _ : Fin n ↦ ht)
  have hmass : 0 < multivariateGaussian (0 : Coord n) G (WeakSimplex.lowerOrthant t) :=
    hpos.trans_le (measure_mono (fun x hx i ↦ (hx i).le))
  exact ENNReal.toReal_pos hmass.ne' (measure_ne_top _ _)

end FSC
