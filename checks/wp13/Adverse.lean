import FSC.Gaussian.CDFContinuity
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology

namespace FSCChecks

def duplicateMatrix : FSC.Mat 2 := fun _ _ ↦ 1

theorem duplicateMatrix_corr : WeakSimplex.IsCorrelation duplicateMatrix := by
  have heq : duplicateMatrix = Matrix.vecMulVec (fun _ : Fin 2 ↦ (1 : ℝ))
      (star (fun _ : Fin 2 ↦ (1 : ℝ))) := by ext i j; simp [duplicateMatrix, Matrix.vecMulVec_apply]
  constructor
  · rw [heq]
    exact Matrix.posSemidef_vecMulVec_self_star _
  · intro i
    rfl

def duplicatePath (s : ℝ) : FSC.Mat 2 := (1 - s) • duplicateMatrix + s • 1

theorem duplicatePath_corr (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    WeakSimplex.IsCorrelation (duplicatePath s) := by
  constructor
  · exact (duplicateMatrix_corr.1.smul (sub_nonneg.mpr hs1)).add (Matrix.PosSemidef.one.smul hs0)
  · intro i
    simp [duplicatePath, duplicateMatrix]

/-- Joint CDF continuity survives positive-rank regularizations converging to duplicated scores. -/
theorem cdf_duplicate_limit (t : ℝ) :
    Tendsto (fun k : ℕ ↦ FSC.cdf (duplicatePath ((1 / 2 : ℝ) ^ k)) t)
      atTop (𝓝 (FSC.cdf duplicateMatrix t)) := by
  have hp : Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hg : Tendsto (fun k : ℕ ↦ duplicatePath ((1 / 2 : ℝ) ^ k))
      atTop (𝓝 duplicateMatrix) := by
    simpa only [duplicatePath, sub_zero, one_smul, zero_smul, add_zero] using
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hp).smul_const duplicateMatrix).add
        (hp.smul_const (1 : FSC.Mat 2))
  let ps (k : ℕ) : {G : FSC.Mat 2 // WeakSimplex.IsCorrelation G} :=
    ⟨duplicatePath ((1 / 2 : ℝ) ^ k), duplicatePath_corr _ (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))⟩
  have hps : Tendsto ps atTop
      (𝓝 (⟨duplicateMatrix, duplicateMatrix_corr⟩ : {G : FSC.Mat 2 // WeakSimplex.IsCorrelation G})) :=
    tendsto_subtype_rng.mpr hg
  simpa only [Function.comp_def, ps] using
    ((FSC.continuous_cdf_on_correlations (n := 2)).tendsto
      (⟨duplicateMatrix, duplicateMatrix_corr⟩, t)).comp (hps.prodMk_nhds tendsto_const_nhds)

/-- A zero-variance coordinate at its exact threshold does carry full boundary mass. -/
theorem deterministic_frontier_mass :
    multivariateGaussian (0 : FSC.Coord 1) (0 : FSC.Mat 1)
      (frontier (FSC.thresholdEvent (0 : FSC.Coord 1))) = 1 := by
  have hmem : (0 : FSC.Coord 1) ∈ frontier (FSC.thresholdEvent 0) := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure (by intro i; simp), ?_⟩
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let x : FSC.Coord 1 := WeakSimplex.Coord.ofFun fun _ ↦ ε / 2
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have hh := hx 0
      change ε / 2 ≤ 0 at hh
      linarith
    · have hn : ‖x‖ = ε / 2 := by
        simp [x, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs, abs_of_pos hε]
        positivity
      simpa [dist_zero_left, hn] using (show ε / 2 < ε by linarith)
  rw [FSC.multivariateGaussian_zero_cov]
  simp [hmem]

#print axioms FSCChecks.duplicateMatrix_corr
#print axioms FSCChecks.duplicatePath_corr
#print axioms FSCChecks.cdf_duplicate_limit
#print axioms FSCChecks.deterministic_frontier_mass

end FSCChecks
