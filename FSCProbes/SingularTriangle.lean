import FSC.Gaussian.PinDefinitions
import FSC.Gaussian.AffineLaw
import FSC.Support.Definitions
import WeakSimplexConjectureLean.Coding.BayesValue
import Mathlib.Tactic

/-!
# Singular triangle: actual laws and redundant support

Concrete regression test from docs/pro-return/PROBES.md. This file does not
certify the normalized-addition derivative until its analytic inputs are proved.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace Topology

namespace FSCProbes.SingularTriangle

open FSC

def gram : Mat 3 := !![1, 0, -(3 / 5); 0, 1, 4 / 5; -(3 / 5), 4 / 5, 1]

def normals : Fin 3 → Coord 2 :=
  ![WeakSimplex.Coord.ofFun ![1, 0],
    WeakSimplex.Coord.ofFun ![0, 1],
    WeakSimplex.Coord.ofFun ![-(3 / 5), 4 / 5]]

theorem codeGram_eq : WeakSimplex.codeGram normals = gram := by
  ext i j
  simp only [WeakSimplex.codeGram, Matrix.gram_apply, PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [normals, gram, Fin.sum_univ_succ]

theorem gram_isCorrelation : WeakSimplex.IsCorrelation gram := by
  constructor
  · rw [← codeGram_eq]
    exact WeakSimplex.codeGram_posSemidef normals
  · intro i
    fin_cases i <;> norm_num [gram]

theorem gram_distinct : DistinctScores gram := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [gram] at *

theorem gram_det : Matrix.det gram = 0 := by
  norm_num [gram, Matrix.det_fin_three, Matrix.cons_val_two]

theorem gram_not_posDef : ¬ gram.PosDef := by
  intro h
  have hp := h.det_pos
  rw [gram_det] at hp
  exact lt_irrefl 0 hp

/-- The singular score law is the actual standard-Gaussian linear image. -/
theorem map_normals_stdGaussian :
    Measure.map
      (fun y : Coord 2 ↦ WeakSimplex.Coord.ofFun (fun i ↦ inner ℝ (normals i) y))
      (stdGaussian (Coord 2)) = multivariateGaussian (0 : Coord 3) gram := by
  rw [← codeGram_eq]
  exact WeakSimplex.map_codeScore_stdGaussian normals

theorem multivariateGaussian_zero_cov {n : ℕ} (μ : Coord n) :
    multivariateGaussian μ (0 : Mat n) = Measure.dirac μ := by
  exact FSC.multivariateGaussian_zero_cov μ

theorem pairResidual_01 :
    pairResidual gram 0 1 = !![0, 0, 0; 0, 0, 0; 3 / 5, -(4 / 5), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairResidual, pairAlpha, pairBeta, gram, Matrix.cons_val_two, Fin.ext_iff]

theorem pairResidual_02 :
    pairResidual gram 0 2 = !![0, 0, 0; -(3 / 4), 1, -(5 / 4); 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairResidual, pairAlpha, pairBeta, gram, Matrix.cons_val_two, Fin.ext_iff]

theorem pairResidual_12 :
    pairResidual gram 1 2 = !![1, -(4 / 3), 5 / 3; 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairResidual, pairAlpha, pairBeta, gram, Matrix.cons_val_two, Fin.ext_iff]

theorem pairCov_01 : pairCov gram 0 1 = 0 := by
  rw [pairCov, pairResidual_01]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pairCov_02 : pairCov gram 0 2 = 0 := by
  rw [pairCov, pairResidual_02]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pairCov_12 : pairCov gram 1 2 = 0 := by
  rw [pairCov, pairResidual_12]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pairLaw_01 (r s : ℝ) :
    pairLaw gram 0 1 r s = Measure.dirac (pairMean gram 0 1 r s) := by
  rw [pairLaw, pairCov_01, multivariateGaussian_zero_cov]

theorem pairLaw_02 (r s : ℝ) :
    pairLaw gram 0 2 r s = Measure.dirac (pairMean gram 0 2 r s) := by
  rw [pairLaw, pairCov_02, multivariateGaussian_zero_cov]

theorem pairLaw_12 (r s : ℝ) :
    pairLaw gram 1 2 r s = Measure.dirac (pairMean gram 1 2 r s) := by
  rw [pairLaw, pairCov_12, multivariateGaussian_zero_cov]

theorem pairSuccess_01 (t : ℝ) (ht : 0 < t) :
    pairSuccess gram 0 1 t = 1 := by
  rw [pairSuccess, pairLaw_01]
  have hmem : pairMean gram 0 1 t t ∈ pairEvent 0 1 t := by
    intro k h0 h1
    fin_cases k <;>
      norm_num [pairMean, pairAlpha, pairBeta, gram] at *
    linarith
  simp [hmem]

theorem pairSuccess_02 (t : ℝ) (ht : 0 < t) :
    pairSuccess gram 0 2 t = 0 := by
  rw [pairSuccess, pairLaw_02]
  have hnot : pairMean gram 0 2 t t ∉ pairEvent 0 2 t := by
    intro h
    have hi := h 1 (by decide) (by decide)
    norm_num [pairMean, pairAlpha, pairBeta, gram, Matrix.cons_val_two] at hi
    linarith
  simp [hnot]

theorem pairSuccess_12 (t : ℝ) (ht : 0 < t) :
    pairSuccess gram 1 2 t = 1 := by
  rw [pairSuccess, pairLaw_12]
  have hmem : pairMean gram 1 2 t t ∈ pairEvent 1 2 t := by
    intro k h1 h2
    fin_cases k <;>
      norm_num [pairMean, pairAlpha, pairBeta, gram, Matrix.cons_val_two] at *
    linarith
  simp [hmem]

theorem q_01 (t : ℝ) (ht : 0 < t) :
    q gram t 0 1 = WeakSimplex.normalPDF t ^ 2 := by
  rw [q, if_pos (by norm_num [gram]), pairSuccess_01 t ht]
  norm_num [pairSupport, pairSigma, gram, pow_two]

theorem q_02 (t : ℝ) (ht : 0 < t) : q gram t 0 2 = 0 := by
  rw [q, if_pos (by norm_num [gram, Matrix.cons_val_two, Fin.ext_iff]), pairSuccess_02 t ht]
  simp

theorem pairSigma_12 : pairSigma gram 1 2 = 3 / 5 := by
  norm_num [pairSigma, gram, Matrix.cons_val_two, Real.sqrt_div]

theorem q_12 (t : ℝ) (ht : 0 < t) :
    q gram t 1 2 = (5 / 3) * WeakSimplex.normalPDF t * WeakSimplex.normalPDF (t / 3) := by
  rw [q, if_pos (by norm_num [gram, Matrix.cons_val_two, Fin.ext_iff]), pairSuccess_12 t ht]
  have hs : pairSupport gram t 1 2 = t / 3 := by
    rw [pairSupport, pairSigma_12]
    norm_num [gram, Matrix.cons_val_two]
    ring
  rw [hs, pairSigma_12]
  ring

theorem q_01_pos (t : ℝ) (ht : 0 < t) : 0 < q gram t 0 1 := by
  rw [q_01 t ht]
  exact sq_pos_of_pos (WeakSimplex.normalPDF_pos t)

theorem q_12_pos (t : ℝ) (ht : 0 < t) : 0 < q gram t 1 2 := by
  rw [q_12 t ht]
  exact mul_pos (mul_pos (by norm_num) (WeakSimplex.normalPDF_pos t))
    (WeakSimplex.normalPDF_pos (t / 3))

/-- Two identical unit normals retain the redundant second inequality. -/
def redundantNormals : Fin 2 → Coord 1 :=
  fun _ ↦ WeakSimplex.Coord.ofFun fun _ ↦ 1

theorem redundant_cap (a b : ℝ) :
    cap redundantNormals ![a, b] = {y : Coord 1 | y 0 ≤ min a b} := by
  ext y
  simp [cap, redundantNormals, PiLp.inner_apply, Fin.forall_fin_two]

theorem redundant_capMass (a b : ℝ) :
    capMass redundantNormals ![a, b] = WeakSimplex.normalCDF (min a b) := by
  have hmap : Measure.map (fun y : Coord 1 ↦ y 0) (stdGaussian (Coord 1)) =
      gaussianReal 0 1 := by
    simpa using (measurePreserving_eval_multivariateGaussian
      (μ := (0 : Coord 1)) (S := (1 : Mat 1)) Matrix.PosSemidef.one
      (i := (0 : Fin 1))).map_eq
  have hmeasure : stdGaussian (Coord 1) {y : Coord 1 | y 0 ≤ min a b} =
      gaussianReal 0 1 (Set.Iic (min a b)) := by
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  rw [capMass, redundant_cap, hmeasure, ← WeakSimplex.normalCDF_eq_measure_Iic]
  exact ENNReal.toReal_ofReal (WeakSimplex.normalCDF_pos _).le

theorem redundant_capMass_actual (t : ℝ) (ht : 0 < t) :
    capMass redundantNormals ![t, 2 * t] = WeakSimplex.normalCDF t := by
  rw [redundant_capMass, min_eq_left (by linarith)]

/-- The weaker parallel inequality has zero derivative at the actual support. -/
theorem hasDerivAt_redundant_support (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun b : ℝ ↦ capMass redundantNormals ![t, b]) 0 (2 * t) := by
  apply (hasDerivAt_const (2 * t) (WeakSimplex.normalCDF t)).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds (show t < 2 * t by linarith)] with b hb
  rw [redundant_capMass, min_eq_left hb.le]

/-- The active parallel inequality has the usual Gaussian density derivative. -/
theorem hasDerivAt_active_support (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun a : ℝ ↦ capMass redundantNormals ![a, 2 * t])
      (WeakSimplex.normalPDF t) t := by
  apply (WeakSimplex.hasDerivAt_normalCDF t).congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds (show t < 2 * t by linarith)] with a ha
  rw [redundant_capMass, min_eq_left ha.le]

/-- The full residual law, including its deterministic coordinate, is a Dirac law. -/
theorem redundant_sliceLaw (j : Fin 2) (z : ℝ) :
    sliceLaw (redundantNormals j) z =
      Measure.dirac (WeakSimplex.Coord.ofFun (fun _ : Fin 1 ↦ z)) := by
  have heq :
      (fun y : Coord 1 ↦ z • redundantNormals j +
        (y - inner ℝ (redundantNormals j) y • redundantNormals j)) =
      fun _ ↦ WeakSimplex.Coord.ofFun (fun _ : Fin 1 ↦ z) := by
    funext y
    ext i
    fin_cases i
    simp [redundantNormals, PiLp.inner_apply]
  rw [sliceLaw, heq]
  simp

theorem redundant_sliceMass_active (a b : ℝ) (hab : a < b) :
    sliceMass redundantNormals ![a, b] 0 = 1 := by
  rw [sliceMass, redundant_sliceLaw]
  simp [redundantNormals, PiLp.inner_apply, Fin.forall_fin_two, hab.le]

theorem redundant_sliceMass_inactive (a b : ℝ) (hab : a < b) :
    sliceMass redundantNormals ![a, b] 1 = 0 := by
  rw [sliceMass, redundant_sliceLaw]
  simp [redundantNormals, PiLp.inner_apply, Fin.forall_fin_two, not_le.mpr hab]

theorem redundant_supportGradient (a b : ℝ) (hab : a < b) :
    supportGradient redundantNormals ![a, b] =
      WeakSimplex.normalPDF a • (ContinuousLinearMap.proj (0 : Fin 2)) := by
  ext h
  simp [supportGradient, Fin.sum_univ_two,
    redundant_sliceMass_active a b hab, redundant_sliceMass_inactive a b hab]
  ring

theorem redundant_capMass_eq_of_lt (b : Fin 2 → ℝ) (hb : b 0 < b 1) :
    capMass redundantNormals b = WeakSimplex.normalCDF (b 0) := by
  have heq : b = ![b 0, b 1] := by
    ext i
    fin_cases i <;> rfl
  calc
    capMass redundantNormals b = capMass redundantNormals ![b 0, b 1] :=
      congrArg (capMass redundantNormals) heq
    _ = WeakSimplex.normalCDF (b 0) := by
      rw [redundant_capMass, min_eq_left hb.le]

theorem contDiff_one_normalCDF : ContDiff ℝ 1 WeakSimplex.normalCDF := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x ↦ (WeakSimplex.hasDerivAt_normalCDF x).differentiableAt, ?_⟩
  have hd : deriv WeakSimplex.normalCDF = WeakSimplex.normalPDF :=
    funext fun x ↦ (WeakSimplex.hasDerivAt_normalCDF x).deriv
  rw [hd]
  exact continuous_iff_continuousAt.mpr fun x ↦
    (WeakSimplex.hasDerivAt_normalPDF x).continuousAt

/-- A genuine open C¹ neighborhood with the frozen slice-law gradient. -/
theorem redundant_support_C1 (t : ℝ) (ht : 0 < t) :
    ∃ U : Set (Fin 2 → ℝ), IsOpen U ∧ ![t, 2 * t] ∈ U ∧
      ContDiffOn ℝ 1 (capMass redundantNormals) U ∧
      ∀ b ∈ U, HasFDerivAt (capMass redundantNormals)
        (supportGradient redundantNormals b) b := by
  let U : Set (Fin 2 → ℝ) := {b | b 0 < b 1}
  have hU : IsOpen U := isOpen_lt (by fun_prop) (by fun_prop)
  refine ⟨U, hU, by change t < 2 * t; linarith, ?_, ?_⟩
  · have h : ContDiff ℝ 1 (fun b : Fin 2 → ℝ ↦ WeakSimplex.normalCDF (b 0)) :=
      contDiff_one_normalCDF.comp (by fun_prop)
    exact h.contDiffOn.congr fun b hb ↦ redundant_capMass_eq_of_lt b hb
  · intro b hb
    have hg : supportGradient redundantNormals b =
        WeakSimplex.normalPDF (b 0) • (ContinuousLinearMap.proj (0 : Fin 2)) := by
      have heq : b = ![b 0, b 1] := by
        ext i
        fin_cases i <;> rfl
      rw [heq]
      exact redundant_supportGradient (b 0) (b 1) hb
    rw [hg]
    have hd := (WeakSimplex.hasDerivAt_normalCDF (b 0)).comp_hasFDerivAt b
      (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt
    apply hd.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hb] with c hc
    exact redundant_capMass_eq_of_lt c hc

def firstPinLoading : Matrix (Fin 3) (Fin 1) ℝ := !![0; 1; 4 / 5]

theorem firstPinLoading_cov :
    firstPinLoading * (1 : Mat 1) * firstPinLoading.transpose = singleCov gram 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstPinLoading, singleCov, gram, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The canonical first pin is exactly the affine image of a scalar Gaussian. -/
theorem singleLaw_0 (t : ℝ) :
    singleLaw gram 0 t =
      (stdGaussian (Coord 1)).map (fun y ↦ singleMean gram 0 t + lin firstPinLoading y) := by
  symm
  simpa only [multivariateGaussian_zero_one, map_zero, add_zero, firstPinLoading_cov, singleLaw]
    using map_affine_multivariateGaussian (0 : Coord 1) (1 : Mat 1)
      Matrix.PosSemidef.one firstPinLoading (singleMean gram 0 t)

theorem firstPin_event (t : ℝ) :
    (fun y : Coord 1 ↦ singleMean gram 0 t + lin firstPinLoading y) ⁻¹' singleEvent 0 t =
      cap redundantNormals ![t, 2 * t] := by
  rw [redundant_cap]
  ext y
  simp [singleEvent, singleMean, gram, lin_apply, firstPinLoading,
    Matrix.mulVec, dotProduct, Fin.forall_fin_succ]
  intro hy
  constructor <;> intro h <;> linarith

/-- The original canonical single-pin mass is the redundant unbounded cap mass. -/
theorem singlePinMass_0_eq_capMass (t : ℝ) :
    singlePinMass gram t 0 = capMass redundantNormals ![t, 2 * t] := by
  rw [singlePinMass, singleLaw_0,
    Measure.map_apply (by fun_prop) (measurableSet_singleEvent 0 t), firstPin_event]
  rfl

theorem singlePinMass_0 (t : ℝ) (ht : 0 < t) :
    singlePinMass gram t 0 = WeakSimplex.normalCDF t := by
  rw [singlePinMass_0_eq_capMass, redundant_capMass_actual t ht]

/-- The equal-support reference has a genuine corner in the redundant coordinate. -/
theorem not_differentiableAt_tied_support (t : ℝ) :
    ¬ DifferentiableAt ℝ (fun b : ℝ ↦ capMass redundantNormals ![t, b]) t := by
  intro hf
  have hleft : HasDerivWithinAt (fun b : ℝ ↦ capMass redundantNormals ![t, b])
      (WeakSimplex.normalPDF t) (Set.Iic t) t := by
    apply ((WeakSimplex.hasDerivAt_normalCDF t).hasDerivWithinAt
      (s := Set.Iic t)).congr_of_mem
    · intro b hb
      rw [redundant_capMass, min_eq_right hb]
    · exact Set.self_mem_Iic
  have hright : HasDerivWithinAt (fun b : ℝ ↦ capMass redundantNormals ![t, b])
      0 (Set.Ici t) t := by
    apply ((hasDerivAt_const t (WeakSimplex.normalCDF t)).hasDerivWithinAt
      (s := Set.Ici t)).congr_of_mem
    · intro b hb
      rw [redundant_capMass, min_eq_left hb]
    · exact Set.self_mem_Ici
  have hl := hleft.derivWithin (uniqueDiffWithinAt_Iic t)
  have hr := hright.derivWithin (uniqueDiffWithinAt_Ici t)
  rw [hf.derivWithin (uniqueDiffWithinAt_Iic t)] at hl
  rw [hf.derivWithin (uniqueDiffWithinAt_Ici t)] at hr
  have hpos := WeakSimplex.normalPDF_pos t
  linarith

end FSCProbes.SingularTriangle
