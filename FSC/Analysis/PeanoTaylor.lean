import FSC.Analysis.Definitions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! A vector-domain second-order Peano expansion from genuine derivative hypotheses. -/

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace FSC

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A differentiable neighborhood derivative field has the exact shared Peano expansion. -/
theorem peano2_of_hasFDerivAt_derivative
    {f : V → ℝ} {f' : V → V →L[ℝ] ℝ} {x : V}
    {B : V →L[ℝ] V →L[ℝ] ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hB : HasFDerivAt f' B x) :
    Peano2 f x (f' x) B := by
  have hsym : ∀ v w : V, B v w = B w v :=
    second_derivative_symmetric_of_eventually_of_real hf hB
  have hadd : Tendsto (fun h : V ↦ x + h) (𝓝 (0 : V)) (𝓝 x) := by
    simpa using! (continuous_const.add continuous_id).tendsto (0 : V)
  have he : ∀ᶠ h in 𝓝 (0 : V), HasFDerivAt f (f' (x + h)) (x + h) :=
    hadd.eventually hf
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  let g : V → ℝ := fun h ↦ f (x + h) - f x - f' x h - (1 / 2 : ℝ) * B h h
  let dg : V → V →L[ℝ] ℝ := fun h ↦ f' (x + h) - f' x - B h
  have hg (h : V) (hh : h ∈ Metric.ball (0 : V) r) :
      HasFDerivAt g (dg h) h := by
    have hfh := (hball (show dist h 0 < r from hh)).comp h
      ((hasFDerivAt_id h).const_add x)
    have hquad : HasFDerivAt (fun z : V ↦ (1 / 2 : ℝ) * B z z) (B h) h := by
      have hq := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id h) (hasFDerivAt_id h)).const_smul
        (1 / 2 : ℝ)
      apply hq.congr_fderiv
      ext z
      simp [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, hsym h z]
      ring
    simpa only [g, dg, ContinuousLinearMap.comp_id] using!
      ((hfh.sub_const (f x)).sub ((f' x).hasFDerivAt)).sub hquad
  have hdg : dg =o[𝓝[Metric.ball (0 : V) r] (0 : V)]
      (fun h ↦ ‖h - 0‖ ^ 1) := by
    simpa only [dg, sub_zero, pow_one] using
      (hasFDerivAt_iff_isLittleO_nhds_zero.mp hB).norm_right.mono nhdsWithin_le_nhds
  have hrem := (convex_ball (0 : V) r).isLittleO_pow_succ
    (Metric.mem_ball_self hr) (fun h hh ↦ (hg h hh).hasFDerivWithinAt) hdg
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds (0 : V) hr)] at hrem
  simpa [g, Peano2] using hrem

/-- Local `C²` regularity implies the shared expansion with the actual first and second derivatives. -/
theorem peano2_of_contDiffAt {f : V → ℝ} {x : V} (hf : ContDiffAt ℝ 2 f x) :
    Peano2 f x (fderiv ℝ f x) (fderiv ℝ (fderiv ℝ f) x) := by
  apply peano2_of_hasFDerivAt_derivative
  · filter_upwards [hf.eventually (by norm_num)] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  · exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt

end FSC
