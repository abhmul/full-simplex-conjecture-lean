import FSC.Analysis.Definitions
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space

/-! Bounded second-order expansions averaged against centered finite-second-moment noise. -/

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology

namespace FSC

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The remainder uses precisely the shared `Peano2` convention. -/
def peanoRemainder (f : V → ℝ) (x : V) (l : V →L[ℝ] ℝ)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (h : V) : ℝ :=
  f (x + h) - f x - l h - (1 / 2 : ℝ) * B h h

@[simp] theorem peanoRemainder_zero (f : V → ℝ) (x : V) (l : V →L[ℝ] ℝ)
    (B : V →L[ℝ] V →L[ℝ] ℝ) : peanoRemainder f x l B 0 = 0 := by
  simp [peanoRemainder]

/-- Boundedness upgrades the local Peano estimate to a global quadratic bound. -/
theorem Peano2.exists_remainder_bound {f : V → ℝ} {x : V} {l : V →L[ℝ] ℝ}
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hp : Peano2 f x l B)
    (hb : ∃ M : ℝ, ∀ z, ‖f z‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h, ‖peanoRemainder f x l B h‖ ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  have he : ∀ᶠ h in 𝓝 (0 : V), ‖peanoRemainder f x l B h‖ ≤ ‖h‖ ^ 2 := by
    simpa only [peanoRemainder, Real.norm_eq_abs, abs_pow, abs_norm] using
      hp.eventuallyLE
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  let C := 1 + 2 * M / r ^ 2 + ‖l‖ / r + ‖B‖ / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun h ↦ ?_⟩
  by_cases hh : ‖h‖ < r
  · have hi := hball (show dist h 0 < r by simpa using hh)
    have h1 : 1 ≤ C := by
      have ha : 0 ≤ 2 * M / r ^ 2 := by positivity
      have hb : 0 ≤ ‖l‖ / r := by positivity
      have hc : 0 ≤ ‖B‖ / 2 := by positivity
      dsimp [C]
      linarith
    exact hi.trans (by nlinarith [sq_nonneg ‖h‖])
  · have hhr : r ≤ ‖h‖ := le_of_not_gt hh
    have hn : 0 ≤ ‖h‖ := norm_nonneg h
    have hsq : r ^ 2 ≤ ‖h‖ ^ 2 := by nlinarith
    have hconst : 2 * M ≤ (2 * M / r ^ 2) * ‖h‖ ^ 2 := by
      calc
        2 * M = (2 * M / r ^ 2) * r ^ 2 := by field_simp
        _ ≤ (2 * M / r ^ 2) * ‖h‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
    have hlinear : ‖l‖ * ‖h‖ ≤ (‖l‖ / r) * ‖h‖ ^ 2 := by
      have hmul : r * ‖h‖ ≤ ‖h‖ ^ 2 := by nlinarith
      calc
        ‖l‖ * ‖h‖ = (‖l‖ / r) * (r * ‖h‖) := by field_simp
        _ ≤ (‖l‖ / r) * ‖h‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
    have hbase : ‖peanoRemainder f x l B h‖ ≤
        2 * M + ‖l‖ * ‖h‖ + (‖B‖ / 2) * ‖h‖ ^ 2 := by
      calc
        ‖peanoRemainder f x l B h‖ ≤
            ‖f (x + h)‖ + ‖f x‖ + ‖l h‖ + ‖(1 / 2 : ℝ) * B h h‖ := by
          change ‖f (x + h) - f x - l h - (1 / 2 : ℝ) * B h h‖ ≤ _
          have h₁ := norm_sub_le (f (x + h)) (f x)
          have h₂ := norm_sub_le (f (x + h) - f x) (l h)
          have h₃ := norm_sub_le (f (x + h) - f x - l h) ((1 / 2 : ℝ) * B h h)
          linarith only [h₁, h₂, h₃]
        _ ≤ M + M + ‖l‖ * ‖h‖ + (1 / 2 : ℝ) * (‖B‖ * ‖h‖ * ‖h‖) := by
          gcongr
          · exact hM (x + h)
          · exact hM x
          · exact l.le_opNorm h
          · rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            gcongr
            exact B.le_opNorm₂ h h
        _ = 2 * M + ‖l‖ * ‖h‖ + (‖B‖ / 2) * ‖h‖ ^ 2 := by ring
    apply hbase.trans
    change 2 * M + ‖l‖ * ‖h‖ + (‖B‖ / 2) * ‖h‖ ^ 2 ≤
      (1 + 2 * M / r ^ 2 + ‖l‖ / r + ‖B‖ / 2) * ‖h‖ ^ 2
    nlinarith [sq_nonneg ‖h‖]

/-- The linear-adjusted difference also has a global quadratic bound. -/
theorem Peano2.exists_secondOrder_bound {f : V → ℝ} {x : V} {l : V →L[ℝ] ℝ}
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hp : Peano2 f x l B)
    (hb : ∃ M : ℝ, ∀ z, ‖f z‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h, ‖f (x + h) - f x - l h‖ ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := hp.exists_remainder_bound hb
  refine ⟨C + ‖B‖ / 2, by positivity, fun h ↦ ?_⟩
  have hid : f (x + h) - f x - l h =
      peanoRemainder f x l B h + (1 / 2 : ℝ) * B h h := by
    simp [peanoRemainder]
  rw [hid]
  calc
    ‖peanoRemainder f x l B h + (1 / 2 : ℝ) * B h h‖ ≤
        ‖peanoRemainder f x l B h‖ + ‖(1 / 2 : ℝ) * B h h‖ := norm_add_le _ _
    _ ≤ C * ‖h‖ ^ 2 + (1 / 2 : ℝ) * (‖B‖ * ‖h‖ * ‖h‖) := by
      gcongr
      · exact hbound h
      · rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        gcongr
        exact B.le_opNorm₂ h h
    _ = (C + ‖B‖ / 2) * ‖h‖ ^ 2 := by ring

private theorem norm_sqrt_smul_sq_div {s : ℝ} (hs : 0 < s) (z : V) :
    ‖Real.sqrt s • z‖ ^ 2 / s = ‖z‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hs.le]
  exact mul_div_cancel_left₀ _ hs.ne'

private theorem bilin_sqrt_smul_div (B : V →L[ℝ] V →L[ℝ] ℝ)
    {s : ℝ} (hs : 0 < s) (z : V) :
    B (Real.sqrt s • z) (Real.sqrt s • z) / s = B z z := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, Real.mul_self_sqrt hs.le]
  exact mul_div_cancel_left₀ _ hs.ne'

omit [NormedSpace ℝ V] in
private theorem norm_add_sq_bound (u y : V) (hu : ‖u‖ ≤ 1) :
    ‖u + y‖ ^ 2 ≤ 2 * (1 + ‖y‖ ^ 2) := by
  have hnorm := norm_add_le u y
  have hsquare : ‖u + y‖ ^ 2 ≤ (‖u‖ + ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [norm_nonneg u, norm_nonneg y, sq_nonneg (‖u‖ - ‖y‖)]

/-- The pointwise second-order quotient along a vanishing normalized drift. -/
theorem Peano2.tendsto_secondOrder_quotient {f : V → ℝ} {x : V} {l : V →L[ℝ] ℝ}
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hp : Peano2 f x l B)
    {u : ℝ → V} (hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0)) (y : V) :
    Tendsto (fun s : ℝ ↦
      (f (x + Real.sqrt s • (u s + y)) - f x - l (Real.sqrt s • (u s + y))) / s)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) * B y y)) := by
  have hs : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hsq : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have huz : Tendsto (fun s ↦ u s + y) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    simpa using hu.add_const y
  have hinc : Tendsto (fun s ↦ Real.sqrt s • (u s + y))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : V)) := by
    simpa using hsq.smul huz
  have hn : Tendsto (fun s : ℝ ↦ ‖Real.sqrt s • (u s + y)‖ ^ 2 / s)
      (𝓝[>] (0 : ℝ)) (𝓝 (‖y‖ ^ 2)) := by
    apply (huz.norm.pow 2).congr'
    exact hs.mono fun s hpos ↦ (norm_sqrt_smul_sq_div hpos (u s + y)).symm
  have hbig : (fun s : ℝ ↦ ‖Real.sqrt s • (u s + y)‖ ^ 2) =O[𝓝[>] (0 : ℝ)]
      (fun s ↦ s) :=
    isBigO_of_div_tendsto_nhds (hs.mono fun _ hpos hzero ↦ (hpos.ne' hzero).elim)
      (‖y‖ ^ 2) hn
  have hr : Tendsto (fun s : ℝ ↦ peanoRemainder f x l B
      (Real.sqrt s • (u s + y)) / s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    ((hp.comp_tendsto hinc).trans_isBigO hbig).tendsto_div_nhds_zero
  have hbilin : Tendsto (fun s : ℝ ↦ B (u s + y) (u s + y))
      (𝓝[>] (0 : ℝ)) (𝓝 (B y y)) :=
    (B.continuous₂.tendsto (y, y)).comp (huz.prodMk_nhds huz)
  have hout := hr.add (hbilin.const_mul (1 / 2 : ℝ))
  simp only [zero_add] at hout
  apply hout.congr'
  filter_upwards [hs] with s hpos
  have hbil := bilin_sqrt_smul_div B hpos (u s + y)
  dsimp [peanoRemainder]
  linear_combination -(1 / 2 : ℝ) * hbil

section Measure

variable [MeasurableSpace V] [BorelSpace V]

/-- Dominated convergence of the second-order quotient uses only the second moment. -/
theorem Peano2.tendsto_integral_secondOrder {f : V → ℝ} {x : V} {l : V →L[ℝ] ℝ}
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hp : Peano2 f x l B)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ z, ‖f z‖ ≤ M)
    (μ : Measure V) [IsFiniteMeasure μ]
    (hsecond : Integrable (fun y : V ↦ ‖y‖ ^ 2) μ)
    {u : ℝ → V} (hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun s : ℝ ↦ ∫ y,
      (f (x + Real.sqrt s • (u s + y)) - f x - l (Real.sqrt s • (u s + y))) / s ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ y, (1 / 2 : ℝ) * B y y ∂μ)) := by
  obtain ⟨C, hC, hbound⟩ := hp.exists_secondOrder_bound hb
  have hu1 : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ‖u s‖ ≤ 1 :=
    (hu.norm.eventually_lt_const (by norm_num : ‖(0 : V)‖ < 1)).mono fun _ hs ↦ hs.le
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y : V ↦ 2 * C * (1 + ‖y‖ ^ 2)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun s ↦
      (((hf.comp (by fun_prop)).sub measurable_const).sub
        (l.continuous.measurable.comp (by fun_prop))).div_const s |>.aestronglyMeasurable
  · filter_upwards [hu1, self_mem_nhdsWithin] with s hus hs
    apply ae_of_all
    intro y
    have hpos : 0 < s := hs
    rw [norm_div, Real.norm_of_nonneg hpos.le]
    calc
      ‖f (x + Real.sqrt s • (u s + y)) - f x - l (Real.sqrt s • (u s + y))‖ / s ≤
          (C * ‖Real.sqrt s • (u s + y)‖ ^ 2) / s :=
        div_le_div_of_nonneg_right (hbound _) hpos.le
      _ = C * ‖u s + y‖ ^ 2 := by
        rw [mul_div_assoc, norm_sqrt_smul_sq_div hpos]
      _ ≤ C * (2 * (1 + ‖y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (norm_add_sq_bound (u s) y hus) hC
      _ = 2 * C * (1 + ‖y‖ ^ 2) := by ring
  · exact ((integrable_const (1 : ℝ)).add hsecond).const_mul (2 * C)
  · exact ae_of_all _ fun y ↦ hp.tendsto_secondOrder_quotient hu y

/-- The bounded-Borel Peano averaging formula gives the feasible right derivative.
Only the centered first moment and finite second moment of the probability law are used. -/
theorem Peano2.hasDerivWithinAt_noiseAverage [CompleteSpace V] [SecondCountableTopology V]
    {f : V → ℝ} {x : V} {l : V →L[ℝ] ℝ} {B : V →L[ℝ] V →L[ℝ] ℝ}
    (hp : Peano2 f x l B) (hf : Measurable f) (hb : ∃ M : ℝ, ∀ z, ‖f z‖ ≤ M)
    (μ : Measure V) [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hsecond : Integrable (fun y : V ↦ ‖y‖ ^ 2) μ)
    {v : ℝ → V} {v₀ : V} (hvzero : v 0 = 0)
    (hv : Tendsto (fun s : ℝ ↦ s⁻¹ • v s) (𝓝[>] (0 : ℝ)) (𝓝 v₀)) :
    HasDerivWithinAt (fun s : ℝ ↦ ∫ y, f (x + v s + Real.sqrt s • y) ∂μ)
      (l v₀ + (1 / 2 : ℝ) * ∫ y, B y y ∂μ) (Set.Ici 0) 0 := by
  have hs : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  let u : ℝ → V := fun s ↦ Real.sqrt s • (s⁻¹ • v s)
  have hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 (0 : V)) := by
    simpa [u] using hsqrt.smul hv
  have hinc (s : ℝ) (hs : 0 < s) (y : V) :
      Real.sqrt s • (u s + y) = v s + Real.sqrt s • y := by
    dsimp [u]
    rw [smul_add, smul_smul, smul_smul, Real.mul_self_sqrt hs.le,
      mul_inv_cancel₀ hs.ne', one_smul]
  have hid : Integrable (fun y : V ↦ y) μ :=
    ((memLp_two_iff_integrable_sq_norm (by fun_prop)).2 hsecond).integrable (by norm_num)
  have hlin_int (s : ℝ) : Integrable (fun y : V ↦ l (v s + Real.sqrt s • y)) μ :=
    l.integrable_comp ((integrable_const (v s)).add (hid.smul (Real.sqrt s)))
  have hlin (s : ℝ) : (∫ y : V, l (v s + Real.sqrt s • y) ∂μ) = l (v s) := by
    have hint : Integrable (fun y : V ↦ v s + Real.sqrt s • y) μ :=
      (integrable_const (v s)).add (hid.smul (Real.sqrt s))
    have hsmul : Integrable (fun y : V ↦ Real.sqrt s • y) μ := hid.smul _
    rw [l.integral_comp_comm hint,
      integral_add (integrable_const (v s)) hsmul,
      integral_smul, hmean]
    simp
  obtain ⟨M, hM⟩ := hb
  have hf_int (s : ℝ) : Integrable (fun y : V ↦ f (x + v s + Real.sqrt s • y)) μ :=
    (integrable_const M).mono' ((hf.comp (by fun_prop)).aestronglyMeasurable)
      (ae_of_all _ fun y ↦ hM _)
  have hlim := hp.tendsto_integral_secondOrder hf ⟨M, hM⟩ μ hsecond hu
  have hquot : Tendsto (fun s : ℝ ↦
      ((∫ y, f (x + v s + Real.sqrt s • y) ∂μ) - f x - l (v s)) / s)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) * ∫ y, B y y ∂μ)) := by
    rw [integral_const_mul] at hlim
    apply hlim.congr'
    filter_upwards [hs] with s hpos
    simp_rw [hinc s hpos, ← add_assoc]
    rw [integral_div]
    have hsub : Integrable (fun y : V ↦ f (x + v s + Real.sqrt s • y) - f x) μ :=
      (hf_int s).sub (integrable_const (f x))
    rw [integral_sub hsub (hlin_int s),
      integral_sub (hf_int s) (integrable_const (f x)), hlin]
    simp
  have hl : Tendsto (fun s : ℝ ↦ l (v s) / s) (𝓝[>] (0 : ℝ)) (𝓝 (l v₀)) := by
    have hcomp : Tendsto (fun s : ℝ ↦ l (s⁻¹ • v s)) (𝓝[>] (0 : ℝ)) (𝓝 (l v₀)) :=
      (l.continuous.tendsto v₀).comp hv
    simpa only [map_smul, smul_eq_mul, div_eq_inv_mul] using hcomp
  have htotal := hl.add hquot
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).2
  apply htotal.congr'
  filter_upwards [hs] with s hpos
  rw [slope_def_field]
  simp only [hvzero, add_zero, Real.sqrt_zero, zero_smul, integral_const,
    probReal_univ, one_smul, sub_zero]
  ring

end Measure

end FSC
