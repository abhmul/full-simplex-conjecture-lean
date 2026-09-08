import FSC.Analysis.NoiseAveraging

open Filter MeasureTheory
open scoped Topology

namespace FSCChecks.WP08

/-- Rank-zero noise is an allowed actual law; its bilinear contribution is zero. -/
theorem dirac_zero_noise {f : ℝ → ℝ} {x : ℝ} {l : ℝ →L[ℝ] ℝ}
    {B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ} (hp : FSC.Peano2 f x l B)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ z, ‖f z‖ ≤ M)
    (a : ℝ) : HasDerivWithinAt (fun s : ℝ ↦ f (x + s * a))
      (l a) (Set.Ici 0) 0 := by
  have hs : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hd := hp.hasDerivWithinAt_noiseAverage hf hb (Measure.dirac (0 : ℝ))
    (by simp) (integrable_dirac (by simp)) (v := fun s : ℝ ↦ s * a) (v₀ := a) (by simp)
    (show Tendsto (fun s : ℝ ↦ s⁻¹ • (s * a)) (𝓝[>] (0 : ℝ)) (𝓝 a) from
      tendsto_const_nhds.congr' (hs.mono fun s hpos ↦ by
        simp [smul_eq_mul, hpos.ne']))
  simpa using hd

end FSCChecks.WP08

#check @FSCChecks.WP08.dirac_zero_noise
#print axioms FSCChecks.WP08.dirac_zero_noise
