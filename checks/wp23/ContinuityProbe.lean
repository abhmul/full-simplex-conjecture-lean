import FSC.Gaussian.CDFContinuity

namespace FSCChecks.WP23

theorem continuous_fixed_cdf {n : ℕ} (G : FSC.Mat n) (hG : WeakSimplex.IsCorrelation G) :
    Continuous (FSC.cdf G) := by
  let c : {H : FSC.Mat n // WeakSimplex.IsCorrelation H} := ⟨G, hG⟩
  have hp : Continuous (fun s : ℝ ↦ (c, s)) := continuous_const.prodMk continuous_id
  change Continuous ((fun p : {H : FSC.Mat n // WeakSimplex.IsCorrelation H} × ℝ ↦
    FSC.cdf p.1.1 p.2) ∘ (fun s : ℝ ↦ (c, s)))
  exact Continuous.comp (g := fun p : {H : FSC.Mat n // WeakSimplex.IsCorrelation H} × ℝ ↦
    FSC.cdf p.1.1 p.2) (f := fun s : ℝ ↦ (c, s))
      (FSC.continuous_cdf_on_correlations (n := n)) hp

end FSCChecks.WP23
