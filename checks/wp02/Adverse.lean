import FSC.Gaussian.IndependentSum

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FSCChecks

/-- Exact arbitrary rectangular transport of a deterministic input law. -/
theorem affine_zero_covariance {m n : ℕ}
    (μ : FSC.Coord n) (A : Matrix (Fin m) (Fin n) ℝ) (b : FSC.Coord m) :
    Measure.map (fun x ↦ b + FSC.lin A x) (multivariateGaussian μ (0 : FSC.Mat n)) =
      Measure.dirac (b + FSC.lin A μ) := by
  simpa only [Matrix.mul_zero, Matrix.zero_mul, FSC.multivariateGaussian_zero_cov] using
    FSC.map_affine_multivariateGaussian μ 0 Matrix.PosSemidef.zero A b

/-- Zero-rank noise is permitted in the exact product-space addition law. -/
theorem addition_zero_noise {n : ℕ} (G : FSC.Mat n) (hG : G.PosSemidef)
    (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (fun p : FSC.Coord n × FSC.Coord n ↦ p.1 + Real.sqrt s • p.2)
      ((multivariateGaussian (0 : FSC.Coord n) G).prod
        (multivariateGaussian (0 : FSC.Coord n) (0 : FSC.Mat n))) =
      multivariateGaussian (0 : FSC.Coord n) G := by
  simpa only [smul_zero, add_zero] using
    FSC.map_add_sqrt_smul_multivariateGaussian G 0 hG Matrix.PosSemidef.zero s hs

/-- The nonnegative addition parameter includes the endpoint s = 0. -/
theorem addition_parameter_zero {n : ℕ} (G L : FSC.Mat n)
    (hG : G.PosSemidef) (hL : L.PosSemidef) :
    Measure.map (fun p : FSC.Coord n × FSC.Coord n ↦ p.1 + Real.sqrt (0 : ℝ) • p.2)
      ((multivariateGaussian (0 : FSC.Coord n) G).prod
        (multivariateGaussian (0 : FSC.Coord n) L)) =
      multivariateGaussian (0 : FSC.Coord n) G := by
  simpa only [zero_smul, add_zero] using
    FSC.map_add_sqrt_smul_multivariateGaussian G L hG hL 0 le_rfl

#print axioms affine_zero_covariance
#print axioms addition_zero_noise
#print axioms addition_parameter_zero

end FSCChecks
