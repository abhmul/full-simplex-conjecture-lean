import FSC.Gaussian.AffineLaw

/-! Exact independent Gaussian sum laws. The product measure is explicit, and all scalar weights and PSD ranks are allowed. The proof uses public characteristic-function and affine-image APIs; no private WSC template is imported or copied. -/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace FSC

/-- Scalar images preserve the actual Gaussian law, including scalar zero. -/
theorem map_smul_multivariateGaussian {n : ℕ} (μ : Coord n) (G : Mat n)
    (hG : G.PosSemidef) (a : ℝ) :
    Measure.map (fun x ↦ a • x) (multivariateGaussian μ G) =
      multivariateGaussian (a • μ) (a ^ 2 • G) := by
  have hlin : lin (a • (1 : Mat n)) = a • ContinuousLinearMap.id ℝ (Coord n) := by
    ext x i
    simp [lin_apply, Matrix.smul_mulVec]
  have hcov : (a • (1 : Mat n)) * G * (a • (1 : Mat n)).transpose = a ^ 2 • G := by
    simp [Matrix.transpose_smul, smul_smul, pow_two]
  have hlinf : (lin (a • (1 : Mat n)) : Coord n → Coord n) = fun x ↦ a • x := by
    funext x
    rw [hlin]
    rfl
  simpa only [hlinf, hcov] using map_lin_multivariateGaussian μ G hG (a • (1 : Mat n))

/-- The sum under the actual independent product law has the sum covariance. -/
theorem map_add_multivariateGaussian {n : ℕ}
    (μ ν : Coord n) (G L : Mat n) (hG : G.PosSemidef) (hL : L.PosSemidef) :
    Measure.map (fun p : Coord n × Coord n ↦ p.1 + p.2)
      ((multivariateGaussian μ G).prod (multivariateGaussian ν L)) =
        multivariateGaussian (μ + ν) (G + L) := by
  change (multivariateGaussian μ G) ∗ (multivariateGaussian ν L) = _
  apply Measure.ext_of_charFun
  ext x
  rw [charFun_conv, charFun_multivariateGaussian hG,
    charFun_multivariateGaussian hL, charFun_multivariateGaussian (hG.add hL),
    ← Complex.exp_add]
  congr 1
  simp only [inner_add_right, Matrix.add_mulVec, dotProduct_add,
    Complex.ofReal_add]
  ring

/-- Independent weighted Gaussian sums with arbitrary real weights and PSD covariances. -/
theorem map_weighted_multivariateGaussian {n : ℕ}
    (μ ν : Coord n) (G L : Mat n) (hG : G.PosSemidef) (hL : L.PosSemidef)
    (a b : ℝ) :
    Measure.map (fun p : Coord n × Coord n ↦ a • p.1 + b • p.2)
      ((multivariateGaussian μ G).prod (multivariateGaussian ν L)) =
        multivariateGaussian (a • μ + b • ν) (a ^ 2 • G + b ^ 2 • L) := by
  change Measure.map ((fun p : Coord n × Coord n ↦ p.1 + p.2) ∘
    Prod.map (fun x ↦ a • x) (fun x ↦ b • x)) _ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    map_smul_multivariateGaussian μ G hG a, map_smul_multivariateGaussian ν L hL b,
    map_add_multivariateGaussian _ _ _ _ (hG.smul (sq_nonneg a)) (hL.smul (sq_nonneg b))]

/-- The all-PSD addition law used in the right-derivative construction. -/
theorem map_add_sqrt_smul_multivariateGaussian {n : ℕ}
    (G L : Mat n) (hG : G.PosSemidef) (hL : L.PosSemidef)
    (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (fun p : Coord n × Coord n ↦ p.1 + Real.sqrt s • p.2)
      ((multivariateGaussian (0 : Coord n) G).prod
        (multivariateGaussian (0 : Coord n) L)) =
      multivariateGaussian (0 : Coord n) (G + s • L) := by
  simpa only [one_smul, one_pow, smul_zero, zero_add, Real.sq_sqrt hs] using
    map_weighted_multivariateGaussian (0 : Coord n) 0 G L hG hL 1 (Real.sqrt s)

end FSC
