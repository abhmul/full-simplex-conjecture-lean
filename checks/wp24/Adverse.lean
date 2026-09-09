import FSC.Gaussian.Maximum
import FSC.Simplex.BaseCases

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FSCChecks.WP24

open FSC

/-- Complementation preserves the actual atom at the threshold: the tail is strictly greater. -/
theorem zero_covariance_zero_tail :
    multivariateGaussian (0 : Coord 2) (0 : Mat 2)
      {x | (0 : ℝ) < WeakSimplex.coordinateMax (by norm_num : 0 < 2) x} = 0 := by
  rw [multivariateGaussian_zero_cov]
  simp [WeakSimplex.coordinateMax]

theorem zero_covariance_negative_tail :
    multivariateGaussian (0 : Coord 2) (0 : Mat 2)
      {x | (-1 : ℝ) < WeakSimplex.coordinateMax (by norm_num : 0 < 2) x} = 1 := by
  rw [multivariateGaussian_zero_cov]
  simp [WeakSimplex.coordinateMax]

/-- The nonpositive branch has the maximal possible simplex upper tail in every allowed dimension. -/
theorem simplex_nonpositive_tail {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (ht : t ≤ 0) :
    multivariateGaussian (0 : Coord n) (simplex n)
      {x | t < WeakSimplex.coordinateMax (by omega : 0 < n) x} = 1 := by
  rw [probability_coordinateMax_tail, ← cdf_eq_measure, simplex_cdf_nonpos hn t ht]
  simp

/-- The exact all-real two-site comparison is transported in the reversed upper-tail direction. -/
theorem two_site_tail_direction (G : Mat 2) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    multivariateGaussian (0 : Coord 2) G
      {x | t < WeakSimplex.coordinateMax (by norm_num : 0 < 2) x} ≤
    multivariateGaussian (0 : Coord 2) (simplex 2)
      {x | t < WeakSimplex.coordinateMax (by norm_num : 0 < 2) x} :=
  (coordinateMax_tail_le_iff_cdf_le (by norm_num) G (simplex 2) t).mpr
    (two_site_compare G hG t)

theorem two_site_strict_tail_direction (G : Mat 2) (hG : WeakSimplex.IsCorrelation G)
    (hne : G ≠ simplex 2) (t : ℝ) (ht : 0 < t) :
    multivariateGaussian (0 : Coord 2) G
      {x | t < WeakSimplex.coordinateMax (by norm_num : 0 < 2) x} <
    multivariateGaussian (0 : Coord 2) (simplex 2)
      {x | t < WeakSimplex.coordinateMax (by norm_num : 0 < 2) x} :=
  (coordinateMax_tail_lt_iff_cdf_lt (by norm_num) G (simplex 2) t).mpr
    (two_site_strict G hG hne t ht)

end FSCChecks.WP24

#print axioms FSCChecks.WP24.zero_covariance_zero_tail
#print axioms FSCChecks.WP24.zero_covariance_negative_tail
#print axioms FSCChecks.WP24.simplex_nonpositive_tail
#print axioms FSCChecks.WP24.two_site_tail_direction
#print axioms FSCChecks.WP24.two_site_strict_tail_direction
