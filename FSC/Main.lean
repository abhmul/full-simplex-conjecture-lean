import FSC.Equality
import FSC.Gaussian.Maximum

/-! The full simplex comparison as literal Gaussian event and finite-maximum probabilities. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FSC

/-- The all-dimensional full simplex comparison for the actual Gaussian lower-orthant measures. -/
theorem lowerOrthant_simplex_le {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    multivariateGaussian (0 : Coord n) (simplex n) (WeakSimplex.lowerOrthant t) ≤
      multivariateGaussian (0 : Coord n) G (WeakSimplex.lowerOrthant t) :=
  (lowerOrthant_le_iff_cdf_le (simplex n) G t).mpr (cdf_simplex_le hn G hG t)

/-- The simplex has the largest upper tail of the finite coordinate maximum. -/
theorem coordinateMax_tail_le_simplex {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    multivariateGaussian (0 : Coord n) G
      {x | t < WeakSimplex.coordinateMax (by omega : 0 < n) x} ≤
    multivariateGaussian (0 : Coord n) (simplex n)
      {x | t < WeakSimplex.coordinateMax (by omega : 0 < n) x} :=
  (coordinateMax_tail_le_iff_cdf_le (by omega) G (simplex n) t).mpr
    (cdf_simplex_le hn G hG t)

/-- At a positive threshold the simplex upper tail is strictly larger for every other correlation. -/
theorem coordinateMax_tail_lt_simplex {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) (ht : 0 < t)
    (hne : G ≠ simplex n) :
    multivariateGaussian (0 : Coord n) G
      {x | t < WeakSimplex.coordinateMax (by omega : 0 < n) x} <
    multivariateGaussian (0 : Coord n) (simplex n)
      {x | t < WeakSimplex.coordinateMax (by omega : 0 < n) x} :=
  (coordinateMax_tail_lt_iff_cdf_lt (by omega) G (simplex n) t).mpr
    (cdf_simplex_lt hn G hG t ht hne)

/-- Equality of these upper tails at any fixed positive threshold characterizes the simplex. -/
theorem coordinateMax_tail_eq_simplex_iff {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) (ht : 0 < t) :
    multivariateGaussian (0 : Coord n) G
        {x | t < WeakSimplex.coordinateMax (by omega : 0 < n) x} =
      multivariateGaussian (0 : Coord n) (simplex n)
        {x | t < WeakSimplex.coordinateMax (by omega : 0 < n) x} ↔
      G = simplex n :=
  (coordinateMax_tail_eq_iff_cdf_eq (by omega) G (simplex n) t).trans
    (cdf_eq_simplex_iff hn G hG t ht)

end FSC
