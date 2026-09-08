import FSC.Simplex.Recursion
import FSC.Threshold.LinearBarrier

/-! Positive contacts of the actual CDFs and the final equality contract. -/

noncomputable section

namespace FSC

/-- Comparison on positive thresholds suffices to identify the two actual slopes at contact. -/
theorem boundarySlope_eq_of_cdf_touch {n : ℕ} (hn : 2 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hd : DistinctScores G) (t : ℝ) (ht : 0 < t)
    (hcomp : ∀ s, 0 < s → cdf (simplex n) s ≤ cdf G s)
    (heq : cdf G t = cdf (simplex n) t) :
    boundarySlope G t = boundarySlope (simplex n) t := by
  exact slope_eq_of_touch (cdf G) (cdf (simplex n)) _ _ t ht hcomp heq
    (hasDerivAt_cdf G hG hd t ht)
    (hasDerivAt_cdf (simplex n) (simplex_isCorrelation hn) (simplex_distinct hn) t ht)

end FSC
