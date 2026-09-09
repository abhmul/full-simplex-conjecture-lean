import FSC.Comparison

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

/-- At any fixed positive threshold, equality holds exactly at the regular simplex. -/
theorem cdf_eq_simplex_iff {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) (ht : 0 < t) :
    cdf G t = cdf (simplex n) t ↔ G = simplex n := by
  constructor
  · intro heq
    by_cases htwo : n = 2
    · subst n
      exact (two_site_equality G hG t ht).mp heq
    have hn3 : 3 ≤ n := by omega
    have hmin : ∀ H : Mat n, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t := by
      intro H hH
      rw [heq]
      exact cdf_simplex_le hn H hH t
    have hd := distinctScores_of_cdf_minimum (by omega) G hG t ht hmin
    apply eq_simplex_of_boundarySlope_eq_of_minimum hn3 G hG t ht hmin
      (fun H hH ↦ cdf_simplex_le (by omega) H hH _)
    exact boundarySlope_eq_of_cdf_touch hn G hG hd t ht
      (fun s _ ↦ cdf_simplex_le hn G hG s) heq
  · rintro rfl
    rfl

/-- Every nonsimplex correlation has strictly larger CDF at each positive threshold. -/
theorem cdf_simplex_lt {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (ht : 0 < t) (hne : G ≠ simplex n) :
    cdf (simplex n) t < cdf G t := by
  refine lt_of_le_of_ne (cdf_simplex_le hn G hG t) ?_
  intro heq
  exact hne ((cdf_eq_simplex_iff hn G hG t ht).mp heq.symm)

end FSC
