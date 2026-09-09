import FSC.Minimizers.SlopeRigidity
import FSC.Compactness
import FSC.Threshold.LinearBarrier
import FSC.Simplex.BaseCases

/-! The full all-correlation, all-threshold simplex comparison by the strict compact barrier. -/

noncomputable section

namespace FSC

/-- One induction step; the lower-size comparison supplies every actual reference floor. -/
theorem cdf_simplex_le_of_lower {n : ℕ} (hn : 3 ≤ n)
    (hprev : ∀ H : Mat (n - 1), WeakSimplex.IsCorrelation H →
      ∀ t : ℝ, cdf (simplex (n - 1)) t ≤ cdf H t)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    cdf (simplex n) t ≤ cdf G t := by
  let K := {H : Mat n // WeakSimplex.IsCorrelation H}
  letI : CompactSpace K := compactSpace_correlations n
  letI : Nonempty K := ⟨⟨G, hG⟩⟩
  have hsimplex := simplex_isCorrelation (by omega : 2 ≤ n)
  have hD : Continuous (cdf (simplex n)) := by
    have hpair : Continuous (fun s : ℝ ↦ (⟨simplex n, hsimplex⟩, s) : ℝ → K × ℝ) :=
      continuous_const.prodMk continuous_id
    have hc := (continuous_cdf_on_correlations (n := n)).comp hpair
    simpa only [Function.comp_def] using hc
  have hbarrier := compact_slope_comparison
    (fun H : K ↦ cdf H.1) (cdf (simplex n)) (boundarySlope (simplex n))
    (continuous_cdf_on_correlations (n := n)) hD
    (fun H s ↦ ⟨cdf_nonneg H.1 s, cdf_le_one H.1 s⟩)
    (fun s ↦ ⟨cdf_nonneg (simplex n) s, cdf_le_one (simplex n) s⟩)
    (simplex_cdf_nonpos (by omega) 0 le_rfl)
    (fun s hs ↦ hasDerivAt_cdf (simplex n) hsimplex (simplex_distinct (by omega)) s hs)
    (by
      intro H s hs hmin
      have hminimum : ∀ J : Mat n, WeakSimplex.IsCorrelation J → cdf H.1 s ≤ cdf J s :=
        fun J hJ ↦ hmin ⟨J, hJ⟩
      have hd := distinctScores_of_cdf_minimum (by omega) H.1 H.2 s hs hminimum
      exact ⟨boundarySlope H.1 s, hasDerivAt_cdf H.1 H.2 hd s hs,
        boundarySlope_simplex_le_of_minimum hn H.1 H.2 s hs hminimum
          (fun J hJ ↦ hprev J hJ _)⟩)
  by_cases ht : t ≤ 0
  · exact comparison_nonpos (by omega) G t ht
  · exact hbarrier ⟨G, hG⟩ t (le_of_not_ge ht)

/-- Full simplex comparison for every PSD correlation and every real threshold. -/
theorem cdf_simplex_le {n : ℕ} (hn : 2 ≤ n)
    (G : Mat n) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    cdf (simplex n) t ≤ cdf G t := by
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    by_cases htwo : n = 2
    · subst n
      exact two_site_compare G hG t
    have hn3 : 3 ≤ n := by omega
    exact cdf_simplex_le_of_lower hn3
      (fun H hH s ↦ ih (n - 1) (by omega) (by omega) H hH s) G hG t

end FSC
