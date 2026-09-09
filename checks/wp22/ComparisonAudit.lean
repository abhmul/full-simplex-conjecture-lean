import FSC.Comparison

#check FSC.cdf_simplex_le
#print axioms FSC.cdf_simplex_le
#print axioms FSC.cdf_simplex_le_of_lower

namespace FSC.ReleaseComparisonChecks

/-- All duplicated scores and rank one are allowed at every real threshold. -/
theorem allOnes_compare {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    cdf (simplex n) t ≤ cdf (WeakSimplex.allOnesMatrix n) t := by
  apply cdf_simplex_le hn _
  refine ⟨?_, fun _ ↦ rfl⟩
  have heq : WeakSimplex.allOnesMatrix n =
      Matrix.vecMulVec (fun _ : Fin n ↦ (1 : ℝ)) (fun _ : Fin n ↦ (1 : ℝ)) := by
    ext i j
    simp [Matrix.vecMulVec]
  rw [heq]
  exact rankOne_posSemidef _

theorem two_site_all_real (G : Mat 2) (hG : WeakSimplex.IsCorrelation G) (t : ℝ) :
    cdf (simplex 2) t ≤ cdf G t := cdf_simplex_le (by omega) G hG t

end FSC.ReleaseComparisonChecks

#print axioms FSC.ReleaseComparisonChecks.allOnes_compare
#print axioms FSC.ReleaseComparisonChecks.two_site_all_real
