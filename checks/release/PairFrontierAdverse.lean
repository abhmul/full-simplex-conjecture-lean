import FSC
import FSCProbes.SingularTriangle

/-! The full-coordinate frontier is not null under a pair law: the pinned
coordinates are deterministic boundary coordinates. This is the raw PROBES
negative statement check, specialized to the actual singular triangle law. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FSCChecks.PairFrontier

open FSC FSCProbes.SingularTriangle

theorem pairMean_01_explicit (t : ℝ) :
    pairMean gram 0 1 t t = WeakSimplex.Coord.ofFun ![t, t, t / 5] := by
  ext i
  fin_cases i <;> norm_num [pairMean, pairAlpha, pairBeta, gram]
  ring

theorem pairMean_01_mem_full_frontier (t : ℝ) (ht : 0 < t) :
    pairMean gram 0 1 t t ∈ frontier (WeakSimplex.lowerOrthant t) := by
  rw [pairMean_01_explicit, frontier_eq_closure_inter_closure]
  refine ⟨subset_closure ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
    linarith
  · apply Metric.mem_closure_iff.mpr
    intro ε hε
    let x : Coord 3 := WeakSimplex.Coord.ofFun ![t + ε / 2, t, t / 5]
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have h₀ := hx 0
      change t + ε / 2 ≤ t at h₀
      linarith
    · have hsq : ‖WeakSimplex.Coord.ofFun ![t, t, t / 5] - x‖ ^ 2 = (ε / 2) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        norm_num [x, Fin.sum_univ_succ]
      have hn : ‖WeakSimplex.Coord.ofFun ![t, t, t / 5] - x‖ = ε / 2 := by
        nlinarith [norm_nonneg (WeakSimplex.Coord.ofFun ![t, t, t / 5] - x)]
      simpa only [dist_eq_norm, hn] using (show ε / 2 < ε by linarith)

/-- The actual canonical pair law gives mass one to the full orthant frontier. -/
theorem pairLaw_full_frontier_mass_one (t : ℝ) (ht : 0 < t) :
    pairLaw gram 0 1 t t (frontier (WeakSimplex.lowerOrthant t)) = 1 := by
  rw [pairLaw_01]
  simp [pairMean_01_mem_full_frontier t ht]

/-- Dropping the exclusion of pinned coordinates makes the frontier-null claim false. -/
theorem pairLaw_full_frontier_not_null (t : ℝ) (ht : 0 < t) :
    pairLaw gram 0 1 t t (frontier (WeakSimplex.lowerOrthant t)) ≠ 0 := by
  rw [pairLaw_full_frontier_mass_one t ht]
  exact one_ne_zero

end FSCChecks.PairFrontier

#check FSCChecks.PairFrontier.pairLaw_full_frontier_mass_one
#print axioms FSCChecks.PairFrontier.pairMean_01_explicit
#print axioms FSCChecks.PairFrontier.pairMean_01_mem_full_frontier
#print axioms FSCChecks.PairFrontier.pairLaw_full_frontier_mass_one
#print axioms FSCChecks.PairFrontier.pairLaw_full_frontier_not_null
