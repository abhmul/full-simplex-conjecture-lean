import FSC.Simplex.Recursion
import Mathlib.Tactic.FinCases

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace FSCProbes.SimplexRecursion

theorem triangle_recursion (t : ℝ) (ht : 0 < t) :
    HasDerivAt (FSC.cdf (FSC.simplex 3))
      (3 * WeakSimplex.normalPDF t * FSC.cdf (FSC.simplex 2) (t * Real.sqrt 3)) t := by
  convert FSC.hasDerivAt_simplex_cdf (by norm_num : 3 ≤ 3) t ht using 1
  norm_num

theorem triangle_pin_actual_antipodal (i : Fin 3) (t : ℝ) :
    (FSC.singleLaw (FSC.simplex 3) i t).map
      (fun x ↦ FSC.simplexPinShift (m := 2) t + FSC.lin (FSC.simplexPinMatrix i) x) =
        multivariateGaussian (0 : FSC.Coord 2) (FSC.simplex 2) ∧
      FSC.simplex 2 0 1 = -1 := by
  refine ⟨FSC.map_simplex_singleLaw (by norm_num) i t, ?_⟩
  norm_num [FSC.simplex_apply (by norm_num : 2 ≤ 2)]

def repeatPair (k : Fin 4) : Fin 2 := if k.val < 2 then 0 else 1

theorem repeatPair_surjective : Function.Surjective repeatPair := by
  intro j
  fin_cases j
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

/-- Exact repeated antipodal event, with all four equal supports tied in pairs. -/
theorem repeated_antipodal_mass {d : ℕ} (u : FSC.Coord d) (r : ℝ) :
    FSC.capMass ((fun j : Fin 2 ↦ if j = 0 then u else -u) ∘ repeatPair)
      (fun _ ↦ r) = FSC.capMass (fun j : Fin 2 ↦ if j = 0 then u else -u) (fun _ ↦ r) := by
  unfold FSC.capMass
  rw [show (fun _ : Fin 4 ↦ r) = (fun _ : Fin 2 ↦ r) ∘ repeatPair from rfl,
    FSC.cap_reindex_surjective _ _ _ repeatPair_surjective]

theorem antipodal_reference_floor {d : ℕ} (u : FSC.Coord d) (hu : ‖u‖ = 1) (r : ℝ)
    (hcompare : ∀ G : FSC.Mat 4, WeakSimplex.IsCorrelation G →
      FSC.cdf (FSC.simplex 4) r ≤ FSC.cdf G r) :
    FSC.cdf (FSC.simplex 4) r ≤
      FSC.capMass (fun j : Fin 2 ↦ if j = 0 then u else -u) (fun _ ↦ r) := by
  apply FSC.reference_floor_of_comparison _ _ (by norm_num) r hcompare
  intro j
  split_ifs <;> simpa using hu

end FSCProbes.SimplexRecursion

#print axioms FSCProbes.SimplexRecursion.triangle_recursion
#print axioms FSCProbes.SimplexRecursion.triangle_pin_actual_antipodal
#print axioms FSCProbes.SimplexRecursion.repeated_antipodal_mass
#print axioms FSCProbes.SimplexRecursion.antipodal_reference_floor
