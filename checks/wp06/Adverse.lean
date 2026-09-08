import FSC.Support.QuadraticTangent
import FSCProbes.SingularTriangle

noncomputable section

open FSC FSCProbes.SingularTriangle

namespace FSCChecks.WP06

/-- The reference ties two identical normals; the actual supports remain distinct. -/
theorem tied_reference_tangent (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    supportGradient redundantNormals ![t, 2 * t] (![t, 2 * t] - ![r, r]) ≤
      capMass redundantNormals ![t, 2 * t] ^ 2 / capMass redundantNormals ![r, r] -
        capMass redundantNormals ![t, 2 * t] := by
  apply quadratic_support_tangent
  · intro j
    have hs : ‖redundantNormals j‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [redundantNormals]
    nlinarith [norm_nonneg (redundantNormals j)]
  · intro j
    fin_cases j <;> simp <;> positivity
  · intro j
    fin_cases j <;> simpa using hr
  · intro j k hjk
    constructor <;> intro _ <;>
      fin_cases j <;> fin_cases k <;> simp at hjk ⊢ <;> linarith

theorem tied_reference_still_not_differentiable (r : ℝ) :
    ¬DifferentiableAt ℝ (fun a : ℝ ↦ capMass redundantNormals ![r, a]) r :=
  not_differentiableAt_tied_support r

/-- There is no nonempty-index or positive-dimension assumption in the tangent theorem. -/
theorem empty_zero_dimensional_tangent (w : Fin 0 → Coord 0) (b c : Fin 0 → ℝ) :
    supportGradient w b (b - c) ≤ capMass w b ^ 2 / capMass w c - capMass w b := by
  apply quadratic_support_tangent
  all_goals intro i; exact Fin.elim0 i

end FSCChecks.WP06

#print axioms FSCChecks.WP06.tied_reference_tangent
#print axioms FSCChecks.WP06.tied_reference_still_not_differentiable
#print axioms FSCChecks.WP06.empty_zero_dimensional_tangent
