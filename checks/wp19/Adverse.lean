import FSC.Minimizers.SlopeRigidity
import FSCProbes.SingularTriangle

noncomputable section

namespace FSCChecks.SlopeRigidity

open FSC

/-- The first inductive dimension needs only the already closed two-site comparison. -/
theorem three_site_minimum_slope (G : Mat 3) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (ht : 0 < t)
    (hmin : ∀ H : Mat 3, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t) :
    boundarySlope (simplex 3) t ≤ boundarySlope G t := by
  exact boundarySlope_simplex_le_of_minimum (by norm_num) G hG t ht hmin
    (fun H hH ↦ two_site_compare H hH _)

/-- Neither distinctness nor non-PD nor lower-size uniqueness is a caller premise. -/
theorem three_site_minimum_rigidity (G : Mat 3) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (ht : 0 < t)
    (hmin : ∀ H : Mat 3, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t)
    (hslope : boundarySlope G t = boundarySlope (simplex 3) t) : G = simplex 3 := by
  exact eq_simplex_of_boundarySlope_eq_of_minimum (by norm_num) G hG t ht hmin
    (fun H hH ↦ two_site_compare H hH _) hslope

/-- A nonsimplex three-site minimum would have a strict boundary-slope gap. -/
theorem three_site_minimum_strict_slope (G : Mat 3) (hG : WeakSimplex.IsCorrelation G)
    (t : ℝ) (ht : 0 < t)
    (hmin : ∀ H : Mat 3, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t)
    (hne : G ≠ simplex 3) : boundarySlope (simplex 3) t < boundarySlope G t := by
  refine lt_of_le_of_ne (three_site_minimum_slope G hG t ht hmin) ?_
  intro hs
  exact hne (three_site_minimum_rigidity G hG t ht hmin hs.symm)

/-- The singular triangle's repeated projected reference is covered by two-site comparison. -/
theorem triangle_projected_reference_floor (i : Fin 3) (r : ℝ) :
    cdf (simplex 2) r ≤ capMass
      (projectedNormal FSCProbes.SingularTriangle.gram i) (fun _ ↦ r) := by
  exact projected_reference_floor (by norm_num) _ FSCProbes.SingularTriangle.gram_isCorrelation
    FSCProbes.SingularTriangle.gram_distinct i r (fun H hH ↦ two_site_compare H hH r)

/-- Actual-support differentiation accepts a reference at a tied, nondifferentiable support. -/
theorem redundant_tied_reference_tangent (t : ℝ) (ht : 0 < t) :
    supportGradient FSCProbes.SingularTriangle.redundantNormals ![t, 2 * t]
      (![t, 2 * t] - ![t, t]) ≤
      capMass FSCProbes.SingularTriangle.redundantNormals ![t, 2 * t] ^ 2 /
        capMass FSCProbes.SingularTriangle.redundantNormals ![t, t] -
      capMass FSCProbes.SingularTriangle.redundantNormals ![t, 2 * t] := by
  obtain ⟨U, _, hb, _, hderiv⟩ := FSCProbes.SingularTriangle.redundant_support_C1 t ht
  apply quadratic_support_tangent_of_hasFDerivAt
  · intro j
    fin_cases j <;> simp <;> linarith
  · intro j
    fin_cases j <;> simpa using ht
  · exact hderiv _ hb

theorem redundant_tied_reference_not_differentiable (t : ℝ) :
    ¬DifferentiableAt ℝ
      (fun b : ℝ ↦ capMass FSCProbes.SingularTriangle.redundantNormals ![t, b]) t :=
  FSCProbes.SingularTriangle.not_differentiableAt_tied_support t

end FSCChecks.SlopeRigidity

#print axioms FSCChecks.SlopeRigidity.three_site_minimum_slope
#print axioms FSCChecks.SlopeRigidity.three_site_minimum_rigidity
#print axioms FSCChecks.SlopeRigidity.three_site_minimum_strict_slope
#print axioms FSCChecks.SlopeRigidity.triangle_projected_reference_floor
#print axioms FSCChecks.SlopeRigidity.redundant_tied_reference_tangent
#print axioms FSCChecks.SlopeRigidity.redundant_tied_reference_not_differentiable
