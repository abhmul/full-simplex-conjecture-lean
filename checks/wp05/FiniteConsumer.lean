import FSC.Analysis.FinitePartialDerivatives

namespace FSCChecks.WP05

/-- Empty support coordinates are handled without a nonemptiness hypothesis. -/
theorem empty_input_C2 (f : (Fin 0 → ℝ) → ℝ) : ContDiff ℝ 2 f := by
  apply FSC.contDiff_two_pi_of_partials (p := fun _ _ ↦ 0)
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- Three-coordinate consumer with mixed and quadratic terms and actual slice derivatives. -/
theorem three_coordinate_C2 :
    ContDiff ℝ 2 (fun y : Fin 3 → ℝ ↦ y 0 * y 1 + (y 2) ^ 2) := by
  apply FSC.contDiff_two_pi_of_partials
    (p := fun y i ↦ if i = 0 then y 1 else if i = 1 then y 0 else 2 * y 2)
  · intro i y
    fin_cases i
    · simpa using ((hasDerivAt_id (y 0)).mul_const (y 1)).add_const ((y 2) ^ 2)
    · simpa using ((hasDerivAt_id (y 1)).const_mul (y 0)).add_const ((y 2) ^ 2)
    · simpa [pow_two, two_mul] using
        ((hasDerivAt_id (y 2)).mul (hasDerivAt_id (y 2))).const_add (y 0 * y 1)
  · intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    · exact contDiff_apply ℝ ℝ 1
    · exact contDiff_apply ℝ ℝ 0
    · exact contDiff_const.mul (contDiff_apply ℝ ℝ 2)

end FSCChecks.WP05

#check @FSCChecks.WP05.empty_input_C2
#check @FSCChecks.WP05.three_coordinate_C2
#print axioms FSCChecks.WP05.empty_input_C2
#print axioms FSCChecks.WP05.three_coordinate_C2
