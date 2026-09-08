import FSC.Analysis.PartialDerivatives

namespace FSCChecks.WP05

/-- A mixed function needs both coordinate derivatives; the adapter supplies C2. -/
theorem mixed_product_C2 : ContDiff ℝ 2 (fun y : ℝ × ℝ ↦ y.1 * y.2) := by
  apply FSC.contDiff_two_prod_of_partials (p := fun y ↦ y.2) (q := fun y ↦ y.1)
  · intro y
    simpa using (hasDerivAt_id y.1).mul_const y.2
  · intro y
    simpa using (hasDerivAt_id y.2).const_mul y.1
  · exact contDiff_snd
  · exact contDiff_fst

end FSCChecks.WP05

#check @FSCChecks.WP05.mixed_product_C2
#print axioms FSCChecks.WP05.mixed_product_C2
