import FSC.Analysis.PeanoTaylor

namespace FSCChecks.WP07

/-- A truly vector-domain mixed polynomial exercises the adapter. -/
theorem mixed_quadratic_peano :
    FSC.Peano2 (fun z : Fin 2 → ℝ ↦ z 0 * z 1) 0
      (fderiv ℝ (fun z : Fin 2 → ℝ ↦ z 0 * z 1) 0)
      (fderiv ℝ (fderiv ℝ (fun z : Fin 2 → ℝ ↦ z 0 * z 1)) 0) := by
  apply FSC.peano2_of_contDiffAt
  fun_prop

end FSCChecks.WP07

#check @FSCChecks.WP07.mixed_quadratic_peano
#print axioms FSCChecks.WP07.mixed_quadratic_peano
