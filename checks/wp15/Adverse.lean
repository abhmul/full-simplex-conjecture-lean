import FSC.Minimizers.FiniteDirections

noncomputable section

namespace FSCChecks.WP15

/-- A valid low-pressure row has a strictly negative affine deficit. -/
theorem negative_signed_row :
    (3 : ℝ) * (1 / 8) - 1 ≤ 1 - Real.sqrt (3 / 4) / FSC.referenceRatio 3 ∧
      1 - Real.sqrt (3 / 4) / FSC.referenceRatio 3 < 0 := by
  have hsq : Real.sqrt (3 / 4 : ℝ) ^ 2 = 3 / 4 := Real.sq_sqrt (by norm_num)
  have href := FSC.referenceRatio_sq (show 3 ≤ 3 by omega)
  have hR := FSC.referenceRatio_pos (show 3 ≤ 3 by omega)
  constructor
  · have h := FSC.signed_row_le (show 3 ≤ 3 by omega) (Real.sqrt (3 / 4)) (1 / 8)
      (by rw [hsq]; norm_num)
    norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 2 = 1 by norm_num, one_mul] at h
    linarith only [h]
  · have hlt : FSC.referenceRatio 3 < Real.sqrt (3 / 4) := by
      norm_num at href
      nlinarith [Real.sqrt_nonneg (3 / 4 : ℝ)]
    have hdiv : 1 < Real.sqrt (3 / 4) / FSC.referenceRatio 3 :=
      (lt_div_iff₀ hR).mpr (by simpa using hlt)
    linarith

/-- Saturating the row covariance bound alone is not signed-loss equality. -/
theorem saturated_low_row_strict :
    (3 : ℝ) * (1 / 8) - 1 < 1 - Real.sqrt (3 / 4) / FSC.referenceRatio 3 := by
  refine lt_of_le_of_ne negative_signed_row.1 ?_
  intro heq
  have h := (FSC.signed_row_equality (show 3 ≤ 3 by omega)
    (Real.sqrt (3 / 4)) (1 / 8) (by rw [Real.sq_sqrt (by norm_num)]; norm_num)).mp
      (by convert heq.symm using 1 <;> norm_num)
  norm_num at h

theorem uniform_row_equality :
    (3 : ℝ) * (1 / 3) - 1 = 1 - FSC.referenceRatio 3 / FSC.referenceRatio 3 := by
  rw [div_self (FSC.referenceRatio_pos (show 3 ≤ 3 by omega)).ne']
  norm_num

/-- At the antipodal two-site law every pair weight vanishes, so kappa may not be divided by. -/
theorem antipodal_zero_kappa (t : ℝ) :
    FSC.kappa (Matrix.vecMulVec (![1, -1] : Fin 2 → ℝ) ![1, -1]) t = 0 := by
  simp [FSC.kappa, FSC.rowK, Fin.sum_univ_two, FSC.q, Matrix.vecMulVec_apply]

/-- The one-sided minimum sign remains valid for a path with nonzero right slope. -/
theorem positive_right_slope :
    HasDerivWithinAt (fun s : ℝ ↦ s) 1 (Set.Ici 0) 0 ∧ (0 : ℝ) ≤ 1 := by
  have hD := (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt (s := Set.Ici 0)
  exact ⟨hD, FSC.right_derivative_nonneg_of_minimum hD (fun _ hs ↦ hs)⟩

end FSCChecks.WP15

#print axioms FSCChecks.WP15.negative_signed_row
#print axioms FSCChecks.WP15.saturated_low_row_strict
#print axioms FSCChecks.WP15.uniform_row_equality
#print axioms FSCChecks.WP15.antipodal_zero_kappa
#print axioms FSCChecks.WP15.positive_right_slope
