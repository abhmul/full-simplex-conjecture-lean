import FSC

/- Foundation milestone coverage only. Final comparison/equality are not implemented. -/
#print axioms FSC.cdf_eq_measure
#print axioms FSC.cdf_nonneg
#print axioms FSC.cdf_le_one
#print axioms FSC.simplex_eq_scaled_matrix
#print axioms FSC.measurableSet_pairEvent
#print axioms FSC.measurableSet_cap
#print axioms FSC.componentwise_compare
#print axioms FSC.componentwise_equality
#print axioms FSC.compact_slope_comparison
#print axioms FSC.slope_eq_of_touch
#print axioms FSC.map_affine_multivariateGaussian
#print axioms FSC.map_add_sqrt_smul_multivariateGaussian
#print axioms FSC.exists_unit_gram
#print axioms FSC.map_gramVectors_stdGaussian
#print axioms FSC.Peano2.hasDerivWithinAt_noiseAverage
#print axioms FSC.measurable_thresholdCDF
#print axioms FSC.thresholdCDF_nonneg
#print axioms FSC.thresholdCDF_le_one
#print axioms FSC.measure_singlePin
#print axioms FSC.singleLaw_pin_ae
#print axioms FSC.contDiff_two_prod_of_partials
#print axioms FSC.peano2_of_contDiffAt
#print axioms FSC.lintegral_pairPin
#print axioms FSC.pairLaw_pin_ae
#print axioms FSC.pairCov_sequential
#print axioms FSC.q_symm
#print axioms FSC.rowK_pos
#print axioms FSC.rowC_pos
#print axioms FSC.kappa_pos
#print axioms FSC.contDiffAt_two_pi_of_partials
#print axioms FSC.hasDerivAt_capMass_dilate
#print axioms FSC.capEnergy_pos
#print axioms FSC.capEnergy_padNormals
#print axioms FSC.lin_pairResidual_sequential
#print axioms FSC.lintegral_normalSlice
#print axioms FSC.capMass_support_C1
#print axioms FSC.isLogConcave_capMeasure
#print axioms FSC.quadratic_support_tangent
#print axioms FSC.cdf_normalizedAdd_eq_noiseAverage
#print axioms FSC.exists_padded_unit_gram_law
#print axioms FSC.map_paddedTangentCoordinates_stdGaussian
#print axioms FSC.gaussian_frontier_thresholdEvent_null
#print axioms FSC.continuous_cdf_on_correlations
#print axioms FSC.exists_cdf_minimizer
#print axioms FSC.map_gramPairSlice_pairLaw
#print axioms FSC.q_eq_projected_slice
#print axioms FSC.peano2_thresholdCDF
#print axioms FSC.thresholdHessian_apply
#print axioms FSC.hasDerivWithinAt_normalizedAdd
#print axioms FSC.hasDerivAt_cdf
#print axioms FSC.simplex_isCorrelation
#print axioms FSC.simplex_cdf_nonpos
#print axioms FSC.two_site_compare
#print axioms FSC.two_site_equality
#print axioms FSC.map_simplex_singleLaw
#print axioms FSC.hasDerivAt_simplex_cdf
#print axioms FSC.exists_correlation_capMass
#print axioms FSC.reference_floor_of_comparison

set_option pp.all true in
#check FSC.Peano2.hasDerivWithinAt_noiseAverage

set_option pp.all true in
#check FSC.hasDerivWithinAt_normalizedAdd
