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

set_option pp.all true in
#check FSC.Peano2.hasDerivWithinAt_noiseAverage
