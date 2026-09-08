import FSC.Definitions
import FSC.Gaussian.PinDefinitions
import FSC.Support.Definitions
import FSC.Analysis.Definitions

#print axioms FSC.cdf_eq_measure
#print axioms FSC.cdf_nonneg
#print axioms FSC.cdf_le_one
#print axioms FSC.thresholdCDF_const
#print axioms FSC.simplex_apply
#print axioms FSC.simplex_eq_scaled_matrix
#print axioms FSC.measurableSet_thresholdEvent
#print axioms FSC.measurableSet_singleEvent
#print axioms FSC.measurableSet_pairEvent
#print axioms FSC.measurableSet_cap
#print axioms FSC.q_self

set_option pp.all true in
#check FSC.cdf_eq_measure
set_option pp.all true in
#check FSC.simplex_eq_scaled_matrix
#print WeakSimplex.IsCorrelation
#print FSC.Peano2
#print FSC.pairCov
#print FSC.pairEvent
#print FSC.q
#print FSC.NoCoincident
#print FSC.supportGradient
