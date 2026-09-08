import FSC.Gaussian.SinglePin

#check FSC.singleResidual_covariance
#check FSC.singleResidual_indep_pin
#check FSC.map_singleResidual_pin
#check FSC.singleLaw_pin_ae
#check FSC.lintegral_singlePin
#check FSC.measure_singlePin

#print axioms FSC.lin_singleResidual_apply
#print axioms FSC.singleResidual_mul_apply
#print axioms FSC.singleResidual_covariance
#print axioms FSC.singleCov_posSemidef
#print axioms FSC.singleResidual_pinned
#print axioms FSC.single_reconstruction
#print axioms FSC.map_singleResidual
#print axioms FSC.map_singleMean_add
#print axioms FSC.covariance_singleResidual_eval
#print axioms FSC.singleResidual_indep_pin
#print axioms FSC.map_pin
#print axioms FSC.map_singleResidual_pin
#print axioms FSC.singleLaw_pin_ae
#print axioms FSC.lintegral_singlePin
#print axioms FSC.measure_singlePin

set_option pp.all true in
#check FSC.map_singleResidual_pin

set_option pp.all true in
#check FSC.lintegral_singlePin
