import FSC.Support.Padding

#print axioms FSC.stdGaussian_null_iff_volume_null
#print axioms FSC.stdGaussian_pos_of_isOpen
#print axioms FSC.capEnergy_pos
#print axioms FSC.cap_smul
#print axioms FSC.integrable_gaussian_majorant
#print axioms FSC.dilationDerivative_bound
#print axioms FSC.capMass_dilate_eq_integral
#print axioms FSC.hasDerivAt_capMass_dilate
#print axioms FSC.capEnergy_eq_of_hasFDerivAt
#print axioms FSC.map_splitCoords_stdGaussian
#print axioms FSC.norm_sq_splitCoords
#print axioms FSC.inner_padNormals
#print axioms FSC.cap_padNormals
#print axioms FSC.capMass_padNormals
#print axioms FSC.integral_sq_standardGaussianReal
#print axioms FSC.integral_sq_norm_stdGaussian
#print axioms FSC.integral_product_padded_energy
#print axioms FSC.capEnergy_padNormals

set_option pp.all true in
#check FSC.hasDerivAt_capMass_dilate
set_option pp.all true in
#check FSC.capEnergy_pos
set_option pp.all true in
#check FSC.capEnergy_padNormals
