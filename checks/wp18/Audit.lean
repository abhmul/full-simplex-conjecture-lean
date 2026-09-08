import FSC.Minimizers.Exclusions

#print axioms FSC.replacementScore_apply
#print axioms FSC.replacementCov_isCorrelation
#print axioms FSC.map_replacementScore
#print axioms FSC.replacementScore_preimage
#print axioms FSC.cdf_replacementCov
#print axioms FSC.duplicate_coordinates_ae
#print axioms FSC.cdf_replacementCov_of_duplicate
#print axioms FSC.allOnes_le_smul_one
#print axioms FSC.exists_pos_sub_allOnes_posSemidef
#print axioms FSC.exists_cdf_lt_of_duplicate
#print axioms FSC.distinctScores_of_cdf_minimum
#print axioms FSC.not_posDef_of_cdf_minimum
#print axioms FSC.cdf_minimum_distinct_not_posDef

set_option pp.all true in
#check FSC.cdf_replacementCov_of_duplicate
set_option pp.all true in
#check FSC.cdf_minimum_distinct_not_posDef
