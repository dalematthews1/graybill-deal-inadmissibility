import GraybillDeal.UniversalConditionalRawTheorem

/-!
# Axiom audit for the conditional universal raw theorem

Every unresolved statistical input in
`UniversalConditionalRawTheorem` is an explicit theorem hypothesis.
These commands verify that the assembled results themselves introduce
no project axiom.
-/

namespace GraybillDeal

#print axioms
  exists_total_canonicalUniversalReduced_dominator_all_scalings_of_completeClass
#print axioms universalRawOracleTheta_realizing
#print axioms universalRaw_sqRisk_le_of_density_domination_lifted
#print axioms universalRaw_sqRisk_lt_of_density_domination_lifted
#print axioms
  exists_universalRaw_reducedEstimator_le_of_completeClass_and_laws
#print axioms
  exists_strict_scaled_parameter_with_realizing_rawVariances_of_completeClass

end GraybillDeal
