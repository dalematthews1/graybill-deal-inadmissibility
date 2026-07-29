import GraybillDeal.UniversalRawRiskTransport

/-!
# Axiom audit for the universal raw-risk transport

These commands make the trust boundary of the raw-sample layer explicit.
They should report only Lean/Mathlib foundations (in particular,
`propext`, `Classical.choice`, and `Quot.sound`) and no project-specific
axioms.
-/

namespace GraybillDeal

#print axioms universalRawReducedCoordinates_eq_summary
#print axioms rawWeightedEstimator_eq_oracle_decomposition
#print axioms TwoNormalSamplesU.integrable_sq_universalRawOracleError
#print axioms TwoNormalSamplesU.integral_universalRawOracleError
#print axioms universalRaw_sqRisk_sub_graybillDeal_eq_reduced
#print axioms universalRaw_sqRisk_lt_graybillDeal_of_reduced
#print axioms universalRaw_sqRisk_le_graybillDeal_of_reduced

end GraybillDeal
