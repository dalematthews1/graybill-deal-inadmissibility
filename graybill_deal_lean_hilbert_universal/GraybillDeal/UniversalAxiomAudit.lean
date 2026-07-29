import GraybillDeal.UniversalCompleteClassBridge

/-!
# Axiom audit for the universal analytic and decision-theoretic endgame

This file is intentionally not imported by the project root: its purpose
is to make Lean print the axiom dependencies of the principal theorems.
No result below should depend on a project-specific axiom.
-/

namespace GraybillDeal

#print axioms UniversalPosteriorIdentity.unequal_false
#print axioms UniversalPosteriorIdentity.equal_impossible
#print axioms no_universalPosteriorIdentity
#print axioms no_universalPosteriorIdentity_sampleSizes
#print axioms exists_universalPosteriorIdentity_of_reduced_ae_finitePrior_tendsto
#print axioms universalReducedBaseline_not_admissible_of_completeClass
#print axioms universalReducedBaseline_not_admissible_sampleSizes_of_completeClass

end GraybillDeal
