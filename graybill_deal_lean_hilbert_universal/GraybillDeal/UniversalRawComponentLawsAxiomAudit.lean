import GraybillDeal.UniversalRawComponentLaws

/-!
# Axiom audit for universal raw component laws

These commands expose the trust boundary of the component-law layer.  The
expected output contains only Lean/Mathlib foundations (`propext`,
`Classical.choice`, and `Quot.sound`) and no project-specific axioms.
-/

namespace GraybillDeal

#print axioms gammaMeasure_half_half_withDensity_id
#print axioms HasLaw.map_withDensity_comp
#print axioms universalRawIndependentComponentMeasure_withDensity_fst
#print axioms TwoNormalSamplesU.hasLaw_universalRawIndependentComponents
#print axioms
  TwoNormalSamplesU.map_universalRawIndependentComponents_withDensity_sq_meanDifference
#print axioms TwoNormalSamplesU.integral_sq_meanDifference

end GraybillDeal
