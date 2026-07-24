import GraybillDeal

/-
Definitive audit: list every axiom the final theorems depend on.
Expected output for each: [propext, Classical.choice, Quot.sound]
(the three standard axioms of Lean/mathlib), and nothing else —
in particular no `sorryAx` and no `Lean.ofReduceBool`.
-/

-- All equal sample sizes n = ν + 1 ≥ 10, with the fixed coefficient ε_ν.
#print axioms GraybillDeal.rawGraybillDealEstimatorN_strictly_dominated
#print axioms GraybillDeal.rawClippedPerturbedEstimatorN_sqRisk_lt_rawGraybillDealEstimatorN
#print axioms GraybillDeal.generalGraybillDealEpsilon_pos

-- The explicit n = 13 construction with ε = 1/2000.
#print axioms GraybillDeal.rawGraybillDealEstimator13_strictly_dominated
#print axioms GraybillDeal.rawClippedPerturbedEstimator13_sqRisk_lt_rawGraybillDealEstimator13
