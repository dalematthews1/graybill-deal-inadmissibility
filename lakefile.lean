import Lake
open Lake DSL

package «graybill-deal» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

@[default_target]
lean_lib GraybillDeal

/-- Prints the axioms of the final theorems during the build.
Expected output: `propext, Classical.choice, Quot.sound` only. -/
@[default_target]
lean_lib CheckAxioms

/-- Non-vacuity witness for the n = 13 model: constructs the two-sample
normal model on the canonical product space and instantiates the
explicit ε = 1/2000 dominance theorem. -/
@[default_target]
lean_lib ModelWitness

/-- Non-vacuity witness for the general model: for every ν, constructs the
model on `(Fin 2 × Fin (ν+1)) → ℝ` and instantiates the all-n dominance
theorem. -/
@[default_target]
lean_lib ModelWitnessGeneral
