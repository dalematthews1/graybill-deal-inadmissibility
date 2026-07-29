import GraybillDeal.GeneralBetaBridge
import GraybillDeal.GeneralQuadraticBounds

/-!
# A fixed all-variance-ratio Graybill--Deal perturbation coefficient

The reduced-risk theorem supplies, for each residual degree of freedom
`ν ≥ 9`, one positive coefficient that works simultaneously for every
interior variance contrast `|s| < 1`.  This module chooses that coefficient
once and for all as a function of `ν` alone.

This quantifier order is essential at estimator level: the perturbation
coefficient cannot depend on the unknown population variance ratio.
-/

namespace GraybillDeal

noncomputable section

private theorem exists_generalGraybillDealEpsilon
    (ν : ℕ) (hν : 9 ≤ ν) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, |s| < 1 →
        2 * ε
              * generalBtheta
                (centeredBetaKa ((ν : ℝ) / 2)) (ν : ℝ) s
          + ε ^ 2
              * generalCtheta
                (centeredBetaKa ((ν : ℝ) / 2)) (ν : ℝ) s
            < 0 := by
  have hνR : (9 : ℝ) ≤ (ν : ℝ) := by
    exact_mod_cast hν
  exact
    exists_generalReducedRisk_epsilon_unconditional
      (centeredBetaKa ((ν : ℝ) / 2)) ν hν
      (centeredBetaKa_pos (by linarith))

/--
The fixed perturbation coefficient for residual degrees of freedom `ν`.

For `ν ≥ 9` it is a chosen witness of the uniform reduced-risk theorem.
The irrelevant values below the theorem's range are set to zero.
-/
noncomputable def generalGraybillDealEpsilon (ν : ℕ) : ℝ :=
  if hν : 9 ≤ ν then
    Classical.choose (exists_generalGraybillDealEpsilon ν hν)
  else
    0

/-- The fixed coefficient is positive throughout the range `ν ≥ 9`. -/
theorem generalGraybillDealEpsilon_pos
    (ν : ℕ) (hν : 9 ≤ ν) :
    0 < generalGraybillDealEpsilon ν := by
  rw [generalGraybillDealEpsilon, dif_pos hν]
  exact
    (Classical.choose_spec
      (exists_generalGraybillDealEpsilon ν hν)).1

/--
The fixed coefficient gives strictly negative reduced risk simultaneously
for every interior population variance contrast.
-/
theorem generalGraybillDealEpsilon_reduced_neg
    (ν : ℕ) (hν : 9 ≤ ν)
    (s : ℝ) (hs : |s| < 1) :
    2 * generalGraybillDealEpsilon ν
          * generalBtheta
            (centeredBetaKa ((ν : ℝ) / 2)) (ν : ℝ) s
      + generalGraybillDealEpsilon ν ^ 2
          * generalCtheta
            (centeredBetaKa ((ν : ℝ) / 2)) (ν : ℝ) s
        < 0 := by
  rw [generalGraybillDealEpsilon, dif_pos hν]
  exact
    (Classical.choose_spec
      (exists_generalGraybillDealEpsilon ν hν)).2 s hs

end

end GraybillDeal
