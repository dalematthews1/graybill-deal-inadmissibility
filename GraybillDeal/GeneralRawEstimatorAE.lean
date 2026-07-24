import GraybillDeal.GeneralRawEstimatorCoordinates

/-!
# Almost-everywhere transport to the literal generic estimators

This focused endpoint packages the two estimator-level almost-everywhere
identifications used when transporting the canonical risk comparison back to
the raw Graybill--Deal estimators.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

namespace TwoNormalSamplesN

variable {ν : ℕ}
  {X : Fin 2 → Fin (ν + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {variance : Fin 2 → NNReal}

/-- The canonical baseline expression is the literal Graybill--Deal estimator a.e. -/
theorem ae_eq_rawGraybillDealEstimatorN_of_normal_samples
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      μ
        + oracleCenteredErrorN ν μ variance X ω
        + meanDifferenceN ν X ω
          * (canonicalR
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawPN ν variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))))
      =ᵐ[P]
    rawGraybillDealEstimatorN ν X :=
  h.ae_eq_generalCanonicalBaseEstimator_rawGraybillDealEstimatorN
    hν hvariance₀ hvariance₁

/--
For every fixed perturbation coefficient, the canonical clipped competitor is
the literal clipped Graybill--Deal perturbation a.e.
-/
theorem ae_eq_rawClippedPerturbedEstimatorN_of_normal_samples
    (ε : ℝ)
    (h : TwoNormalSamplesN ν X P μ variance)
    (hν : 9 ≤ ν)
    (hvariance₀ : 0 < (variance 0 : ℝ))
    (hvariance₁ : 0 < (variance 1 : ℝ)) :
    (fun ω =>
      μ
        + oracleCenteredErrorN ν μ variance X ω
        + meanDifferenceN ν X ω
          * (generalCanonicalClippedWeight ε (ν : ℝ)
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))
                (normalRawPN ν variance X ω)
                (normalRawLN ν variance X ω)
                (normalRawVN ν variance X ω)
              - canonicalTheta
                (rawVarianceContrast
                  (variance 0 : ℝ) (variance 1 : ℝ))))
      =ᵐ[P]
    rawClippedPerturbedEstimatorN ε ν X :=
  h.ae_eq_generalCanonicalClippedEstimator_rawClippedPerturbedEstimatorN
    ε hν hvariance₀ hvariance₁

end TwoNormalSamplesN

end

end GraybillDeal
