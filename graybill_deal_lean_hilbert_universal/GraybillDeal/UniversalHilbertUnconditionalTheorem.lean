import GraybillDeal.UniversalHilbertCompleteClass
import GraybillDeal.UniversalRawLawUnconditional

/-!
# Unconditional universal Graybill--Deal inadmissibility

The Hilbert complete-class theorem removes the final decision-theoretic
hypothesis from the existing exact raw-law theorem.  Thus, for every pair
of positive residual degrees of freedom, the literal Graybill--Deal
estimator for two independent normal samples is not universally measurably
admissible.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The canonical Hilbert complete-class theorem, rewritten in the
sample-size shape notation consumed by the raw theorem. -/
theorem
    universalMeasurableFiniteBayesCompleteClassProperty_residualShapes
    {ν₁ ν₂ : ℕ} (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂) :
    UniversalMeasurableFiniteBayesCompleteClassProperty
      (universalReducedObservationReference
        universalReducedLebesgueMeasure
        (universalShape (ν₁ + 1))
        (universalShape (ν₂ + 1)))
      (universalShape (ν₁ + 1))
      (universalShape (ν₂ + 1)) := by
  simpa only
      [universalHilbertDominatingMeasure,
        universalShape_residualDegrees] using
    (universalMeasurableFiniteBayesCompleteClassProperty_halfShapes
      hν₁ hν₂)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Domination of the literal Graybill--Deal estimator by an arbitrary
measurable raw-sample estimator, without restricting the candidate's
syntactic form. -/
def UniversalRawEstimatorRiskDominatesGraybillDeal
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (P : ℝ → NNReal → NNReal → Measure Ω)
    (candidate : Ω → ℝ) : Prop :=
  (∀ (μ : ℝ) (v₁ v₂ : NNReal),
      0 < v₁ → 0 < v₂ →
        sqRisk μ candidate (P μ v₁ v₂)
          ≤
        sqRisk μ
          (universalRawGraybillDealEstimator ν₁ ν₂ X Y)
          (P μ v₁ v₂)) ∧
  ∃ (μ : ℝ) (v₁ v₂ : NNReal),
    0 < v₁ ∧ 0 < v₂ ∧
      sqRisk μ candidate (P μ v₁ v₂)
        <
      sqRisk μ
        (universalRawGraybillDealEstimator ν₁ ν₂ X Y)
        (P μ v₁ v₂)

/-- Ordinary measurable admissibility of the raw Graybill--Deal estimator
against all measurable raw-sample estimators. -/
def IsUniversallyMeasurablyAdmissibleRawGraybillDealAmongAllEstimators
    (ν₁ ν₂ : ℕ)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (P : ℝ → NNReal → NNReal → Measure Ω) : Prop :=
  ¬ ∃ candidate : Ω → ℝ,
    Measurable candidate ∧
      UniversalRawEstimatorRiskDominatesGraybillDeal
        ν₁ ν₂ X Y P candidate

/-- A measurable reduced rule induces a measurable estimator on the raw
sample space. -/
theorem measurable_universalRawReducedEstimator
    {δ : ℝ × ℝ → ℝ} (hδ : Measurable δ)
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j)) :
    Measurable
      (universalRawReducedEstimator δ ν₁ ν₂ X Y) := by
  unfold universalRawReducedEstimator
  exact
    (measurable_sampleMeanN hX).add
      ((measurable_universalRawReducedWeight hδ hX hY).mul
        (measurable_meanDifferenceU hX hY))

/-- For every universal two-normal-sample family with positive residual
degrees of freedom, one measurable rule weakly improves the literal
Graybill--Deal estimator at every parameter and improves it strictly at
some parameter. -/
theorem exists_universalRaw_dominator
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P) :
    ∃ δ : ℝ × ℝ → ℝ,
      Measurable δ ∧
        UniversalRawRiskDominatesGraybillDeal
          ν₁ ν₂ X Y P δ := by
  exact
    exists_universalRaw_dominator_of_completeClass
      hν₁ hν₂ hX hY hfamily
      (universalMeasurableFiniteBayesCompleteClassProperty_residualShapes
        hν₁ hν₂)

/-- The reduced dominator is, in particular, an ordinary measurable
function on the raw sample space that dominates Graybill--Deal. -/
theorem exists_universalRaw_measurableEstimator_dominator
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P) :
    ∃ candidate : Ω → ℝ,
      Measurable candidate ∧
        UniversalRawEstimatorRiskDominatesGraybillDeal
          ν₁ ν₂ X Y P candidate := by
  obtain ⟨δ, hδ, hdom⟩ :=
    exists_universalRaw_dominator
      hν₁ hν₂ hX hY hfamily
  refine
    ⟨universalRawReducedEstimator δ ν₁ ν₂ X Y,
      measurable_universalRawReducedEstimator hδ hX hY, ?_⟩
  simpa only
      [UniversalRawEstimatorRiskDominatesGraybillDeal,
        UniversalRawRiskDominatesGraybillDeal] using hdom

/-- The unconditional sample-size-universal theorem: the literal
Graybill--Deal estimator is not universally measurably admissible for any
two independent normal samples having positive residual degrees of
freedom. -/
theorem universalRawGraybillDeal_not_admissible
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P) :
    ¬ IsUniversallyMeasurablyAdmissibleRawGraybillDeal
      ν₁ ν₂ X Y P := by
  exact
    universalRawGraybillDeal_not_admissible_of_completeClass
      hν₁ hν₂ hX hY hfamily
      (universalMeasurableFiniteBayesCompleteClassProperty_residualShapes
        hν₁ hν₂)

/-- The same conclusion in the ordinary decision class of all measurable
raw-sample estimators. -/
theorem
    universalRawGraybillDeal_not_admissible_among_all_measurableEstimators
    {ν₁ ν₂ : ℕ}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    {P : ℝ → NNReal → NNReal → Measure Ω}
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j))
    (hfamily : IsUniversalTwoNormalSampleFamily ν₁ ν₂ X Y P) :
    ¬
      IsUniversallyMeasurablyAdmissibleRawGraybillDealAmongAllEstimators
        ν₁ ν₂ X Y P := by
  intro hadmissible
  exact hadmissible
    (exists_universalRaw_measurableEstimator_dominator
      hν₁ hν₂ hX hY hfamily)

end

end GraybillDeal
