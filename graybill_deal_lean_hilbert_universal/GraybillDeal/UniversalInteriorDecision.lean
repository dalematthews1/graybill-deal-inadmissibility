import GraybillDeal.UniversalAELimitBridge
import GraybillDeal.UniversalDecision
import GraybillDeal.UniversalReducedExperiment

/-!
# Finite-Bayes decision interface on the open parameter interval

The statistical parameter space in the universal Graybill--Deal argument
is the *open* interval `UniversalInteriorTheta = (0,1)`.  Compactification
to `UniversalTheta = [0,1]` is used only after a sequence of finite priors
has been endpoint-reweighted.

This file keeps those two roles separate.

* `PositiveFinitePrior Θ` is a generic, explicitly finite probability
  prior with strictly positive `ℝ≥0` masses.
* `HasPositiveFiniteBayesApproximation` and
  `PositiveFiniteBayesCompleteClassProperty` are generic
  decision-theoretic interfaces.  They contain no complete-class axiom.
* Specializing `Θ` to `UniversalInteriorTheta` gives the precise open
  parameter interface needed by the universal proof.
* `PositiveFinitePrior.toUniversalInteriorFinitePrior` converts an open
  finite prior to the representation used by endpoint reweighting and
  weak compactness.

The last theorem is a convenience wrapper around
`exists_universalPosteriorIdentity_of_ae_finitePrior_tendsto`.  It shows
that an almost-everywhere limit of the genuinely open-parameter finite
Bayes rules supplies the compactified posterior identity.  The
Lehmann--Casella complete-class theorem itself is deliberately not
asserted here.
-/

namespace GraybillDeal

open Filter MeasureTheory Set
open scoped BigOperators NNReal Topology

noncomputable section

variable {Θ X : Type*}

/-- An explicitly finite probability prior with strictly positive
`ℝ≥0` masses.

The positivity field excludes redundant zero-mass presentation points.
The normalization field implies that the presentation is nonempty.
-/
structure PositiveFinitePrior (Θ : Type*) where
  /-- Number of entries in the finite presentation. -/
  card : ℕ
  /-- Parameter value at each entry. -/
  point : Fin card → Θ
  /-- Strictly positive mass at each entry. -/
  weight : Fin card → ℝ≥0
  /-- Every presented mass is strictly positive. -/
  weight_pos : ∀ i, 0 < weight i
  /-- The masses sum to one. -/
  weight_sum : ∑ i, weight i = 1

namespace PositiveFinitePrior

/-- Prior mass times likelihood at one finite support entry. -/
def posteriorWeight
    (π : PositiveFinitePrior Θ)
    (density : Θ → X → ℝ) (x : X)
    (i : Fin π.card) : ℝ :=
  (π.weight i : ℝ) * density (π.point i) x

/-- The finite-prior Bayes action under squared loss. -/
def bayesAction
    (π : PositiveFinitePrior Θ)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (x : X) : ℝ :=
  finiteWeightedMean Finset.univ
    (π.posteriorWeight density x)
    (fun i => target (π.point i))

theorem bayesAction_eq_ratio
    (π : PositiveFinitePrior Θ)
    (density : Θ → X → ℝ)
    (target : Θ → ℝ) (x : X) :
    π.bayesAction density target x
      =
    (∑ i, (π.weight i : ℝ) * density (π.point i) x
          * target (π.point i))
      / ∑ i, (π.weight i : ℝ) * density (π.point i) x := by
  unfold bayesAction posteriorWeight finiteWeightedMean finiteWeightTotal
  rfl

/-- Regard a finite prior on the open interval as an interior finite
prior on the compactified interval.

No endpoint mass is introduced: every support point remains strictly
inside `(0,1)`.
-/
def toUniversalInteriorFinitePrior
    (π : PositiveFinitePrior UniversalInteriorTheta) :
    UniversalInteriorFinitePrior where
  card := π.card
  point i := universalInteriorThetaInclusion (π.point i)
  weight := π.weight
  weight_sum := π.weight_sum
  point_pos i := (π.point i).property.1
  point_lt_one i := (π.point i).property.2

@[simp]
theorem toUniversalInteriorFinitePrior_card
    (π : PositiveFinitePrior UniversalInteriorTheta) :
    π.toUniversalInteriorFinitePrior.card = π.card :=
  rfl

@[simp]
theorem toUniversalInteriorFinitePrior_point
    (π : PositiveFinitePrior UniversalInteriorTheta)
    (i : Fin π.card) :
    π.toUniversalInteriorFinitePrior.point i
      = universalInteriorThetaInclusion (π.point i) :=
  rfl

@[simp]
theorem toUniversalInteriorFinitePrior_weight
    (π : PositiveFinitePrior UniversalInteriorTheta)
    (i : Fin π.card) :
    π.toUniversalInteriorFinitePrior.weight i = π.weight i :=
  rfl

end PositiveFinitePrior

/-- A sequence of positive finite-prior Bayes rules which converges
almost everywhere to an estimator.

The parameter type is generic.  In the universal application it is
specialized to `UniversalInteriorTheta`, not to its compactification.
-/
def HasPositiveFiniteBayesApproximation
    [MeasurableSpace X]
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ) (estimator : X → ℝ) : Prop :=
  ∃ priors : ℕ → PositiveFinitePrior Θ,
    ∀ᵐ x ∂m,
      Tendsto
        (fun j => (priors j).bayesAction density target x)
        atTop (𝓝 (estimator x))

/-- The finite-prior complete-class conclusion as an ordinary generic
property.  This definition does not postulate that the property holds.
-/
def PositiveFiniteBayesCompleteClassProperty
    [MeasurableSpace X]
    (m : Measure X) (density : Θ → X → ℝ)
    (target : Θ → ℝ) : Prop :=
  ∀ estimator : X → ℝ,
    IsAdmissibleDensitySquared m density target estimator →
      HasPositiveFiniteBayesApproximation
        m density target estimator

theorem hasPositiveFiniteBayesApproximation_of_admissible
    [MeasurableSpace X]
    {m : Measure X}
    {density : Θ → X → ℝ}
    {target : Θ → ℝ}
    (hcomplete :
      PositiveFiniteBayesCompleteClassProperty m density target)
    {estimator : X → ℝ}
    (hadmissible :
      IsAdmissibleDensitySquared m density target estimator) :
    HasPositiveFiniteBayesApproximation
      m density target estimator :=
  hcomplete estimator hadmissible

/-- The complete-class property specialized to the genuine open
parameter interval `(0,1)`.
-/
abbrev UniversalInteriorFiniteBayesCompleteClassProperty
    [MeasurableSpace X]
    (m : Measure X)
    (density : UniversalInteriorTheta → X → ℝ)
    (target : UniversalInteriorTheta → ℝ) : Prop :=
  PositiveFiniteBayesCompleteClassProperty m density target

/-- The finite-Bayes approximation conclusion specialized to the genuine
open parameter interval `(0,1)`.
-/
abbrev HasUniversalInteriorFiniteBayesApproximation
    [MeasurableSpace X]
    (m : Measure X)
    (density : UniversalInteriorTheta → X → ℝ)
    (target : UniversalInteriorTheta → ℝ)
    (estimator : X → ℝ) : Prop :=
  HasPositiveFiniteBayesApproximation
    m density target estimator

/-- The endpoint-weighted likelihood extended to the boundary `q = 0`
of the observation space.

The boundary is used only for the continuity argument.  On `q > 0` this
is exactly `universalReducedLikelihood`.
-/
def universalInteriorExtendedLikelihood
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (z : UniversalObservation) : ℝ :=
  universalEndpointWeight a b
      (universalInteriorThetaInclusion θ)
    * universalKernel a b
        (universalObservation_r z)
        (universalObservation_q z)
        (universalInteriorThetaInclusion θ)

theorem universalInteriorExtendedLikelihood_eq_reducedLikelihood
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    universalInteriorExtendedLikelihood a b θ
      (⟨x.r, x.r_pos, x.r_lt_one⟩,
        ⟨x.q, x.q_nonneg⟩)
      =
    universalReducedLikelihood a b θ x :=
  rfl

/-- The finite Bayes action on the open parameter interval agrees
definitionally, up to reassociation of multiplication, with the
`UniversalInteriorFinitePrior` action used by endpoint reweighting.
-/
theorem PositiveFinitePrior.bayesAction_extendedLikelihood_eq_fullReduced
    (π : PositiveFinitePrior UniversalInteriorTheta)
    (a b : ℝ) (z : UniversalObservation) :
    π.bayesAction
        (universalInteriorExtendedLikelihood a b)
        (fun θ => (θ : ℝ)) z
      =
    π.toUniversalInteriorFinitePrior.fullReducedPosteriorAction
      a b (universalObservation_r z) (universalObservation_q z) := by
  unfold PositiveFinitePrior.bayesAction
    PositiveFinitePrior.posteriorWeight
    universalInteriorExtendedLikelihood
    UniversalInteriorFinitePrior.fullReducedPosteriorAction
  congr 1
  funext i
  simp only [PositiveFinitePrior.toUniversalInteriorFinitePrior]
  ring

/-- Open-parameter finite Bayes limits produce the compactified
posterior identity used by the analytic contradiction.

This is only a transport theorem.  Its `haction` premise is the
finite-Bayes approximation conclusion that a separately formalized
complete-class theorem must supply.
-/
theorem exists_universalPosteriorIdentity_of_ae_openFinitePrior_tendsto
    (πs : ℕ → PositiveFinitePrior UniversalInteriorTheta)
    (ρ : Measure UniversalObservation)
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hopen :
      ∀ U : Set UniversalObservation,
        IsOpen U → U.Nonempty → 0 < ρ U)
    (haction :
      ∀ᵐ z ∂ρ,
        Tendsto
          (fun n =>
            (πs n).bayesAction
              (universalInteriorExtendedLikelihood a b)
              (fun θ => (θ : ℝ)) z)
          atTop (𝓝 (universalObservation_r z))) :
    ∃ ν : ProbabilityMeasure UniversalTheta,
      UniversalPosteriorIdentity
        (ν : Measure UniversalTheta) a b := by
  apply exists_universalPosteriorIdentity_of_ae_finitePrior_tendsto
    (fun n => (πs n).toUniversalInteriorFinitePrior)
    ρ ha hb hopen
  filter_upwards [haction] with z hz
  simpa only [
    PositiveFinitePrior.bayesAction_extendedLikelihood_eq_fullReduced
  ] using hz

end

end GraybillDeal
