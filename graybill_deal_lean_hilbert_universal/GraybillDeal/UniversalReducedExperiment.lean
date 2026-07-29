import GraybillDeal.UniversalEndpointReweighting

/-!
# The universal reduced experiment

The complete-class argument is applied on the open parameter interval and
the open statistical sample space

`(θ, r, q) ∈ (0,1) × (0,1) × (0,∞)`.

The observation-only factor in the explicit density is absorbed into the
dominating measure.  The remaining likelihood is therefore precisely

`endpointWeight(θ) * universalKernel(r,q,θ)`.

This is the factor which enters Bayes' formula and the endpoint
reweighting module.
-/

namespace GraybillDeal

open Set

noncomputable section

/-- The genuine (non-compactified) reduced parameter space. -/
abbrev UniversalInteriorTheta := Set.Ioo (0 : ℝ) 1

/-- Inclusion of the open parameter interval into its compactification. -/
def universalInteriorThetaInclusion
    (θ : UniversalInteriorTheta) : UniversalTheta :=
  ⟨(θ : ℝ), θ.property.1.le, θ.property.2.le⟩

@[simp]
theorem universalInteriorThetaInclusion_coe
    (θ : UniversalInteriorTheta) :
    (universalInteriorThetaInclusion θ : ℝ) = (θ : ℝ) :=
  rfl

/-- The statistical reduced sample space.  The boundary `q = 0` is added
later only by continuity of the limiting posterior ratio. -/
abbrev UniversalReducedObservation :=
  {x : ℝ × ℝ // 0 < x.1 ∧ x.1 < 1 ∧ 0 < x.2}

namespace UniversalReducedObservation

def r (x : UniversalReducedObservation) : ℝ :=
  x.1.1

def q (x : UniversalReducedObservation) : ℝ :=
  x.1.2

theorem r_pos (x : UniversalReducedObservation) :
    0 < x.r :=
  x.property.1

theorem r_lt_one (x : UniversalReducedObservation) :
    x.r < 1 :=
  x.property.2.1

theorem q_pos (x : UniversalReducedObservation) :
    0 < x.q :=
  x.property.2.2

theorem q_nonneg (x : UniversalReducedObservation) :
    0 ≤ x.q :=
  (x.q_pos).le

end UniversalReducedObservation

/-- The Graybill--Deal rule in reduced coordinates. -/
def universalReducedBaseline
    (x : UniversalReducedObservation) : ℝ :=
  x.r

/-- Parameter-dependent part of the risk-weighted reduced density, after
the strictly positive observation-only factor is absorbed into the
dominating measure. -/
def universalReducedLikelihood
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) : ℝ :=
  universalEndpointWeight a b
      (universalInteriorThetaInclusion θ)
    * universalKernel a b x.r x.q
      (universalInteriorThetaInclusion θ)

theorem universalReducedLikelihood_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    0 < universalReducedLikelihood a b θ x := by
  apply mul_pos
  · exact universalEndpointWeight_pos θ.property.1 θ.property.2
  · exact universalKernel_pos ha hb x.r_pos x.r_lt_one
      x.q_nonneg _

theorem universalReducedLikelihood_ne_zero
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    universalReducedLikelihood a b θ x ≠ 0 :=
  ne_of_gt (universalReducedLikelihood_pos ha hb θ x)

end

end GraybillDeal
