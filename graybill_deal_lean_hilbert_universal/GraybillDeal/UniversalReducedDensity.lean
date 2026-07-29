import GraybillDeal.UniversalReducedExperiment
import Mathlib.Probability.Distributions.Gamma

/-!
# The explicit universal reduced density

This file records the algebraic and measure-theoretic target of the raw
normal-sample reduction for arbitrary positive residual shapes `a` and `b`.
It deliberately does not use the older unequal beta--gamma ratio theorem:
that theorem assumes `1 < a` and `1 < b` only to simplify its boundary
bookkeeping, whereas the universal theorem must also cover the shapes
`1 / 2` and `1` arising from samples of sizes two and three.

For `θ,r ∈ (0,1)` and `q > 0`, the risk-weighted reduced density is

```
C(a,b) r^(a-1) (1-r)^(b-1) q^(1/2)
  θ^(b+3/2) (1-θ)^(a+3/2) / B(a,b,r,q,θ)^(a+b+3/2).
```

The observation-only factor is split off below.  The remaining factor is
definitionally the likelihood used by the universal limiting-Bayes
argument.
-/

namespace GraybillDeal

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The normalizing constant in the risk-weighted reduced density. -/
def universalReducedDensityConstant (a b : ℝ) : ℝ :=
  2 ^ (a + b + 3 / 2) * a ^ a * b ^ b
    * Real.Gamma (a + b + 3 / 2)
    / (Real.sqrt (2 * Real.pi) * Real.Gamma a * Real.Gamma b)

/-- The factor in the reduced density which depends on the observation but
not on `θ`. -/
def universalReducedObservationFactor
    (a b r q : ℝ) : ℝ :=
  universalReducedDensityConstant a b
    * r ^ (a - 1) * (1 - r) ^ (b - 1) * q ^ (1 / 2 : ℝ)

/-- The full explicit risk-weighted density on the open reduced sample
space. -/
def universalFullReducedDensity
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) : ℝ :=
  universalReducedObservationFactor a b x.r x.q
    * universalReducedLikelihood a b θ x

/-- The exponential rate before the radial `t` variable is integrated out. -/
def universalRadialRate
    (a b r q θ : ℝ) : ℝ :=
  a * r / θ + b * (1 - r) / (1 - θ) + q / 2

/-- Inverse of the positive-coordinate change
`(g₁,g₂,w) ↦ (r,q,t)`. -/
def universalReducedInverseCoordinates
    (r q t : ℝ) : ℝ × ℝ × ℝ :=
  (r * t, (1 - r) * t, q * t)

/-- The absolute Jacobian of the inverse coordinate map on `t > 0`. -/
def universalReducedInverseJacobian (t : ℝ) : ℝ :=
  t ^ 2

theorem universalReducedInverseJacobian_pos
    {t : ℝ} (ht : 0 < t) :
    0 < universalReducedInverseJacobian t := by
  unfold universalReducedInverseJacobian
  positivity

/-- The denominator `B` is exactly `2 θ (1-θ)` times the radial rate. -/
theorem universalB_eq_two_mul_radialRate
    {a b r q θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    universalB a b r q
        ⟨θ, hθ0.le, hθ1.le⟩
      =
    2 * θ * (1 - θ) * universalRadialRate a b r q θ := by
  unfold universalB universalRadialRate
  field_simp [ne_of_gt hθ0, ne_of_gt (sub_pos.mpr hθ1)]

theorem universalRadialRate_pos
    {a b r q θ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hq : 0 < q) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 < universalRadialRate a b r q θ := by
  unfold universalRadialRate
  have h₁ : 0 < a * r / θ := div_pos (mul_pos ha hr0) hθ0
  have h₂ : 0 < b * (1 - r) / (1 - θ) :=
    div_pos (mul_pos hb (sub_pos.mpr hr1)) (sub_pos.mpr hθ1)
  positivity

theorem universalReducedDensityConstant_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < universalReducedDensityConstant a b := by
  unfold universalReducedDensityConstant
  have hab : 0 < a + b + 3 / 2 := by linarith
  have htwo : 0 < (2 : ℝ) ^ (a + b + 3 / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have haa : 0 < a ^ a := Real.rpow_pos_of_pos ha _
  have hbb : 0 < b ^ b := Real.rpow_pos_of_pos hb _
  have hGab : 0 < Real.Gamma (a + b + 3 / 2) :=
    Real.Gamma_pos_of_pos hab
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  positivity

theorem universalReducedObservationFactor_pos
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 < q) :
    0 < universalReducedObservationFactor a b r q := by
  unfold universalReducedObservationFactor
  have hconst := universalReducedDensityConstant_pos ha hb
  have hrpow : 0 < r ^ (a - 1) := Real.rpow_pos_of_pos hr0 _
  have h1rpow : 0 < (1 - r) ^ (b - 1) :=
    Real.rpow_pos_of_pos (sub_pos.mpr hr1) _
  have hqpow : 0 < q ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hq _
  positivity

theorem universalFullReducedDensity_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    0 < universalFullReducedDensity a b θ x := by
  unfold universalFullReducedDensity
  exact mul_pos
    (universalReducedObservationFactor_pos
      ha hb x.r_pos x.r_lt_one x.q_pos)
    (universalReducedLikelihood_pos ha hb θ x)

/-- The key statistical factorization: after removing a strictly positive
observation-only factor, the exact density is the universal likelihood. -/
theorem universalFullReducedDensity_eq_observationFactor_mul_likelihood
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    universalFullReducedDensity a b θ x
      =
    universalReducedObservationFactor a b x.r x.q
      * universalReducedLikelihood a b θ x :=
  rfl

/-- Expanded pointwise form of the reduced density. -/
theorem universalFullReducedDensity_eq_explicit
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    universalFullReducedDensity a b θ x
      =
    universalReducedDensityConstant a b
      * x.r ^ (a - 1) * (1 - x.r) ^ (b - 1)
      * x.q ^ (1 / 2 : ℝ)
      * ((θ : ℝ) ^ (b + 3 / 2)
          * (1 - (θ : ℝ)) ^ (a + 3 / 2))
      * universalB a b x.r x.q
          (universalInteriorThetaInclusion θ)
          ^ (-(a + b + 3 / 2)) := by
  unfold universalFullReducedDensity universalReducedObservationFactor
    universalReducedLikelihood universalEndpointWeight universalKernel
    universalExponent
  rw [universalInteriorThetaInclusion_coe]
  ring

theorem measurable_universalReducedObservationFactor
    (a b : ℝ) :
    Measurable (fun x : UniversalReducedObservation =>
      universalReducedObservationFactor a b x.r x.q) := by
  unfold universalReducedObservationFactor
  unfold UniversalReducedObservation.r UniversalReducedObservation.q
  fun_prop

theorem measurable_universalReducedLikelihood_explicit
    (a b : ℝ) (θ : UniversalInteriorTheta) :
    Measurable (fun x : UniversalReducedObservation =>
      universalReducedLikelihood a b θ x) := by
  unfold universalReducedLikelihood universalKernel universalB
    universalEndpointWeight universalExponent
  unfold UniversalReducedObservation.r UniversalReducedObservation.q
  fun_prop

theorem measurable_universalFullReducedDensity
    (a b : ℝ) (θ : UniversalInteriorTheta) :
    Measurable (universalFullReducedDensity a b θ) := by
  unfold universalFullReducedDensity
  exact
    (measurable_universalReducedObservationFactor a b).mul
      (measurable_universalReducedLikelihood_explicit a b θ)

/-- Lebesgue measure on the open reduced sample space, obtained by comapping
two-dimensional Lebesgue measure along the subtype inclusion. -/
def universalReducedLebesgueMeasure :
    Measure UniversalReducedObservation :=
  Measure.comap Subtype.val (volume : Measure (ℝ × ℝ))

/-- Absorb the strictly positive observation-only density factor into a
reference measure.  This is the dominating measure used by the
limiting-Bayes argument. -/
def universalReducedObservationReference
    (reference : Measure UniversalReducedObservation)
    (a b : ℝ) : Measure UniversalReducedObservation :=
  reference.withDensity
    (fun x =>
      ENNReal.ofReal
        (universalReducedObservationFactor a b x.r x.q))

theorem measurable_universalReducedObservationFactor_ennreal
    (a b : ℝ) :
    Measurable (fun x : UniversalReducedObservation =>
      ENNReal.ofReal
        (universalReducedObservationFactor a b x.r x.q)) :=
  (measurable_universalReducedObservationFactor a b).ennreal_ofReal

theorem measurable_universalReducedLikelihood_ennreal
    (a b : ℝ) (θ : UniversalInteriorTheta) :
    Measurable (fun x : UniversalReducedObservation =>
      ENNReal.ofReal (universalReducedLikelihood a b θ x)) :=
  (measurable_universalReducedLikelihood_explicit a b θ).ennreal_ofReal

/-- Because its density is everywhere positive on the open sample space,
absorbing the observation factor does not alter almost-everywhere
statements. -/
theorem ae_universalReducedObservationReference_iff
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (reference : Measure UniversalReducedObservation)
    (p : UniversalReducedObservation → Prop) :
    (∀ᵐ x ∂universalReducedObservationReference reference a b, p x)
      ↔
    ∀ᵐ x ∂reference, p x := by
  unfold universalReducedObservationReference
  rw [ae_withDensity_iff
    (measurable_universalReducedObservationFactor_ennreal a b)]
  constructor
  · intro hp
    filter_upwards [hp] with x hx
    exact hx (ENNReal.ofReal_ne_zero_iff.mpr
      (universalReducedObservationFactor_pos
        ha hb x.r_pos x.r_lt_one x.q_pos))
  · intro hp
    filter_upwards [hp] with x hx _
    exact hx

/-- A measure has the exact universal risk-weighted reduced density.

This ordinary proposition is the intended interface for the remaining
change-of-variables proof.  It is not an axiom: downstream theorems must
receive a proof of it from the raw component law. -/
def HasUniversalReducedDensity
    (reference Q : Measure UniversalReducedObservation)
    (a b : ℝ) (θ : UniversalInteriorTheta) : Prop :=
  Q =
    reference.withDensity
      (fun x =>
        ENNReal.ofReal (universalFullReducedDensity a b θ x))

theorem HasUniversalReducedDensity.eq_withDensity
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} {θ : UniversalInteriorTheta}
    (h : HasUniversalReducedDensity reference Q a b θ) :
    Q =
      reference.withDensity
        (fun x =>
          ENNReal.ofReal (universalFullReducedDensity a b θ x)) :=
  h

theorem HasUniversalReducedDensity.likelihood_factorization
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} {θ : UniversalInteriorTheta}
    (h : HasUniversalReducedDensity reference Q a b θ) :
    Q =
      reference.withDensity
        (fun x =>
          ENNReal.ofReal
            (universalReducedObservationFactor a b x.r x.q
              * universalReducedLikelihood a b θ x)) := by
  rw [h]
  congr 1

/-- Exact likelihood rebasing.  Once the positive observation factor is
absorbed into the reference measure, the Radon--Nikodym density is precisely
`universalReducedLikelihood`, with no omitted parameter-dependent factor. -/
theorem hasUniversalReducedDensity_iff_rebasedLikelihood
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta) :
    HasUniversalReducedDensity reference Q a b θ
      ↔
    Q =
      (universalReducedObservationReference reference a b).withDensity
        (fun x =>
          ENNReal.ofReal (universalReducedLikelihood a b θ x)) := by
  unfold HasUniversalReducedDensity
    universalReducedObservationReference universalFullReducedDensity
  let f : UniversalReducedObservation → ℝ≥0∞ :=
    fun x => ENNReal.ofReal
      (universalReducedObservationFactor a b x.r x.q)
  let g : UniversalReducedObservation → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (universalReducedLikelihood a b θ x)
  have hf : Measurable f :=
    measurable_universalReducedObservationFactor_ennreal a b
  have hg : Measurable g :=
    measurable_universalReducedLikelihood_ennreal a b θ
  have hfg :
      (fun x : UniversalReducedObservation =>
        ENNReal.ofReal
          (universalReducedObservationFactor a b x.r x.q
            * universalReducedLikelihood a b θ x))
        = f * g := by
    funext x
    rw [Pi.mul_apply, ENNReal.ofReal_mul
      (universalReducedObservationFactor_pos
        ha hb x.r_pos x.r_lt_one x.q_pos).le]
  rw [hfg, withDensity_mul reference hf hg]

end

end GraybillDeal
