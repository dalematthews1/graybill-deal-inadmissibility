import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval

/-!
# The reduced kernel in the universal Graybill--Deal argument

This module contains the measure-independent core of the limiting-Bayes
proof, together with the elementary analytic facts needed to integrate the
kernel against an arbitrary probability measure on the compactified
parameter interval `[0,1]`.

The statistical and complete-class arguments live in later modules.  In
particular, this file does not assume admissibility and introduces no
decision-theoretic axiom.
-/

namespace GraybillDeal

open MeasureTheory Set
open scoped BoundedContinuousFunction unitInterval

noncomputable section

/-- The compactified reduced parameter space. -/
abbrev UniversalTheta := unitInterval

/-- The denominator appearing in the reduced risk-weighted density. -/
def universalB (a b r q : ℝ) (θ : UniversalTheta) : ℝ :=
  2 * a * r * (1 - (θ : ℝ))
    + 2 * b * (1 - r) * (θ : ℝ)
    + q * (θ : ℝ) * (1 - (θ : ℝ))

/-- The exponent in the reduced density. -/
def universalExponent (a b : ℝ) : ℝ :=
  a + b + 3 / 2

/-- The likelihood kernel after the endpoint weight has been absorbed into
the prior. -/
def universalKernel (a b r q : ℝ) (θ : UniversalTheta) : ℝ :=
  universalB a b r q θ ^ (-universalExponent a b)

theorem universalB_eq_affine_add (a b r q : ℝ) (θ : UniversalTheta) :
    universalB a b r q θ
      =
    (2 * a * r) * (1 - (θ : ℝ))
      + (2 * b * (1 - r)) * (θ : ℝ)
      + q * (θ : ℝ) * (1 - (θ : ℝ)) := by
  unfold universalB
  ring

/-- The affine part of `universalB` is a convex combination of its endpoint
values; the `q` term is nonnegative. -/
theorem universalB_lower_bound
    {a b r q : ℝ}
    (hq : 0 ≤ q)
    (θ : UniversalTheta) :
    min (2 * a * r) (2 * b * (1 - r))
      ≤ universalB a b r q θ := by
  have hθ0 : 0 ≤ (θ : ℝ) := θ.property.1
  have hθ1 : (θ : ℝ) ≤ 1 := θ.property.2
  have h1θ : 0 ≤ 1 - (θ : ℝ) := sub_nonneg.mpr hθ1
  have hqterm : 0 ≤ q * (θ : ℝ) * (1 - (θ : ℝ)) :=
    mul_nonneg (mul_nonneg hq hθ0) h1θ
  calc
    min (2 * a * r) (2 * b * (1 - r))
        =
      min (2 * a * r) (2 * b * (1 - r)) * (1 - (θ : ℝ))
        + min (2 * a * r) (2 * b * (1 - r)) * (θ : ℝ) := by
          ring
    _ ≤
      (2 * a * r) * (1 - (θ : ℝ))
        + (2 * b * (1 - r)) * (θ : ℝ) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (min_le_left _ _) h1θ)
            (mul_le_mul_of_nonneg_right
              (min_le_right _ _) hθ0)
    _ ≤ universalB a b r q θ := by
      rw [universalB_eq_affine_add]
      linarith

theorem universalB_pos
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q)
    (θ : UniversalTheta) :
    0 < universalB a b r q θ := by
  have har : 0 < 2 * a * r := by positivity
  have hb1r : 0 < 2 * b * (1 - r) := by positivity
  exact lt_of_lt_of_le (lt_min har hb1r)
    (universalB_lower_bound hq θ)

theorem universalKernel_pos
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q)
    (θ : UniversalTheta) :
    0 < universalKernel a b r q θ := by
  exact Real.rpow_pos_of_pos
    (universalB_pos ha hb hr0 hr1 hq θ) _

theorem continuous_universalB_theta (a b r q : ℝ) :
    Continuous (fun θ : UniversalTheta => universalB a b r q θ) := by
  unfold universalB
  fun_prop

theorem continuous_universalKernel_theta
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    Continuous (fun θ : UniversalTheta =>
      universalKernel a b r q θ) := by
  unfold universalKernel
  exact (continuous_universalB_theta a b r q).rpow_const
    (fun θ => Or.inl (ne_of_gt
      (universalB_pos ha hb hr0 hr1 hq θ)))

theorem continuous_universalTheta_mul_kernel
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    Continuous (fun θ : UniversalTheta =>
      (θ : ℝ) * universalKernel a b r q θ) := by
  exact continuous_subtype_val.mul
    (continuous_universalKernel_theta ha hb hr0 hr1 hq)

/-- The denominator kernel as a bounded continuous function. -/
def universalKernelBCF
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    UniversalTheta →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun θ => universalKernel a b r q θ,
      continuous_universalKernel_theta ha hb hr0 hr1 hq⟩

/-- The numerator kernel as a bounded continuous function. -/
def universalNumeratorKernelBCF
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    UniversalTheta →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun θ => (θ : ℝ) * universalKernel a b r q θ,
      continuous_universalTheta_mul_kernel ha hb hr0 hr1 hq⟩

/-- Denominator of the limiting posterior mean. -/
def universalPosteriorDenominator
    (ν : Measure UniversalTheta) (a b r q : ℝ) : ℝ :=
  ∫ θ, universalKernel a b r q θ ∂ν

/-- Numerator of the limiting posterior mean. -/
def universalPosteriorNumerator
    (ν : Measure UniversalTheta) (a b r q : ℝ) : ℝ :=
  ∫ θ, (θ : ℝ) * universalKernel a b r q θ ∂ν

/-- The posterior-mean ratio forced by a limiting-Bayes argument. -/
def universalPosteriorAction
    (ν : Measure UniversalTheta) (a b r q : ℝ) : ℝ :=
  universalPosteriorNumerator ν a b r q
    / universalPosteriorDenominator ν a b r q

theorem integrable_universalKernel
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    Integrable (fun θ : UniversalTheta =>
      universalKernel a b r q θ) ν := by
  change Integrable
    (universalKernelBCF ha hb hr0 hr1 hq : UniversalTheta → ℝ) ν
  exact BoundedContinuousFunction.integrable ν
    (universalKernelBCF ha hb hr0 hr1 hq)

theorem integrable_universalNumeratorKernel
    (ν : Measure UniversalTheta) [IsFiniteMeasure ν]
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    Integrable (fun θ : UniversalTheta =>
      (θ : ℝ) * universalKernel a b r q θ) ν := by
  change Integrable
    (universalNumeratorKernelBCF ha hb hr0 hr1 hq :
      UniversalTheta → ℝ) ν
  exact BoundedContinuousFunction.integrable ν
    (universalNumeratorKernelBCF ha hb hr0 hr1 hq)

theorem universalPosteriorDenominator_pos
    (ν : Measure UniversalTheta) [IsProbabilityMeasure ν]
    {a b r q : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    0 < universalPosteriorDenominator ν a b r q := by
  unfold universalPosteriorDenominator
  rw [integral_pos_iff_support_of_nonneg
    (fun θ => (universalKernel_pos ha hb hr0 hr1 hq θ).le)
    (integrable_universalKernel ν ha hb hr0 hr1 hq)]
  have hsupp :
      Function.support (fun θ : UniversalTheta =>
        universalKernel a b r q θ) = Set.univ := by
    ext θ
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (universalKernel_pos ha hb hr0 hr1 hq θ)
  rw [hsupp]
  simp

end

end GraybillDeal
