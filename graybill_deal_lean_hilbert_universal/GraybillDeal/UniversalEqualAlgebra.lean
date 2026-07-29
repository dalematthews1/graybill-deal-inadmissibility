import GraybillDeal.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Algebraic endgame for the equal-size universal argument

This module isolates the finite algebra behind the equal-sample branch of
the limiting-Bayes contradiction.  It contains no measure theory and makes
the two inputs from the preceding transform argument completely explicit.

Let `a > 0` be the common beta shape and put

`p = 2a + 3/2`.

At the centre `r = 1/2`, write `z = θ - 1/2` and
`t = θ(1-θ) = 1/4-z²`.  If `m₂ = E[z²]` and `m₄ = E[z⁴]`, the identity
of the `q = 0` posterior action with `r` gives the two finite Taylor
coefficient identities

`4 p m₂ = 1`

and

`(32/3) p(p+1)(p+2)m₄
  = (4 p m₂)(8 p(p+1)m₂)`.

They imply

`m₂ = 1/(4p)` and `m₄ = 3/(16p(p+2))`.

The mixed `q,r` coefficient of the posterior action is

`(p/a) E[t] - (4p(p+1)/a) E[z²t]`.

Substitution of the two moments reduces this coefficient to

`(p-1)/(4a(p+2))`,

which is strictly positive.  Thus an action which is identically `r` cannot
also have the zero mixed derivative forced by that identity.

The definitions of the three Taylor coefficients below are deliberately
kept separate.  A future analytic module can establish the coefficient
identities from derivatives or power series and then invoke the final
theorem in this file without repeating any algebra.
-/

namespace GraybillDeal

noncomputable section

/-- The kernel exponent in the equal-size problem with common beta shape
`a`. -/
def universalEqualExponent (a : ℝ) : ℝ :=
  2 * a + 3 / 2

/-- The coefficient of `x` in the centered posterior numerator at `q = 0`.
Here `x = r - 1/2`. -/
def universalEqualNumeratorLinearCoefficient
    (p m₂ : ℝ) : ℝ :=
  4 * p * m₂

/-- The coefficient of `x²` in the centered posterior denominator at
`q = 0`. -/
def universalEqualDenominatorQuadraticCoefficient
    (p m₂ : ℝ) : ℝ :=
  8 * p * (p + 1) * m₂

/-- The coefficient of `x³` in the centered posterior numerator at
`q = 0`. -/
def universalEqualNumeratorCubicCoefficient
    (p m₄ : ℝ) : ℝ :=
  (32 / 3) * p * (p + 1) * (p + 2) * m₄

/--
The two coefficient identities obtained by comparing the quotient

`E[z(1-4xz)⁻ᵖ] / E[(1-4xz)⁻ᵖ]`

with the function `x`.

The cubic identity is the ordinary quotient identity `U₃ = U₁ V₂`;
it is stated without division.
-/
structure UniversalEqualQuotientIdentities
    (p m₂ m₄ : ℝ) : Prop where
  linear :
    universalEqualNumeratorLinearCoefficient p m₂ = 1
  cubic :
    universalEqualNumeratorCubicCoefficient p m₄
      =
    universalEqualNumeratorLinearCoefficient p m₂
      * universalEqualDenominatorQuadraticCoefficient p m₂

/--
The two exact centered moments needed by the mixed-coefficient calculation.
-/
structure UniversalEqualMomentCertificate
    (p m₂ m₄ : ℝ) : Prop where
  second : 4 * p * m₂ = 1
  fourth : 16 * p * (p + 2) * m₄ = 3

theorem universalEqualExponent_pos
    {a : ℝ} (ha : 0 < a) :
    0 < universalEqualExponent a := by
  unfold universalEqualExponent
  linarith

theorem universalEqualExponent_gt_one
    {a : ℝ} (ha : 0 < a) :
    1 < universalEqualExponent a := by
  unfold universalEqualExponent
  linarith

theorem universalEqualExponent_add_two_pos
    {a : ℝ} (ha : 0 < a) :
    0 < universalEqualExponent a + 2 := by
  have hp := universalEqualExponent_pos ha
  linarith

/--
The linear and cubic quotient identities imply the two polynomial moment
identities.  This is the cancellation step which, on paper, extracts the
second and fourth moments from the equality of the posterior quotient with
`x`.
-/
theorem UniversalEqualQuotientIdentities.toMomentCertificate
    {p m₂ m₄ : ℝ}
    (h : UniversalEqualQuotientIdentities p m₂ m₄)
    (hp : 0 < p) :
    UniversalEqualMomentCertificate p m₂ m₄ := by
  have hp1 : p + 1 ≠ 0 := by
    positivity
  have hsecond : 4 * p * m₂ = 1 := by
    simpa [universalEqualNumeratorLinearCoefficient] using h.linear
  have hproduct :
      universalEqualNumeratorLinearCoefficient p m₂
          * universalEqualDenominatorQuadraticCoefficient p m₂
        =
      2 * (p + 1) := by
    unfold universalEqualNumeratorLinearCoefficient
      universalEqualDenominatorQuadraticCoefficient
    calc
      (4 * p * m₂) * (8 * p * (p + 1) * m₂)
          =
        (4 * p * m₂) * (2 * (p + 1) * (4 * p * m₂)) := by
          ring
      _ = 2 * (p + 1) := by rw [hsecond]; ring
  have hcubic :
      (32 / 3) * p * (p + 1) * (p + 2) * m₄
        =
      2 * (p + 1) := by
    simpa [universalEqualNumeratorCubicCoefficient, hproduct] using
      h.cubic.trans hproduct
  have hcancel :
      (p + 1) * ((32 / 3) * p * (p + 2) * m₄)
        =
      (p + 1) * 2 := by
    calc
      (p + 1) * ((32 / 3) * p * (p + 2) * m₄)
          =
        (32 / 3) * p * (p + 1) * (p + 2) * m₄ := by ring
      _ = 2 * (p + 1) := hcubic
      _ = (p + 1) * 2 := by ring
  have hcubic' :
      (32 / 3) * p * (p + 2) * m₄ = 2 :=
    mul_left_cancel₀ hp1 hcancel
  refine
    { second := hsecond
      fourth := ?_ }
  nlinarith [hcubic']

/-- Exact second centered moment. -/
theorem UniversalEqualMomentCertificate.second_eq
    {p m₂ m₄ : ℝ}
    (h : UniversalEqualMomentCertificate p m₂ m₄)
    (hp : 0 < p) :
    m₂ = 1 / (4 * p) := by
  have hne : 4 * p ≠ 0 := by positivity
  apply (eq_div_iff hne).2
  nlinarith [h.second]

/-- Exact fourth centered moment. -/
theorem UniversalEqualMomentCertificate.fourth_eq
    {p m₂ m₄ : ℝ}
    (h : UniversalEqualMomentCertificate p m₂ m₄)
    (hp : 0 < p) :
    m₄ = 3 / (16 * p * (p + 2)) := by
  have hne : 16 * p * (p + 2) ≠ 0 := by positivity
  apply (eq_div_iff hne).2
  nlinarith [h.fourth]

/-- Since `t = 1/4-z²`, this is `E[t]`. -/
def universalEqualTFirstMoment (m₂ : ℝ) : ℝ :=
  1 / 4 - m₂

/-- Since `z²t = z²/4-z⁴`, this is `E[z²t]`. -/
def universalEqualZ2TFirstMoment (m₂ m₄ : ℝ) : ℝ :=
  m₂ / 4 - m₄

/--
The mixed coefficient in the physical `q` coordinate.  The factor `1/a`
comes from replacing the normalized variable `q/a` by `q`.
-/
def universalEqualMixedCoefficient
    (a p m₂ m₄ : ℝ) : ℝ :=
  (p / a) * universalEqualTFirstMoment m₂
    - (4 * p * (p + 1) / a)
      * universalEqualZ2TFirstMoment m₂ m₄

/-- The exact value of `E[t]`. -/
theorem UniversalEqualMomentCertificate.tFirstMoment_eq
    {p m₂ m₄ : ℝ}
    (h : UniversalEqualMomentCertificate p m₂ m₄)
    (hp : 0 < p) :
    universalEqualTFirstMoment m₂ = (p - 1) / (4 * p) := by
  rw [universalEqualTFirstMoment, h.second_eq hp]
  have hp0 : p ≠ 0 := ne_of_gt hp
  field_simp [hp0]

/-- The exact value of `E[z²t]`. -/
theorem UniversalEqualMomentCertificate.z2tFirstMoment_eq
    {p m₂ m₄ : ℝ}
    (h : UniversalEqualMomentCertificate p m₂ m₄)
    (hp : 0 < p) :
    universalEqualZ2TFirstMoment m₂ m₄
      = (p - 1) / (16 * p * (p + 2)) := by
  rw [universalEqualZ2TFirstMoment, h.second_eq hp, h.fourth_eq hp]
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp2 : p + 2 ≠ 0 := by positivity
  field_simp [hp0, hp2]
  ring

/--
The load-bearing algebraic identity for the equal-size contradiction.
-/
theorem universalEqualMixedCoefficient_eq
    {a p m₂ m₄ : ℝ}
    (ha : 0 < a) (hp : 0 < p)
    (h : UniversalEqualMomentCertificate p m₂ m₄) :
    universalEqualMixedCoefficient a p m₂ m₄
      =
    (p - 1) / (4 * a * (p + 2)) := by
  rw [universalEqualMixedCoefficient, h.tFirstMoment_eq hp,
    h.z2tFirstMoment_eq hp]
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp2 : p + 2 ≠ 0 := by positivity
  field_simp [ha0, hp0, hp2]
  ring

/--
Direct endgame from the two quotient identities, specialized to the
equal-size exponent `p = 2a+3/2`.
-/
theorem universalEqualMixedCoefficient_eq_of_quotientIdentities
    {a m₂ m₄ : ℝ}
    (ha : 0 < a)
    (h :
      UniversalEqualQuotientIdentities
        (universalEqualExponent a) m₂ m₄) :
    universalEqualMixedCoefficient
        a (universalEqualExponent a) m₂ m₄
      =
    (universalEqualExponent a - 1)
      / (4 * a * (universalEqualExponent a + 2)) := by
  have hp := universalEqualExponent_pos ha
  exact universalEqualMixedCoefficient_eq ha hp
    (h.toMomentCertificate hp)

/-- The mixed coefficient is strictly positive for every common shape
`a > 0`. -/
theorem universalEqualMixedCoefficient_pos_of_quotientIdentities
    {a m₂ m₄ : ℝ}
    (ha : 0 < a)
    (h :
      UniversalEqualQuotientIdentities
        (universalEqualExponent a) m₂ m₄) :
    0 <
      universalEqualMixedCoefficient
        a (universalEqualExponent a) m₂ m₄ := by
  rw [universalEqualMixedCoefficient_eq_of_quotientIdentities ha h]
  have hp1 := universalEqualExponent_gt_one ha
  have hp2 := universalEqualExponent_add_two_pos ha
  exact div_pos (sub_pos.mpr hp1)
    (mul_pos (mul_pos (by norm_num) ha) hp2)

/--
Contradiction form used by a future analytic module: the coefficient cannot
simultaneously be forced to vanish and satisfy the two quotient identities.
-/
theorem universalEqual_no_zero_mixedCoefficient
    {a m₂ m₄ : ℝ}
    (ha : 0 < a)
    (h :
      UniversalEqualQuotientIdentities
        (universalEqualExponent a) m₂ m₄)
    (hzero :
      universalEqualMixedCoefficient
        a (universalEqualExponent a) m₂ m₄ = 0) :
    False := by
  exact (ne_of_gt
    (universalEqualMixedCoefficient_pos_of_quotientIdentities ha h))
    hzero

end

end GraybillDeal
