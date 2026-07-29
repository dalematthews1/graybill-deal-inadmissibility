import GraybillDeal.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Algebra for the universal unequal-sample obstruction

This file isolates the purely real-algebraic part of the limiting-Bayes
argument for unequal sample sizes.  The measure-theoretic layer will
eventually supply a probability measure `ν` and the three centered moments
recorded in `universalUnequalMoment_of_odeMoments`.  No measure or integral is
needed here: those moments are represented by arbitrary real numbers
`m₁`, `m₂`, and `m₃` together with explicit equality hypotheses.

For beta shapes `a,b > 0`, put

* `h = a + b`,
* `p = h + 3/2`,
* `r₀ = b/h`,
* `c = ab/h`, and
* `Z = a - h θ`.

At `(r,q) = (r₀,0)`, the reduced denominator

`B(a,b,r,q,θ) =
  2ar(1-θ) + 2b(1-r)θ + qθ(1-θ)`

is the constant `2c`.  The ODE moment identities imply

`E[(θ-r₀)θ(1-θ)] =
  2ab(a-b)(2h+1)/(h^3(2h+3)(2h+5))`.

Consequently, once the quotient-rule layer identifies the right
`q`-derivative as `-p/(2c)` times this moment, the derivative is

`-(a-b)(2h+1)/(2h^2(2h+5))`,

which is nonzero exactly when `a ≠ b`.
-/

namespace GraybillDeal

noncomputable section

/-- The sum of the two beta-shape parameters. -/
def universalH (a b : ℝ) : ℝ :=
  a + b

/-- The exponent occurring in the reduced limiting-Bayes kernel. -/
def universalP (a b : ℝ) : ℝ :=
  universalH a b + 3 / 2

/-- The pivot at which the `q = 0` denominator becomes constant. -/
def universalUnequalPivot (a b : ℝ) : ℝ :=
  b / universalH a b

/-- Half of the constant pivot denominator. -/
def universalUnequalC (a b : ℝ) : ℝ :=
  a * b / universalH a b

/--
The denominator in the reduced limiting-Bayes kernel.

The later analytic layer uses `universalReducedDenominator a b r q θ`
raised to the real power `-universalP a b`.
-/
def universalReducedDenominator
    (a b r q θ : ℝ) : ℝ :=
  2 * a * r * (1 - θ)
    + 2 * b * (1 - r) * θ
    + q * θ * (1 - θ)

/-- The centered variable used by the `q = 0` ODE. -/
def universalCenteredZ (a b θ : ℝ) : ℝ :=
  a - universalH a b * θ

/-- The asymmetry `a-b`. -/
def universalUnequalD (a b : ℝ) : ℝ :=
  a - b

/-- The quadratic expression `a²+b²`. -/
def universalUnequalS (a b : ℝ) : ℝ :=
  a ^ 2 + b ^ 2

/-- The quadratic expression `a²-ab+b²`. -/
def universalUnequalK (a b : ℝ) : ℝ :=
  a ^ 2 - a * b + b ^ 2

/-- The ODE exponent `λ = h + 1/2`. -/
def universalUnequalLambda (a b : ℝ) : ℝ :=
  universalH a b + 1 / 2

/--
The scalar obtained after expanding
`E[(θ-r₀)θ(1-θ)]` in terms of the first three moments of
`Z = a-hθ`.
-/
def universalCenteredIntegrandMoment
    (a b m₁ m₂ m₃ : ℝ) : ℝ :=
  let h := universalH a b
  let d := universalUnequalD a b
  (a * b * d + (d ^ 2 - a * b) * m₁ - 2 * d * m₂ + m₃)
    / h ^ 3

/-- The exact centered moment forced by the ODE identities. -/
def universalUnequalMoment (a b : ℝ) : ℝ :=
  let h := universalH a b
  2 * a * b * (a - b) * (2 * h + 1)
    / (h ^ 3 * (2 * h + 3) * (2 * h + 5))

/--
The derivative value obtained from the quotient-rule identity after the
denominator has collapsed to the constant `2c`.
-/
def universalQDerivativeFromMoment
    (a b moment : ℝ) : ℝ :=
  -(universalP a b / (2 * universalUnequalC a b)) * moment

/-- The final explicit unequal-sample obstruction coefficient. -/
def universalUnequalObstruction (a b : ℝ) : ℝ :=
  let h := universalH a b
  (-1) * (a - b) * (2 * h + 1) / (2 * h ^ 2 * (2 * h + 5))

theorem universalH_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < universalH a b := by
  unfold universalH
  positivity

theorem universalP_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < universalP a b := by
  have hh := universalH_pos ha hb
  unfold universalP
  positivity

theorem universalUnequalC_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < universalUnequalC a b := by
  exact div_pos (mul_pos ha hb) (universalH_pos ha hb)

theorem universalUnequalPivot_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < universalUnequalPivot a b := by
  exact div_pos hb (universalH_pos ha hb)

theorem universalUnequalPivot_lt_one
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    universalUnequalPivot a b < 1 := by
  rw [universalUnequalPivot, div_lt_one (universalH_pos ha hb)]
  unfold universalH
  linarith

/-- `B` is affine in the nonnegative statistical coordinate `q`. -/
theorem universalReducedDenominator_sub_q_zero
    (a b r q θ : ℝ) :
    universalReducedDenominator a b r q θ
        - universalReducedDenominator a b r 0 θ
      = q * θ * (1 - θ) := by
  unfold universalReducedDenominator
  ring

/-- The exact `q` difference quotient of `B`, away from `q=0`. -/
theorem universalReducedDenominator_q_differenceQuotient
    (a b r q θ : ℝ) (hq : q ≠ 0) :
    (universalReducedDenominator a b r q θ
        - universalReducedDenominator a b r 0 θ) / q
      = θ * (1 - θ) := by
  rw [universalReducedDenominator_sub_q_zero]
  field_simp

/--
At the pivot `r₀=b/(a+b)` and `q=0`, the reduced denominator is independent
of `θ` and equals `2ab/(a+b) = 2c`.
-/
theorem universalReducedDenominator_pivot_zero
    {a b θ : ℝ} (hh : universalH a b ≠ 0) :
    universalReducedDenominator a b
        (universalUnequalPivot a b) 0 θ
      = 2 * universalUnequalC a b := by
  have hab : a + b ≠ 0 := by
    simpa [universalH] using hh
  unfold universalReducedDenominator universalUnequalPivot
    universalUnequalC universalH
  field_simp [hab]
  ring

/--
The centered coordinate reconstructs `θ`.
-/
theorem theta_eq_sub_centeredZ_div
    {a b θ : ℝ} (hh : universalH a b ≠ 0) :
    θ = (a - universalCenteredZ a b θ) / universalH a b := by
  unfold universalCenteredZ
  field_simp [hh]
  ring

/--
At the pivot, `θ-r₀ = (a-b-Z)/h`.
-/
theorem theta_sub_pivot_eq
    {a b θ : ℝ} (hh : universalH a b ≠ 0) :
    θ - universalUnequalPivot a b
      =
    (universalUnequalD a b - universalCenteredZ a b θ)
      / universalH a b := by
  unfold universalUnequalPivot universalUnequalD universalCenteredZ
    universalH
  unfold universalH at hh
  field_simp [hh]
  ring

/-- In centered coordinates, `1-θ = (b+Z)/h`. -/
theorem one_sub_theta_eq
    {a b θ : ℝ} (hh : universalH a b ≠ 0) :
    1 - θ
      =
    (b + universalCenteredZ a b θ) / universalH a b := by
  unfold universalCenteredZ universalH
  unfold universalH at hh
  field_simp [hh]
  ring

/--
The polynomial identity underlying the conversion of the needed cubic
moment into the first three moments of `Z`.
-/
theorem universalUnequal_centered_cubic_expand
    (a b z : ℝ) :
    (universalUnequalD a b - z) * (a - z) * (b + z)
      =
    a * b * universalUnequalD a b
      + (universalUnequalD a b ^ 2 - a * b) * z
      - 2 * universalUnequalD a b * z ^ 2
      + z ^ 3 := by
  unfold universalUnequalD
  ring

/--
Pointwise conversion of the target integrand into centered coordinates.
-/
theorem universalUnequal_integrand_centered
    {a b θ : ℝ} (hh : universalH a b ≠ 0) :
    (θ - universalUnequalPivot a b) * θ * (1 - θ)
      =
    ((universalUnequalD a b - universalCenteredZ a b θ)
        * (a - universalCenteredZ a b θ)
        * (b + universalCenteredZ a b θ))
      / universalH a b ^ 3 := by
  unfold universalUnequalPivot universalUnequalD universalCenteredZ
    universalH
  unfold universalH at hh
  field_simp [hh]
  ring

/--
The moment hypotheses produced by the `q=0` ODE imply the exact cubic
moment needed by the unequal-sample contradiction.

This theorem is the principal interface for the later measure-theoretic
module.  It needs only the values of `E[Z]`, `E[Z²]`, and `E[Z³]`.
-/
theorem universalUnequalMoment_of_odeMoments
    {a b m₁ m₂ m₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hm₁ : m₁ = universalUnequalD a b)
    (hm₂ :
      m₂ =
        (universalUnequalK a b
            + universalUnequalLambda a b
                * universalUnequalD a b ^ 2)
          / (universalUnequalLambda a b + 1))
    (hm₃ :
      m₃ =
        universalUnequalD a b
          * (2 * universalUnequalS a b
              + 3 * universalUnequalLambda a b
                  * universalUnequalK a b
              + universalUnequalLambda a b ^ 2
                  * universalUnequalD a b ^ 2)
          / ((universalUnequalLambda a b + 1)
              * (universalUnequalLambda a b + 2))) :
    universalCenteredIntegrandMoment a b m₁ m₂ m₃
      = universalUnequalMoment a b := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  have hlambda1 : 0 < universalUnequalLambda a b + 1 := by
    unfold universalUnequalLambda
    positivity
  have hlambda2 : 0 < universalUnequalLambda a b + 2 := by
    unfold universalUnequalLambda
    positivity
  have h2h3 : 0 < 2 * universalH a b + 3 := by positivity
  have h2h5 : 0 < 2 * universalH a b + 5 := by positivity
  rw [hm₁, hm₂, hm₃]
  unfold universalCenteredIntegrandMoment universalUnequalMoment
    universalUnequalD universalUnequalK universalUnequalS
    universalUnequalLambda universalH
  field_simp [ne_of_gt hh, ne_of_gt hlambda1, ne_of_gt hlambda2,
    ne_of_gt h2h3, ne_of_gt h2h5]
  ring

/--
Substitution of the exact cubic moment into the quotient-rule coefficient.
-/
theorem universalQDerivativeFromMoment_eq_obstruction
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    universalQDerivativeFromMoment a b
        (universalUnequalMoment a b)
      = universalUnequalObstruction a b := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  have hc : 0 < universalUnequalC a b :=
    universalUnequalC_pos ha hb
  have h2h3 : 0 < 2 * universalH a b + 3 := by positivity
  have h2h5 : 0 < 2 * universalH a b + 5 := by positivity
  unfold universalQDerivativeFromMoment universalUnequalMoment
    universalUnequalObstruction universalP universalUnequalC universalH
  field_simp [ne_of_gt hh, ne_of_gt hc, ne_of_gt h2h3, ne_of_gt h2h5]

/--
Combined interface: if an analytic quotient-rule calculation produces
`derivative = -p/(2c) · moment`, and the ODE layer supplies the three
moment identities, then the derivative is the explicit obstruction.
-/
theorem universalUnequal_qDerivative_of_odeMoments
    {a b m₁ m₂ m₃ derivative : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hm₁ : m₁ = universalUnequalD a b)
    (hm₂ :
      m₂ =
        (universalUnequalK a b
            + universalUnequalLambda a b
                * universalUnequalD a b ^ 2)
          / (universalUnequalLambda a b + 1))
    (hm₃ :
      m₃ =
        universalUnequalD a b
          * (2 * universalUnequalS a b
              + 3 * universalUnequalLambda a b
                  * universalUnequalK a b
              + universalUnequalLambda a b ^ 2
                  * universalUnequalD a b ^ 2)
          / ((universalUnequalLambda a b + 1)
              * (universalUnequalLambda a b + 2)))
    (hderivative :
      derivative =
        universalQDerivativeFromMoment a b
          (universalCenteredIntegrandMoment a b m₁ m₂ m₃)) :
    derivative = universalUnequalObstruction a b := by
  rw [hderivative,
    universalUnequalMoment_of_odeMoments ha hb hm₁ hm₂ hm₃,
    universalQDerivativeFromMoment_eq_obstruction ha hb]

/-- The explicit unequal obstruction is nonzero when `a ≠ b`. -/
theorem universalUnequalObstruction_ne_zero
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    universalUnequalObstruction a b ≠ 0 := by
  have hh : 0 < universalH a b := universalH_pos ha hb
  have hnum1 : 0 < 2 * universalH a b + 1 := by positivity
  have hden5 : 0 < 2 * universalH a b + 5 := by positivity
  unfold universalUnequalObstruction
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab))
      hnum1.ne'
  · exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hh.ne'))
      hden5.ne'

/--
The algebraic contradiction used in the unequal branch: a derivative cannot
simultaneously be zero (because the posterior action is constant in `q`) and
equal the nonzero obstruction coefficient.
-/
theorem universalUnequal_no_zero_qDerivative
    {a b derivative : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hzero : derivative = 0)
    (hobstruction : derivative = universalUnequalObstruction a b) :
    False := by
  apply universalUnequalObstruction_ne_zero ha hb hab
  rw [← hobstruction, hzero]

end

end GraybillDeal
