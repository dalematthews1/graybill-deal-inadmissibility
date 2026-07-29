import GraybillDeal.UniversalReducedKernel

/-!
# The limiting posterior identity

This file packages the identity that the decision-theoretic limiting-Bayes
argument must produce.  Keeping it as an explicit structure lets the
analytic contradiction be developed and audited independently of the
complete-class theorem.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

/-- The balanced `r` coordinate at which the `q = 0` denominator is
independent of the parameter. -/
def universalBalance (a b : ℝ) : ℝ :=
  b / (a + b)

/-- Half of the constant value of `universalB` at the balanced point. -/
def universalBalanceScale (a b : ℝ) : ℝ :=
  a * b / (a + b)

theorem universalBalance_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < universalBalance a b := by
  unfold universalBalance
  positivity

theorem universalBalance_lt_one
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    universalBalance a b < 1 := by
  unfold universalBalance
  rw [div_lt_one (add_pos ha hb)]
  linarith

theorem universalBalanceScale_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < universalBalanceScale a b := by
  unfold universalBalanceScale
  positivity

theorem universalB_balance_zero
    {a b : ℝ} (hab : a + b ≠ 0) (θ : UniversalTheta) :
    universalB a b (universalBalance a b) 0 θ
      = 2 * universalBalanceScale a b := by
  unfold universalB universalBalance universalBalanceScale
  field_simp [hab]
  ring

theorem universalKernel_balance_zero
    {a b : ℝ} (hab : a + b ≠ 0) (θ : UniversalTheta) :
    universalKernel a b (universalBalance a b) 0 θ
      =
    (2 * universalBalanceScale a b) ^ (-universalExponent a b) := by
  unfold universalKernel
  rw [universalB_balance_zero hab]

/-- The exact posterior identity forced by the limiting-Bayes bridge. -/
structure UniversalPosteriorIdentity
    (ν : Measure UniversalTheta) (a b : ℝ) : Prop where
  action_eq :
    ∀ r q : ℝ, 0 < r → r < 1 → 0 ≤ q →
      universalPosteriorAction ν a b r q = r

namespace UniversalPosteriorIdentity

variable {ν : Measure UniversalTheta} [IsProbabilityMeasure ν]
variable {a b : ℝ}

theorem numerator_eq_mul_denominator
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b)
    {r q : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 ≤ q) :
    universalPosteriorNumerator ν a b r q
      =
    r * universalPosteriorDenominator ν a b r q := by
  have hden :
      universalPosteriorDenominator ν a b r q ≠ 0 :=
    ne_of_gt
      (universalPosteriorDenominator_pos
        ν ha hb hr0 hr1 hq)
  have haction := H.action_eq r q hr0 hr1 hq
  unfold universalPosteriorAction at haction
  exact (div_eq_iff hden).mp haction

theorem action_eq_at_balance_zero
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b) :
    universalPosteriorAction ν a b
      (universalBalance a b) 0 = universalBalance a b := by
  exact H.action_eq _ _ (universalBalance_pos ha hb)
    (universalBalance_lt_one ha hb) le_rfl

theorem numerator_eq_mul_denominator_at_balance_zero
    (H : UniversalPosteriorIdentity ν a b)
    (ha : 0 < a) (hb : 0 < b) :
    universalPosteriorNumerator ν a b
        (universalBalance a b) 0
      =
    universalBalance a b
      * universalPosteriorDenominator ν a b
          (universalBalance a b) 0 := by
  exact H.numerator_eq_mul_denominator ha hb
    (universalBalance_pos ha hb)
    (universalBalance_lt_one ha hb) le_rfl

end UniversalPosteriorIdentity

end

end GraybillDeal
