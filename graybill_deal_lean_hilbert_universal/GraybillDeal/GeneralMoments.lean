import GraybillDeal.GeneralAnalytic
import Mathlib.Probability.Distributions.Beta

/-!
# Beta moments for arbitrary residual degrees of freedom

For residual degrees of freedom `ν`, set

`Mν(j) = 1/2 * Β(j + 1/2, ν/2 + 1)`.

Analytically this is the moment

`∫ x in 0..1, x^(2j) * (1-x²)^(ν/2)`.

This file proves the recurrence and the two ratios needed to turn the first
three terms of the generalized series into `generalLowerQuadratic`.
-/

namespace GraybillDeal

open ProbabilityTheory Real

noncomputable section

/-- The beta-function form of the generalized even moment. -/
def generalMoment (ν : ℝ) (j : ℕ) : ℝ :=
  (1 / 2) * beta ((j : ℝ) + 1 / 2) (ν / 2 + 1)

theorem generalMoment_pos {ν : ℝ} (hν : -2 < ν) (j : ℕ) :
    0 < generalMoment ν j := by
  unfold generalMoment
  have hj : 0 < (j : ℝ) + 1 / 2 := by positivity
  have hshape : 0 < ν / 2 + 1 := by linarith
  exact mul_pos (by norm_num) (beta_pos hj hshape)

/--
The generalized moment recurrence

`(2j+1) Mν(j) = (2j+ν+3) Mν(j+1)`.
-/
theorem generalMoment_recurrence {ν : ℝ} (hν : -2 < ν) (j : ℕ) :
    (2 * (j : ℝ) + 1) * generalMoment ν j
      =
    (2 * (j : ℝ) + ν + 3) * generalMoment ν (j + 1) := by
  have hu : 0 < (j : ℝ) + 1 / 2 := by positivity
  have hv : 0 < ν / 2 + 1 := by linarith
  have huv : 0 < ((j : ℝ) + 1 / 2) + (ν / 2 + 1) :=
    add_pos hu hv
  have hGuv :
      Gamma (((j : ℝ) + 1 / 2) + (ν / 2 + 1)) ≠ 0 :=
    (Gamma_pos_of_pos huv).ne'
  have hbeta :
      beta (((j : ℝ) + 1 / 2) + 1) (ν / 2 + 1)
        =
      (((j : ℝ) + 1 / 2) /
          (((j : ℝ) + 1 / 2) + (ν / 2 + 1)))
        * beta ((j : ℝ) + 1 / 2) (ν / 2 + 1) := by
    unfold beta
    rw [Real.Gamma_add_one hu.ne']
    rw [show ((j : ℝ) + 1 / 2 + 1) + (ν / 2 + 1)
          = (((j : ℝ) + 1 / 2) + (ν / 2 + 1)) + 1 by ring,
      Real.Gamma_add_one huv.ne']
    field_simp [huv.ne', hGuv]
  have hsum : 3 + 2 * (j : ℝ) + ν ≠ 0 := by
    have hj : 0 ≤ (j : ℝ) := by positivity
    linarith
  have hsum' : 2 * (j : ℝ) + 1 + (ν + 2) ≠ 0 := by
    have hj : 0 ≤ (j : ℝ) := by positivity
    linarith
  have hscalar :
      (2 * (j : ℝ) + ν + 3) * (1 / 2)
          * (((j : ℝ) + 1 / 2) /
            (((j : ℝ) + 1 / 2) + (ν / 2 + 1)))
        =
      (2 * (j : ℝ) + 1) * (1 / 2) := by
    field_simp [huv.ne', hsum, hsum']
    ring
  unfold generalMoment
  rw [show ((j + 1 : ℕ) : ℝ) + 1 / 2
        = ((j : ℝ) + 1 / 2) + 1 by
      norm_num
      ring,
    hbeta]
  calc
    (2 * (j : ℝ) + 1) *
          (1 / 2 * beta ((j : ℝ) + 1 / 2) (ν / 2 + 1))
        =
      ((2 * (j : ℝ) + 1) * (1 / 2))
        * beta ((j : ℝ) + 1 / 2) (ν / 2 + 1) := by ring
    _ =
      ((2 * (j : ℝ) + ν + 3) * (1 / 2)
          * (((j : ℝ) + 1 / 2) /
            (((j : ℝ) + 1 / 2) + (ν / 2 + 1))))
        * beta ((j : ℝ) + 1 / 2) (ν / 2 + 1) := by rw [hscalar]
    _ =
      (2 * (j : ℝ) + ν + 3) *
        (1 / 2 *
          ((((j : ℝ) + 1 / 2) /
              (((j : ℝ) + 1 / 2) + (ν / 2 + 1)))
            * beta ((j : ℝ) + 1 / 2) (ν / 2 + 1))) := by ring

theorem generalMoment_two_ratio {ν : ℝ} (hν : -2 < ν) :
    generalMoment ν 2
      = (3 / (ν + 5)) * generalMoment ν 1 := by
  have hden : ν + 5 ≠ 0 := by linarith
  have hrec := generalMoment_recurrence hν 1
  norm_num at hrec
  field_simp [hden]
  linarith

theorem generalMoment_three_ratio {ν : ℝ} (hν : -2 < ν) :
    generalMoment ν 3
      = (15 / ((ν + 5) * (ν + 7))) * generalMoment ν 1 := by
  have h5 : ν + 5 ≠ 0 := by linarith
  have h7 : ν + 7 ≠ 0 := by linarith
  have hrecTwo := generalMoment_recurrence hν 2
  norm_num at hrecTwo
  have hthree :
      generalMoment ν 3
        = (5 / (ν + 7)) * generalMoment ν 2 := by
    field_simp [h7]
    linarith
  rw [hthree, generalMoment_two_ratio hν]
  field_simp [h5, h7]
  ring

/-- The first three general series coefficients before moment ratios. -/
def generalQ0 (ν : ℝ) : ℝ :=
  (ν - 4) / (2 * (ν - 1))

def generalQ1 (ν : ℝ) : ℝ :=
  -(ν ^ 2 + 4 * ν + 40) / (6 * (ν - 1))

def generalQ2 (ν : ℝ) : ℝ :=
  (5 * ν ^ 2 - 19 * ν - 28) / (2 * (ν - 1))

/--
After the beta-moment recurrence, the first three generalized series terms
are exactly `Mν(1) * generalLowerQuadratic ν z`.
-/
theorem general_first_three_eq_lowerQuadratic
    {ν z : ℝ} (hν : 9 ≤ ν) :
    generalMoment ν 1 * generalQ0 ν
        + generalMoment ν 2 * generalQ1 ν * z
        + generalMoment ν 3 * generalQ2 ν * z ^ 2
      =
    generalMoment ν 1 * generalLowerQuadratic ν z := by
  have hν' : -2 < ν := by linarith
  have h1 : ν - 1 ≠ 0 := by linarith
  have h5 : ν + 5 ≠ 0 := by linarith
  have h7 : ν + 7 ≠ 0 := by linarith
  rw [generalMoment_two_ratio hν', generalMoment_three_ratio hν']
  unfold generalQ0 generalQ1 generalQ2
  unfold generalLowerQuadratic generalA generalB generalC
  field_simp [h1, h5, h7]
  ring

/-- Strict positivity of the generalized first-three-term truncation. -/
theorem general_first_three_pos
    (ν : ℕ) (hν : 9 ≤ ν) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 <
      generalMoment (ν : ℝ) 1 * generalQ0 (ν : ℝ)
        + generalMoment (ν : ℝ) 2 * generalQ1 (ν : ℝ) * z
        + generalMoment (ν : ℝ) 3 * generalQ2 (ν : ℝ) * z ^ 2 := by
  rw [general_first_three_eq_lowerQuadratic (by exact_mod_cast hν)]
  exact mul_pos
    (generalMoment_pos (by
      have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
      linarith) 1)
    (generalLowerQuadratic_pos_nat ν hν hz0 hz1)

end

end GraybillDeal
