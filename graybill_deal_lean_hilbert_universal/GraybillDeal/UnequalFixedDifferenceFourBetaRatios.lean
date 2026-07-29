import GraybillDeal.UnequalFixedDifferenceFourMoments

/-!
# Inverse-beta ratios for the fixed-difference-four family

This file evaluates the four shifted beta-function ratios used by the
quadratic envelope.  Keeping these calculations separate from the
measure-theoretic integration proof makes the latter depend only on exact
moment identities.
-/

namespace GraybillDeal

open ProbabilityTheory

noncomputable section

private theorem unequalFD4Beta_cast_seven_le
    {m : ℕ} (hm : 7 ≤ m) :
    (7 : ℝ) ≤ (m : ℝ) := by
  exact_mod_cast hm

/-- Symmetry of Euler's real beta function. -/
theorem beta_symm_real (a b : ℝ) :
    beta a b = beta b a := by
  unfold beta
  rw [add_comm a b]
  ring

/-- One-step beta recurrence in the second argument. -/
theorem beta_add_one_right
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    beta a (b + 1) = (b / (a + b)) * beta a b := by
  calc
    beta a (b + 1) = beta (b + 1) a :=
      beta_symm_real a (b + 1)
    _ = (b / (b + a)) * beta b a :=
      beta_add_one_left hb ha
    _ = (b / (a + b)) * beta a b := by
      rw [beta_symm_real b a]
      congr 2
      ring

/--
Right-chart inverse-square moment:

`B(m+3,m-3) / B(m+1,m-1)
  = (m+1)(m+2) / ((m-2)(m-3))`.
-/
theorem unequalFixedDifferenceFourPlusBetaRatioTwo
    {m : ℕ} (hm : 7 ≤ m) :
    beta ((m : ℝ) + 1 + 2) ((m : ℝ) - 1 - 2)
        / beta ((m : ℝ) + 1) ((m : ℝ) - 1)
      =
    (((m : ℝ) + 1) * ((m : ℝ) + 2))
      / (((m : ℝ) - 2) * ((m : ℝ) - 3)) := by
  have hmR := unequalFD4Beta_cast_seven_le hm
  have hbase : beta ((m : ℝ) + 1) ((m : ℝ) - 3) ≠ 0 :=
    (beta_pos (by linarith) (by linarith)).ne'
  have hleft1 :=
    beta_add_one_left
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 3)
      (by linarith) (by linarith)
  have hleft2 :=
    beta_add_one_left
      (a := (m : ℝ) + 2) (b := (m : ℝ) - 3)
      (by linarith) (by linarith)
  have hright1 :=
    beta_add_one_right
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 3)
      (by linarith) (by linarith)
  have hright2 :=
    beta_add_one_right
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 2)
      (by linarith) (by linarith)
  have hm2 : (m : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : (m : ℝ) - 3 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m2 : 2 * (m : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have hprod12 :
      2 - (m : ℝ) * 6 + (m : ℝ) ^ 2 * 4 ≠ 0 := by
    rw [show
      2 - (m : ℝ) * 6 + (m : ℝ) ^ 2 * 4
        = (2 * (m : ℝ) - 1) * (2 * (m : ℝ) - 2) by ring]
    exact mul_ne_zero h2m1 h2m2
  rw [show (m : ℝ) + 1 + 2 = ((m : ℝ) + 2) + 1 by ring,
    show (m : ℝ) - 1 - 2 = (m : ℝ) - 3 by ring,
    hleft2,
    show beta ((m : ℝ) + 2) ((m : ℝ) - 3)
        = beta (((m : ℝ) + 1) + 1) ((m : ℝ) - 3) by ring,
    hleft1,
    show (m : ℝ) - 1 = ((m : ℝ) - 2) + 1 by ring,
    hright2,
    show beta ((m : ℝ) + 1) ((m : ℝ) - 2)
        = beta ((m : ℝ) + 1) (((m : ℝ) - 3) + 1) by ring,
    hright1]
  field_simp [hbase, hm2, hm3, h2m1, h2m2, hprod12]
  apply (div_eq_iff (mul_ne_zero (by linarith) (by linarith))).2
  ring

/--
Right-chart inverse-fourth moment.
-/
theorem unequalFixedDifferenceFourPlusBetaRatioFour
    {m : ℕ} (hm : 7 ≤ m) :
    beta ((m : ℝ) + 1 + 2) ((m : ℝ) - 1 - 4)
        / beta ((m : ℝ) + 1) ((m : ℝ) - 1)
      =
    (((m : ℝ) + 1) * ((m : ℝ) + 2)
        * (2 * (m : ℝ) - 1) * (2 * (m : ℝ) - 2))
      /
    (((m : ℝ) - 2) * ((m : ℝ) - 3)
        * ((m : ℝ) - 4) * ((m : ℝ) - 5)) := by
  have hmR := unequalFD4Beta_cast_seven_le hm
  have hbase : beta ((m : ℝ) + 1) ((m : ℝ) - 5) ≠ 0 :=
    (beta_pos (by linarith) (by linarith)).ne'
  have hl1 :=
    beta_add_one_left
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 5)
      (by linarith) (by linarith)
  have hl2 :=
    beta_add_one_left
      (a := (m : ℝ) + 2) (b := (m : ℝ) - 5)
      (by linarith) (by linarith)
  have hr1 :=
    beta_add_one_right
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 5)
      (by linarith) (by linarith)
  have hr2 :=
    beta_add_one_right
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 4)
      (by linarith) (by linarith)
  have hr3 :=
    beta_add_one_right
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 3)
      (by linarith) (by linarith)
  have hr4 :=
    beta_add_one_right
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 2)
      (by linarith) (by linarith)
  have hm2 : (m : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : (m : ℝ) - 3 ≠ 0 := ne_of_gt (by linarith)
  have hm4 : (m : ℝ) - 4 ≠ 0 := ne_of_gt (by linarith)
  have hm5 : (m : ℝ) - 5 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m2 : 2 * (m : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have h2m3 : 2 * (m : ℝ) - 3 ≠ 0 := ne_of_gt (by linarith)
  have h2m4 : 2 * (m : ℝ) - 4 ≠ 0 := ne_of_gt (by linarith)
  have hprod12 :
      2 - (m : ℝ) * 6 + (m : ℝ) ^ 2 * 4 ≠ 0 := by
    rw [show
      2 - (m : ℝ) * 6 + (m : ℝ) ^ 2 * 4
        = (2 * (m : ℝ) - 1) * (2 * (m : ℝ) - 2) by ring]
    exact mul_ne_zero h2m1 h2m2
  have hprod34 :
      12 - (m : ℝ) * 14 + (m : ℝ) ^ 2 * 4 ≠ 0 := by
    rw [show
      12 - (m : ℝ) * 14 + (m : ℝ) ^ 2 * 4
        = (2 * (m : ℝ) - 3) * (2 * (m : ℝ) - 4) by ring]
    exact mul_ne_zero h2m3 h2m4
  rw [show (m : ℝ) + 1 + 2 = ((m : ℝ) + 2) + 1 by ring,
    show (m : ℝ) - 1 - 4 = (m : ℝ) - 5 by ring,
    hl2,
    show beta ((m : ℝ) + 2) ((m : ℝ) - 5)
        = beta (((m : ℝ) + 1) + 1) ((m : ℝ) - 5) by ring,
    hl1,
    show (m : ℝ) - 1 = ((m : ℝ) - 2) + 1 by ring,
    hr4,
    show beta ((m : ℝ) + 1) ((m : ℝ) - 2)
        = beta ((m : ℝ) + 1) (((m : ℝ) - 3) + 1) by ring,
    hr3,
    show beta ((m : ℝ) + 1) ((m : ℝ) - 3)
        = beta ((m : ℝ) + 1) (((m : ℝ) - 4) + 1) by ring,
    hr2,
    show beta ((m : ℝ) + 1) ((m : ℝ) - 4)
        = beta ((m : ℝ) + 1) (((m : ℝ) - 5) + 1) by ring,
    hr1]
  field_simp [hbase, hm2, hm3, hm4, hm5,
    h2m1, h2m2, h2m3, h2m4, hprod12, hprod34]
  apply (div_eq_iff (mul_ne_zero (by linarith) (by linarith))).2
  ring

/-- Left-chart inverse-square moment. -/
theorem unequalFixedDifferenceFourMinusBetaRatioTwo
    {m : ℕ} (hm : 7 ≤ m) :
    beta ((m : ℝ) - 1 + 2) ((m : ℝ) + 1 - 2)
        / beta ((m : ℝ) - 1) ((m : ℝ) + 1)
      = 1 := by
  have hmR := unequalFD4Beta_cast_seven_le hm
  have hbeta : beta ((m : ℝ) - 1) ((m : ℝ) + 1) ≠ 0 :=
    (beta_pos (by linarith) (by linarith)).ne'
  rw [show (m : ℝ) - 1 + 2 = (m : ℝ) + 1 by ring,
    show (m : ℝ) + 1 - 2 = (m : ℝ) - 1 by ring,
    beta_symm_real ((m : ℝ) + 1) ((m : ℝ) - 1)]
  exact div_self hbeta

/-- Left-chart inverse-fourth moment. -/
theorem unequalFixedDifferenceFourMinusBetaRatioFour
    {m : ℕ} (hm : 7 ≤ m) :
    beta ((m : ℝ) - 1 + 2) ((m : ℝ) + 1 - 4)
        / beta ((m : ℝ) - 1) ((m : ℝ) + 1)
      =
    ((2 * (m : ℝ) - 1) * (2 * (m : ℝ) - 2))
      / (((m : ℝ) - 2) * ((m : ℝ) - 3)) := by
  have hmR := unequalFD4Beta_cast_seven_le hm
  have hbase : beta ((m : ℝ) + 1) ((m : ℝ) - 3) ≠ 0 :=
    (beta_pos (by linarith) (by linarith)).ne'
  have hr1 :=
    beta_add_one_right
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 3)
      (by linarith) (by linarith)
  have hr2 :=
    beta_add_one_right
      (a := (m : ℝ) + 1) (b := (m : ℝ) - 2)
      (by linarith) (by linarith)
  have hm2 : (m : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have hm3 : (m : ℝ) - 3 ≠ 0 := ne_of_gt (by linarith)
  have h2m1 : 2 * (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2m2 : 2 * (m : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have hprod12 :
      2 - (m : ℝ) * 6 + (m : ℝ) ^ 2 * 4 ≠ 0 := by
    rw [show
      2 - (m : ℝ) * 6 + (m : ℝ) ^ 2 * 4
        = (2 * (m : ℝ) - 1) * (2 * (m : ℝ) - 2) by ring]
    exact mul_ne_zero h2m1 h2m2
  rw [show (m : ℝ) - 1 + 2 = (m : ℝ) + 1 by ring,
    show (m : ℝ) + 1 - 4 = (m : ℝ) - 3 by ring,
    beta_symm_real ((m : ℝ) - 1) ((m : ℝ) + 1),
    show (m : ℝ) - 1 = ((m : ℝ) - 2) + 1 by ring,
    hr2,
    show beta ((m : ℝ) + 1) ((m : ℝ) - 2)
        = beta ((m : ℝ) + 1) (((m : ℝ) - 3) + 1) by ring,
    hr1]
  field_simp [hbase, hm2, hm3, h2m1, h2m2, hprod12]
  ring

end

end GraybillDeal
