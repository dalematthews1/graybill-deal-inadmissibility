import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial sign certificate for the fixed-difference-four family

This file isolates the finite algebraic certificate used for the family

`(n₁, n₂) = (2m - 1, 2m + 3)`, with `m ≥ 7`.

The first three coefficients in each one-sided series reduce to five
distinct numerator polynomials.  The remaining coefficients reduce to two
bivariate tail polynomials.  After the shifts

`u = m - 7` and `v = n - 3`,

every displayed coefficient is a strictly positive integer.  The
definitions below are the exact shifted polynomials produced by
`numerics/derive_unequal_fixed_difference_four.py`.

This module proves only their algebraic positivity.  It deliberately does
not identify them with probability integrals or risk coefficients.
-/

namespace GraybillDeal

noncomputable section

/-! ## The five exceptional numerator polynomials -/

def unequalFD4HeadZero (m : ℝ) : ℝ :=
  (m - 1) * (m ^ 5 + 3 * m ^ 4 - 10 * m ^ 2 - 17 * m + 15)

def unequalFD4HeadPlusOne (m : ℝ) : ℝ :=
  (m - 1) *
    (3 * m ^ 6 + 16 * m ^ 5 + 27 * m ^ 4 - 22 * m ^ 3
      - 101 * m ^ 2 + 46 * m + 15)

def unequalFD4HeadMinusOne (m : ℝ) : ℝ :=
  (m - 1) *
    (3 * m ^ 6 + 2 * m ^ 5 - 27 * m ^ 4 - 38 * m ^ 3
      - m ^ 2 + 44 * m - 15)

def unequalFD4HeadPlusTwo (m : ℝ) : ℝ :=
  (m - 1) *
    (12 * m ^ 9 - 20 * m ^ 8 - 86 * m ^ 7 + 618 * m ^ 6
      + 1968 * m ^ 5 - 1238 * m ^ 4 - 1395 * m ^ 3
      - 163 * m ^ 2 + 1065 * m - 225)

def unequalFD4HeadMinusTwo (m : ℝ) : ℝ :=
  (m - 1) *
    (12 * m ^ 9 - 20 * m ^ 8 - 198 * m ^ 7 - 38 * m ^ 6
      + 1116 * m ^ 5 - 154 * m ^ 4 + 349 * m ^ 3
      - 1435 * m ^ 2 + 605 * m + 75)

def unequalFD4HeadZeroShift (u : ℝ) : ℝ :=
  u ^ 6 + 44 * u ^ 5 + 802 * u ^ 4 + 7746 * u ^ 3
    + 41776 * u ^ 2 + 119200 * u + 140496

def unequalFD4HeadPlusOneShift (u : ℝ) : ℝ :=
  3 * u ^ 7 + 160 * u ^ 6 + 3644 * u ^ 5 + 45906 * u ^ 4
    + 345224 * u ^ 3 + 1548848 * u ^ 2
    + 3836816 * u + 4047168

def unequalFD4HeadMinusOneShift (u : ℝ) : ℝ :=
  3 * u ^ 7 + 146 * u ^ 6 + 3016 * u ^ 5 + 34254 * u ^ 4
    + 230764 * u ^ 3 + 920944 * u ^ 2
    + 2012560 * u + 1853664

def unequalFD4HeadPlusTwoShift (u : ℝ) : ℝ :=
  12 * u ^ 10 + 808 * u ^ 9 + 24378 * u ^ 8 + 434480 * u ^ 7
    + 5073830 * u ^ 6 + 40653718 * u ^ 5
    + 226948439 * u ^ 4 + 874390272 * u ^ 3
    + 2232934952 * u ^ 2 + 3424743992 * u
    + 2402724864

def unequalFD4HeadMinusTwoShift (u : ℝ) : ℝ :=
  12 * u ^ 10 + 808 * u ^ 9 + 24266 * u ^ 8 + 427664 * u ^ 7
    + 4893314 * u ^ 6 + 37936350 * u ^ 5
    + 201518239 * u ^ 4 + 722881272 * u ^ 3
    + 1671697576 * u ^ 2 + 2242793016 * u
    + 1319133888

theorem unequalFD4HeadZero_shift (u : ℝ) :
    unequalFD4HeadZero (u + 7) = unequalFD4HeadZeroShift u := by
  unfold unequalFD4HeadZero unequalFD4HeadZeroShift
  ring

theorem unequalFD4HeadPlusOne_shift (u : ℝ) :
    unequalFD4HeadPlusOne (u + 7) = unequalFD4HeadPlusOneShift u := by
  unfold unequalFD4HeadPlusOne unequalFD4HeadPlusOneShift
  ring

theorem unequalFD4HeadMinusOne_shift (u : ℝ) :
    unequalFD4HeadMinusOne (u + 7) = unequalFD4HeadMinusOneShift u := by
  unfold unequalFD4HeadMinusOne unequalFD4HeadMinusOneShift
  ring

theorem unequalFD4HeadPlusTwo_shift (u : ℝ) :
    unequalFD4HeadPlusTwo (u + 7) = unequalFD4HeadPlusTwoShift u := by
  unfold unequalFD4HeadPlusTwo unequalFD4HeadPlusTwoShift
  ring

theorem unequalFD4HeadMinusTwo_shift (u : ℝ) :
    unequalFD4HeadMinusTwo (u + 7) = unequalFD4HeadMinusTwoShift u := by
  unfold unequalFD4HeadMinusTwo unequalFD4HeadMinusTwoShift
  ring

theorem unequalFD4HeadZeroShift_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4HeadZeroShift u := by
  unfold unequalFD4HeadZeroShift
  positivity

theorem unequalFD4HeadPlusOneShift_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4HeadPlusOneShift u := by
  unfold unequalFD4HeadPlusOneShift
  positivity

theorem unequalFD4HeadMinusOneShift_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4HeadMinusOneShift u := by
  unfold unequalFD4HeadMinusOneShift
  positivity

theorem unequalFD4HeadPlusTwoShift_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4HeadPlusTwoShift u := by
  unfold unequalFD4HeadPlusTwoShift
  positivity

theorem unequalFD4HeadMinusTwoShift_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4HeadMinusTwoShift u := by
  unfold unequalFD4HeadMinusTwoShift
  positivity

private theorem real_eq_sub_add_of_le {a b : ℝ} (_h : b ≤ a) :
    a = (a - b) + b := by
  ring

theorem unequalFD4HeadZero_pos {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFD4HeadZero m := by
  rw [real_eq_sub_add_of_le hm, unequalFD4HeadZero_shift]
  exact unequalFD4HeadZeroShift_pos (sub_nonneg.mpr hm)

theorem unequalFD4HeadPlusOne_pos {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFD4HeadPlusOne m := by
  rw [real_eq_sub_add_of_le hm, unequalFD4HeadPlusOne_shift]
  exact unequalFD4HeadPlusOneShift_pos (sub_nonneg.mpr hm)

theorem unequalFD4HeadMinusOne_pos {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFD4HeadMinusOne m := by
  rw [real_eq_sub_add_of_le hm, unequalFD4HeadMinusOne_shift]
  exact unequalFD4HeadMinusOneShift_pos (sub_nonneg.mpr hm)

theorem unequalFD4HeadPlusTwo_pos {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFD4HeadPlusTwo m := by
  rw [real_eq_sub_add_of_le hm, unequalFD4HeadPlusTwo_shift]
  exact unequalFD4HeadPlusTwoShift_pos (sub_nonneg.mpr hm)

theorem unequalFD4HeadMinusTwo_pos {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFD4HeadMinusTwo m := by
  rw [real_eq_sub_add_of_le hm, unequalFD4HeadMinusTwo_shift]
  exact unequalFD4HeadMinusTwoShift_pos (sub_nonneg.mpr hm)

/-! ## The plus-chart tail polynomial -/

def unequalFD4TailPlusA0 (u : ℝ) : ℝ :=
  720 * u ^ 10 + 51960 * u ^ 9 + 1666320 * u ^ 8
    + 31247124 * u ^ 7 + 379139664 * u ^ 6
    + 3107966358 * u ^ 5 + 17420490234 * u ^ 4
    + 65901684756 * u ^ 3 + 161061561000 * u ^ 2
    + 229926565632 * u + 146076779520

def unequalFD4TailPlusA1 (u : ℝ) : ℝ :=
  600 * u ^ 10 + 44540 * u ^ 9 + 1459740 * u ^ 8
    + 27774144 * u ^ 7 + 339031406 * u ^ 6
    + 2765791827 * u ^ 5 + 15202322359 * u ^ 4
    + 55205669726 * u ^ 3 + 125303849868 * u ^ 2
    + 157192252928 * u + 79138944000

def unequalFD4TailPlusA2 (u : ℝ) : ℝ :=
  120 * u ^ 10 + 10180 * u ^ 9 + 370130 * u ^ 8
    + 7649004 * u ^ 7 + 99760958 * u ^ 6
    + 857448520 * u ^ 5 + 4898100821 * u ^ 4
    + 18191664968 * u ^ 3 + 41243680528 * u ^ 2
    + 49369697912 * u + 20869465760

def unequalFD4TailPlusA3 (u : ℝ) : ℝ :=
  540 * u ^ 9 + 34350 * u ^ 8 + 956944 * u ^ 7
    + 15296928 * u ^ 6 + 154284145 * u ^ 5
    + 1015130091 * u ^ 4 + 4337992418 * u ^ 3
    + 11530616468 * u ^ 2 + 17102085872 * u
    + 10558352320

def unequalFD4TailPlusA4 (u : ℝ) : ℝ :=
  60 * u ^ 9 + 4110 * u ^ 8 + 123200 * u ^ 7
    + 2121794 * u ^ 6 + 23145402 * u ^ 5
    + 165873827 * u ^ 4 + 780974172 * u ^ 3
    + 2328732008 * u ^ 2 + 3987944440 * u
    + 2985036000

def unequalFD4TailPlusA5 (u : ℝ) : ℝ :=
  30 * u ^ 8 + 1680 * u ^ 7 + 40842 * u ^ 6
    + 563388 * u ^ 5 + 4825572 * u ^ 4
    + 26289672 * u ^ 3 + 88986240 * u ^ 2
    + 171124704 * u + 143156160

def unequalFD4TailPlusShift (u v : ℝ) : ℝ :=
  unequalFD4TailPlusA0 u
    + unequalFD4TailPlusA1 u * v
    + unequalFD4TailPlusA2 u * v ^ 2
    + unequalFD4TailPlusA3 u * v ^ 3
    + unequalFD4TailPlusA4 u * v ^ 4
    + unequalFD4TailPlusA5 u * v ^ 5

theorem unequalFD4TailPlusA0_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailPlusA0 u := by
  unfold unequalFD4TailPlusA0
  positivity

theorem unequalFD4TailPlusA1_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailPlusA1 u := by
  unfold unequalFD4TailPlusA1
  positivity

theorem unequalFD4TailPlusA2_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailPlusA2 u := by
  unfold unequalFD4TailPlusA2
  positivity

theorem unequalFD4TailPlusA3_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailPlusA3 u := by
  unfold unequalFD4TailPlusA3
  positivity

theorem unequalFD4TailPlusA4_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailPlusA4 u := by
  unfold unequalFD4TailPlusA4
  positivity

theorem unequalFD4TailPlusA5_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailPlusA5 u := by
  unfold unequalFD4TailPlusA5
  positivity

theorem unequalFD4TailPlusShift_pos
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < unequalFD4TailPlusShift u v := by
  have h0 := unequalFD4TailPlusA0_pos hu
  have h1 := unequalFD4TailPlusA1_pos hu
  have h2 := unequalFD4TailPlusA2_pos hu
  have h3 := unequalFD4TailPlusA3_pos hu
  have h4 := unequalFD4TailPlusA4_pos hu
  have h5 := unequalFD4TailPlusA5_pos hu
  unfold unequalFD4TailPlusShift
  positivity

/-! ## The swapped-chart tail polynomial -/

def unequalFD4TailMinusA0 (u : ℝ) : ℝ :=
  720 * u ^ 11 + 58440 * u ^ 10 + 2138280 * u ^ 9
    + 46540836 * u ^ 8 + 669363012 * u ^ 7
    + 6678187170 * u ^ 6 + 47161100844 * u ^ 5
    + 235790833206 * u ^ 4 + 818406673788 * u ^ 3
    + 1880336022864 * u ^ 2 + 2579112245520 * u
    + 1605296296800

def unequalFD4TailMinusA1 (u : ℝ) : ℝ :=
  600 * u ^ 11 + 49940 * u ^ 10 + 1874600 * u ^ 9
    + 41905196 * u ^ 8 + 620198830 * u ^ 7
    + 6386347083 * u ^ 6 + 46744686616 * u ^ 5
    + 243615602269 * u ^ 4 + 887955543362 * u ^ 3
    + 2162182110424 * u ^ 2 + 3177173929560 * u
    + 2143327493520

def unequalFD4TailMinusA2 (u : ℝ) : ℝ :=
  120 * u ^ 11 + 11260 * u ^ 10 + 471590 * u ^ 9
    + 11682526 * u ^ 8 + 190810958 * u ^ 7
    + 2163576410 * u ^ 6 + 17423854427 * u ^ 5
    + 99906810023 * u ^ 4 + 400669205060 * u ^ 3
    + 1072768675056 * u ^ 2 + 1729349457880 * u
    + 1273744556640

def unequalFD4TailMinusA3 (u : ℝ) : ℝ :=
  540 * u ^ 10 + 41850 * u ^ 9 + 1454366 * u ^ 8
    + 29864788 * u ^ 7 + 401585535 * u ^ 6
    + 3697751042 * u ^ 5 + 23631024693 * u ^ 4
    + 103579748510 * u ^ 3 + 298257237256 * u ^ 2
    + 509855085880 * u + 393177936240

def unequalFD4TailMinusA4 (u : ℝ) : ℝ :=
  60 * u ^ 10 + 4890 * u ^ 9 + 177230 * u ^ 8
    + 3768686 * u ^ 7 + 52151900 * u ^ 6
    + 491429163 * u ^ 5 + 3197496277 * u ^ 4
    + 14201553352 * u ^ 3 + 41251921552 * u ^ 2
    + 70838761800 * u + 54662391360

def unequalFD4TailMinusA5 (u : ℝ) : ℝ :=
  30 * u ^ 9 + 1950 * u ^ 8 + 56118 * u ^ 7
    + 938862 * u ^ 6 + 10067796 * u ^ 5
    + 71800164 * u ^ 4 + 340749528 * u ^ 3
    + 1038387792 * u ^ 2 + 1845093120 * u
    + 1457648640

def unequalFD4TailMinusShift (u v : ℝ) : ℝ :=
  unequalFD4TailMinusA0 u
    + unequalFD4TailMinusA1 u * v
    + unequalFD4TailMinusA2 u * v ^ 2
    + unequalFD4TailMinusA3 u * v ^ 3
    + unequalFD4TailMinusA4 u * v ^ 4
    + unequalFD4TailMinusA5 u * v ^ 5

theorem unequalFD4TailMinusA0_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailMinusA0 u := by
  unfold unequalFD4TailMinusA0
  positivity

theorem unequalFD4TailMinusA1_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailMinusA1 u := by
  unfold unequalFD4TailMinusA1
  positivity

theorem unequalFD4TailMinusA2_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailMinusA2 u := by
  unfold unequalFD4TailMinusA2
  positivity

theorem unequalFD4TailMinusA3_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailMinusA3 u := by
  unfold unequalFD4TailMinusA3
  positivity

theorem unequalFD4TailMinusA4_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailMinusA4 u := by
  unfold unequalFD4TailMinusA4
  positivity

theorem unequalFD4TailMinusA5_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < unequalFD4TailMinusA5 u := by
  unfold unequalFD4TailMinusA5
  positivity

theorem unequalFD4TailMinusShift_pos
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < unequalFD4TailMinusShift u v := by
  have h0 := unequalFD4TailMinusA0_pos hu
  have h1 := unequalFD4TailMinusA1_pos hu
  have h2 := unequalFD4TailMinusA2_pos hu
  have h3 := unequalFD4TailMinusA3_pos hu
  have h4 := unequalFD4TailMinusA4_pos hu
  have h5 := unequalFD4TailMinusA5_pos hu
  unfold unequalFD4TailMinusShift
  positivity

/-!
The following wrappers expose the shifted certificate directly in the
original parameter coordinates.  A later coefficient-identification module
can rewrite its exact numerator to these definitions without duplicating the
large positivity proof.
-/

def unequalFD4TailPlus (m n : ℝ) : ℝ :=
  unequalFD4TailPlusShift (m - 7) (n - 3)

def unequalFD4TailMinus (m n : ℝ) : ℝ :=
  unequalFD4TailMinusShift (m - 7) (n - 3)

theorem unequalFD4TailPlus_pos
    {m n : ℝ} (hm : 7 ≤ m) (hn : 3 ≤ n) :
    0 < unequalFD4TailPlus m n := by
  unfold unequalFD4TailPlus
  exact unequalFD4TailPlusShift_pos
    (sub_nonneg.mpr hm) (sub_nonneg.mpr hn)

theorem unequalFD4TailMinus_pos
    {m n : ℝ} (hm : 7 ≤ m) (hn : 3 ≤ n) :
    0 < unequalFD4TailMinus m n := by
  unfold unequalFD4TailMinus
  exact unequalFD4TailMinusShift_pos
    (sub_nonneg.mpr hm) (sub_nonneg.mpr hn)

end

end GraybillDeal
