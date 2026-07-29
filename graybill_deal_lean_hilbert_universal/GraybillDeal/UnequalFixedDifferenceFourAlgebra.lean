import GraybillDeal.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Algebra for the fixed-difference-four unequal family

This file records the elementary constants used for the sample-size family

`(n₁, n₂) = (2m - 1, 2m + 3)`, with `m ≥ 7`.

Equivalently, the residual degrees of freedom are `2(m - 1)` and
`2(m + 1)`, and the beta shapes are `m - 1` and `m + 1`.
All definitions below are real-valued functions of the natural-number
parameter `m`.
-/

namespace GraybillDeal

noncomputable section

/-- The beta pivot `(m - 1) / (2m)`. -/
def unequalFixedDifferenceFourT (m : ℕ) : ℝ :=
  ((m : ℝ) - 1) / (2 * (m : ℝ))

/-- The complementary beta pivot `(m + 1) / (2m)`. -/
def unequalFixedDifferenceFourQ (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) / (2 * (m : ℝ))

/-- The common polynomial denominator in the pivot certificate. -/
def unequalFixedDifferenceFourD (m : ℕ) : ℝ :=
  (m : ℝ) ^ 3 + 2 * (m : ℝ) ^ 2 - (m : ℝ) + 10

/-- The pivot-orthogonalizing asymmetric correction. -/
def unequalFixedDifferenceFourKappa (m : ℕ) : ℝ :=
  ((2 * (m : ℝ) + 5) * (5 * (m : ℝ) ^ 2 - 4 * (m : ℝ) + 3))
    / ((m : ℝ) ^ 2 * unequalFixedDifferenceFourD m)

/-- The constant multiplying the standardized squared mean difference. -/
def unequalFixedDifferenceFourC (m : ℕ) : ℝ :=
  (12 * (m : ℝ) ^ 2 + 2 * (m : ℝ) - 1)
    / (2 * (m : ℝ) * (2 * (m : ℝ) - 1))

/-- The positive pivot margin `-B(t)`. -/
def unequalFixedDifferenceFourB0 (m : ℕ) : ℝ :=
  (((m : ℝ) - 1)
      * ((m : ℝ) ^ 5 + 3 * (m : ℝ) ^ 4
        - 10 * (m : ℝ) ^ 2 - 17 * (m : ℝ) + 15))
    /
  (16 * (m : ℝ) ^ 3
      * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3)
      * unequalFixedDifferenceFourD m)

/-- The right-chart inverse-beta quadratic envelope. -/
def unequalFixedDifferenceFourMPlus (m : ℕ) : ℝ :=
  unequalFixedDifferenceFourQ m ^ 2
    * (((m : ℝ) + 1) * ((m : ℝ) + 2)
      / (((m : ℝ) - 2) * ((m : ℝ) - 3)))
    * (unequalFixedDifferenceFourC m ^ 2
      + 60 * (m : ℝ) ^ 2
        / (((m : ℝ) - 4) * ((m : ℝ) - 5)))

/-- The left-chart inverse-beta quadratic envelope. -/
def unequalFixedDifferenceFourMMinus (m : ℕ) : ℝ :=
  unequalFixedDifferenceFourQ m ^ 2
    * (unequalFixedDifferenceFourC m ^ 2
      + 60 * (m : ℝ) ^ 2
        / (((m : ℝ) - 2) * ((m : ℝ) - 3)))

/-- A fixed perturbation size for the sample-size pair indexed by `m`. -/
def unequalFixedDifferenceFourEpsilon (m : ℕ) : ℝ :=
  unequalFixedDifferenceFourB0 m / unequalFixedDifferenceFourMPlus m

private theorem unequalFixedDifferenceFour_cast_seven_le
    {m : ℕ} (hm : 7 ≤ m) :
    (7 : ℝ) ≤ (m : ℝ) := by
  exact_mod_cast hm

theorem unequalFixedDifferenceFourT_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourT m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  unfold unequalFixedDifferenceFourT
  exact div_pos (by linarith) (by positivity)

theorem unequalFixedDifferenceFourQ_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourQ m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  unfold unequalFixedDifferenceFourQ
  exact div_pos (by linarith) (by positivity)

theorem unequalFixedDifferenceFourD_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourD m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  have hu : 0 ≤ (m : ℝ) - 7 := by linarith
  have hshift :
      unequalFixedDifferenceFourD m
        =
      ((m : ℝ) - 7) ^ 3
        + 23 * ((m : ℝ) - 7) ^ 2
        + 174 * ((m : ℝ) - 7) + 444 := by
    unfold unequalFixedDifferenceFourD
    ring
  rw [hshift]
  positivity

theorem unequalFixedDifferenceFourKappaDenominator_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 <
      (m : ℝ) ^ 2 * unequalFixedDifferenceFourD m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  exact mul_pos (sq_pos_of_pos (by linarith))
    (unequalFixedDifferenceFourD_pos hm)

theorem unequalFixedDifferenceFourB0Denominator_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 <
      16 * (m : ℝ) ^ 3
        * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3)
        * unequalFixedDifferenceFourD m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  have hD := unequalFixedDifferenceFourD_pos hm
  positivity

theorem unequalFixedDifferenceFourKappa_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourKappa m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  have hquad :
      0 < 5 * (m : ℝ) ^ 2 - 4 * (m : ℝ) + 3 := by
    nlinarith [sq_nonneg ((m : ℝ) - 1)]
  unfold unequalFixedDifferenceFourKappa
  exact div_pos
    (mul_pos (by linarith) hquad)
    (unequalFixedDifferenceFourKappaDenominator_pos hm)

theorem unequalFixedDifferenceFourKappa_lt_one
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourKappa m < 1 := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  have hu : 0 ≤ (m : ℝ) - 7 := by linarith
  have hgap :
      0 <
        (m : ℝ) ^ 5 + 2 * (m : ℝ) ^ 4
          - 11 * (m : ℝ) ^ 3 - 7 * (m : ℝ) ^ 2
          + 14 * (m : ℝ) - 15 := by
    rw [show
      (m : ℝ) ^ 5 + 2 * (m : ℝ) ^ 4
          - 11 * (m : ℝ) ^ 3 - 7 * (m : ℝ) ^ 2
          + 14 * (m : ℝ) - 15
        =
      ((m : ℝ) - 7) ^ 5
        + 37 * ((m : ℝ) - 7) ^ 4
        + 535 * ((m : ℝ) - 7) ^ 3
        + 3780 * ((m : ℝ) - 7) ^ 2
        + 13048 * ((m : ℝ) - 7) + 17576 by ring]
    positivity
  unfold unequalFixedDifferenceFourKappa
  rw [div_lt_one (unequalFixedDifferenceFourKappaDenominator_pos hm)]
  unfold unequalFixedDifferenceFourD
  nlinarith

theorem unequalFixedDifferenceFourC_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourC m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  have hnum :
      0 < 12 * (m : ℝ) ^ 2 + 2 * (m : ℝ) - 1 := by
    nlinarith [sq_nonneg (m : ℝ)]
  unfold unequalFixedDifferenceFourC
  exact div_pos hnum (mul_pos (by positivity) (by linarith))

theorem unequalFixedDifferenceFourB0_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourB0 m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  have hu : 0 ≤ (m : ℝ) - 7 := by linarith
  have hpoly :
      0 <
        (m : ℝ) ^ 5 + 3 * (m : ℝ) ^ 4
          - 10 * (m : ℝ) ^ 2 - 17 * (m : ℝ) + 15 := by
    rw [show
      (m : ℝ) ^ 5 + 3 * (m : ℝ) ^ 4
          - 10 * (m : ℝ) ^ 2 - 17 * (m : ℝ) + 15
        =
      ((m : ℝ) - 7) ^ 5
        + 38 * ((m : ℝ) - 7) ^ 4
        + 574 * ((m : ℝ) - 7) ^ 3
        + 4302 * ((m : ℝ) - 7) ^ 2
        + 15964 * ((m : ℝ) - 7) + 23416 by ring]
    positivity
  unfold unequalFixedDifferenceFourB0
  exact div_pos
    (mul_pos (by linarith) hpoly)
    (unequalFixedDifferenceFourB0Denominator_pos hm)

theorem unequalFixedDifferenceFourMPlus_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourMPlus m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have hc := unequalFixedDifferenceFourC_pos hm
  have hden23 :
      0 < ((m : ℝ) - 2) * ((m : ℝ) - 3) :=
    mul_pos (by linarith) (by linarith)
  have hden45 :
      0 < ((m : ℝ) - 4) * ((m : ℝ) - 5) :=
    mul_pos (by linarith) (by linarith)
  unfold unequalFixedDifferenceFourMPlus
  exact mul_pos
    (mul_pos (sq_pos_of_pos hq)
      (div_pos (mul_pos (by linarith) (by linarith)) hden23))
    (add_pos (sq_pos_of_pos hc)
      (div_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
        hden45))

theorem unequalFixedDifferenceFourMMinus_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourMMinus m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have hc := unequalFixedDifferenceFourC_pos hm
  have hden23 :
      0 < ((m : ℝ) - 2) * ((m : ℝ) - 3) :=
    mul_pos (by linarith) (by linarith)
  unfold unequalFixedDifferenceFourMMinus
  exact mul_pos (sq_pos_of_pos hq)
    (add_pos (sq_pos_of_pos hc)
      (div_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
        hden23))

theorem unequalFixedDifferenceFourMMinus_lt_MPlus
    {m : ℕ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourMMinus m
      < unequalFixedDifferenceFourMPlus m := by
  have hmR := unequalFixedDifferenceFour_cast_seven_le hm
  have hq2 : 0 < unequalFixedDifferenceFourQ m ^ 2 :=
    sq_pos_of_pos (unequalFixedDifferenceFourQ_pos hm)
  have hc := unequalFixedDifferenceFourC_pos hm
  have hx : 0 < (m : ℝ) := by linarith
  have hnum : 0 < 60 * (m : ℝ) ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hx)
  have hden23 :
      0 < ((m : ℝ) - 2) * ((m : ℝ) - 3) :=
    mul_pos (by linarith) (by linarith)
  have hden45 :
      0 < ((m : ℝ) - 4) * ((m : ℝ) - 5) :=
    mul_pos (by linarith) (by linarith)
  have hden_lt :
      ((m : ℝ) - 4) * ((m : ℝ) - 5)
        < ((m : ℝ) - 2) * ((m : ℝ) - 3) := by
    nlinarith
  have hinv :
      60 * (m : ℝ) ^ 2
          / (((m : ℝ) - 2) * ((m : ℝ) - 3))
        <
      60 * (m : ℝ) ^ 2
          / (((m : ℝ) - 4) * ((m : ℝ) - 5)) := by
    rw [div_lt_div_iff₀ hden23 hden45]
    exact mul_lt_mul_of_pos_left hden_lt hnum
  have hbracket :
      unequalFixedDifferenceFourC m ^ 2
          + 60 * (m : ℝ) ^ 2
            / (((m : ℝ) - 2) * ((m : ℝ) - 3))
        <
      unequalFixedDifferenceFourC m ^ 2
          + 60 * (m : ℝ) ^ 2
            / (((m : ℝ) - 4) * ((m : ℝ) - 5)) := by
    linarith
  have hfactor :
      1 <
        ((m : ℝ) + 1) * ((m : ℝ) + 2)
          / (((m : ℝ) - 2) * ((m : ℝ) - 3)) := by
    apply (lt_div_iff₀ hden23).2
    nlinarith
  have hbracket_pos :
      0 <
        unequalFixedDifferenceFourC m ^ 2
          + 60 * (m : ℝ) ^ 2
            / (((m : ℝ) - 4) * ((m : ℝ) - 5)) := by
    exact add_pos (sq_pos_of_pos hc) (div_pos hnum hden45)
  unfold unequalFixedDifferenceFourMMinus
    unequalFixedDifferenceFourMPlus
  calc
    unequalFixedDifferenceFourQ m ^ 2
          * (unequalFixedDifferenceFourC m ^ 2
            + 60 * (m : ℝ) ^ 2
              / (((m : ℝ) - 2) * ((m : ℝ) - 3)))
        <
      unequalFixedDifferenceFourQ m ^ 2
          * (unequalFixedDifferenceFourC m ^ 2
            + 60 * (m : ℝ) ^ 2
              / (((m : ℝ) - 4) * ((m : ℝ) - 5))) :=
        mul_lt_mul_of_pos_left hbracket hq2
    _ <
      unequalFixedDifferenceFourQ m ^ 2
        * (((m : ℝ) + 1) * ((m : ℝ) + 2)
          / (((m : ℝ) - 2) * ((m : ℝ) - 3)))
        * (unequalFixedDifferenceFourC m ^ 2
          + 60 * (m : ℝ) ^ 2
            / (((m : ℝ) - 4) * ((m : ℝ) - 5))) := by
      have hscale :=
        mul_lt_mul_of_pos_right hfactor hbracket_pos
      nlinarith

theorem unequalFixedDifferenceFourEpsilon_pos
    {m : ℕ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourEpsilon m := by
  unfold unequalFixedDifferenceFourEpsilon
  exact div_pos
    (unequalFixedDifferenceFourB0_pos hm)
    (unequalFixedDifferenceFourMPlus_pos hm)

/--
The ratio-free deterministic endgame for the family choice
`ε(m) = b₀(m) / M₊(m)`.
-/
theorem unequalFixedDifferenceFour_reducedCoefficient_neg
    {m : ℕ} (hm : 7 ≤ m) :
    -2 * unequalFixedDifferenceFourEpsilon m
          * unequalFixedDifferenceFourB0 m
        + unequalFixedDifferenceFourEpsilon m ^ 2
          * unequalFixedDifferenceFourMPlus m
      < 0 := by
  have hb := unequalFixedDifferenceFourB0_pos hm
  have hM := unequalFixedDifferenceFourMPlus_pos hm
  have heq :
      -2 * unequalFixedDifferenceFourEpsilon m
            * unequalFixedDifferenceFourB0 m
          + unequalFixedDifferenceFourEpsilon m ^ 2
            * unequalFixedDifferenceFourMPlus m
        =
      -(unequalFixedDifferenceFourB0 m ^ 2
        / unequalFixedDifferenceFourMPlus m) := by
    unfold unequalFixedDifferenceFourEpsilon
    field_simp [hM.ne']
    ring
  rw [heq]
  exact neg_neg_of_pos
    (div_pos (sq_pos_of_pos hb) hM)

/--
The ratio-free reduced-risk inequality for the whole family.

Once the analytic charts supply

`B ≤ -b₀(m) (1-s)²` and `C ≤ M₊(m) (1-s)²`,

the fixed pair-dependent choice `ε(m) = b₀(m) / M₊(m)` makes the reduced
quadratic strictly negative for every `s < 1`.
-/
theorem unequalFixedDifferenceFour_reducedRisk_neg_of_bounds
    {m : ℕ} (hm : 7 ≤ m) {s B C : ℝ} (hs : s < 1)
    (hB :
      B ≤ -unequalFixedDifferenceFourB0 m * (1 - s) ^ 2)
    (hC :
      C ≤ unequalFixedDifferenceFourMPlus m * (1 - s) ^ 2) :
    2 * unequalFixedDifferenceFourEpsilon m * B
        + unequalFixedDifferenceFourEpsilon m ^ 2 * C
      < 0 := by
  have hε := unequalFixedDifferenceFourEpsilon_pos hm
  have hε2 : 0 ≤ unequalFixedDifferenceFourEpsilon m ^ 2 :=
    sq_nonneg _
  have hsq : 0 < (1 - s) ^ 2 := by
    positivity
  have hcoefficient :=
    unequalFixedDifferenceFour_reducedCoefficient_neg hm
  calc
    2 * unequalFixedDifferenceFourEpsilon m * B
          + unequalFixedDifferenceFourEpsilon m ^ 2 * C
        ≤
      2 * unequalFixedDifferenceFourEpsilon m
          * (-unequalFixedDifferenceFourB0 m * (1 - s) ^ 2)
        + unequalFixedDifferenceFourEpsilon m ^ 2
          * (unequalFixedDifferenceFourMPlus m * (1 - s) ^ 2) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hB
                (mul_nonneg (by norm_num) hε.le))
              (mul_le_mul_of_nonneg_left hC hε2)
    _ =
      (1 - s) ^ 2
        * (-2 * unequalFixedDifferenceFourEpsilon m
            * unequalFixedDifferenceFourB0 m
          + unequalFixedDifferenceFourEpsilon m ^ 2
            * unequalFixedDifferenceFourMPlus m) := by
          ring
    _ < 0 := mul_neg_of_pos_of_neg hsq hcoefficient

end

end GraybillDeal
