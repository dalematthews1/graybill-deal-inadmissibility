import GraybillDeal.Elementary
import GraybillDeal.UnequalFixedDifferenceFourCoefficients
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Real-parameter algebra for the fixed-difference-four family

This file is the real-parameter counterpart of
`UnequalFixedDifferenceFourAlgebra`.  The natural parameter in that module
reaches the odd sample-size pairs

`(n₁, n₂) = (2m - 1, 2m + 3)`.

Allowing `m : ℝ` also covers the half-integral parameters arising from even
sample sizes.  All elementary signs, the comparison of the two quadratic
envelopes, and the ratio-free reduced-risk endgame hold unchanged for every
real `m ≥ 7`.
-/

namespace GraybillDeal

noncomputable section

/-- The beta pivot `(m - 1) / (2m)`, for real `m`. -/
def unequalFixedDifferenceFourRealT (m : ℝ) : ℝ :=
  (m - 1) / (2 * m)

/-- The complementary beta pivot `(m + 1) / (2m)`, for real `m`. -/
def unequalFixedDifferenceFourRealQ (m : ℝ) : ℝ :=
  (m + 1) / (2 * m)

/-- The common polynomial denominator in the pivot certificate. -/
def unequalFixedDifferenceFourRealD (m : ℝ) : ℝ :=
  m ^ 3 + 2 * m ^ 2 - m + 10

/-- The pivot-orthogonalizing asymmetric correction. -/
def unequalFixedDifferenceFourRealKappa (m : ℝ) : ℝ :=
  ((2 * m + 5) * (5 * m ^ 2 - 4 * m + 3))
    / (m ^ 2 * unequalFixedDifferenceFourRealD m)

/-- The constant multiplying the standardized squared mean difference. -/
def unequalFixedDifferenceFourRealC (m : ℝ) : ℝ :=
  (12 * m ^ 2 + 2 * m - 1) / (2 * m * (2 * m - 1))

/-- The positive pivot margin `-B(t)`. -/
def unequalFixedDifferenceFourRealB0 (m : ℝ) : ℝ :=
  ((m - 1) * (m ^ 5 + 3 * m ^ 4 - 10 * m ^ 2 - 17 * m + 15))
    /
  (16 * m ^ 3 * (2 * m + 1) * (2 * m + 3)
    * unequalFixedDifferenceFourRealD m)

/-- The right-chart inverse-beta quadratic envelope. -/
def unequalFixedDifferenceFourRealMPlus (m : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealQ m ^ 2
    * ((m + 1) * (m + 2) / ((m - 2) * (m - 3)))
    * (unequalFixedDifferenceFourRealC m ^ 2
      + 60 * m ^ 2 / ((m - 4) * (m - 5)))

/-- The left-chart inverse-beta quadratic envelope. -/
def unequalFixedDifferenceFourRealMMinus (m : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealQ m ^ 2
    * (unequalFixedDifferenceFourRealC m ^ 2
      + 60 * m ^ 2 / ((m - 2) * (m - 3)))

/-- A fixed perturbation size for the sample-size pair indexed by `m`. -/
def unequalFixedDifferenceFourRealEpsilon (m : ℝ) : ℝ :=
  unequalFixedDifferenceFourRealB0 m
    / unequalFixedDifferenceFourRealMPlus m

theorem unequalFixedDifferenceFourRealT_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealT m := by
  unfold unequalFixedDifferenceFourRealT
  exact div_pos (by linarith) (by positivity)

theorem unequalFixedDifferenceFourRealQ_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealQ m := by
  unfold unequalFixedDifferenceFourRealQ
  exact div_pos (by linarith) (by positivity)

theorem unequalFixedDifferenceFourRealD_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealD m := by
  have hu : 0 ≤ m - 7 := by linarith
  have hshift :
      unequalFixedDifferenceFourRealD m
        =
      (m - 7) ^ 3 + 23 * (m - 7) ^ 2
        + 174 * (m - 7) + 444 := by
    unfold unequalFixedDifferenceFourRealD
    ring
  rw [hshift]
  positivity

theorem unequalFixedDifferenceFourRealKappaDenominator_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < m ^ 2 * unequalFixedDifferenceFourRealD m := by
  exact mul_pos (sq_pos_of_pos (by linarith))
    (unequalFixedDifferenceFourRealD_pos hm)

theorem unequalFixedDifferenceFourRealB0Denominator_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 <
      16 * m ^ 3 * (2 * m + 1) * (2 * m + 3)
        * unequalFixedDifferenceFourRealD m := by
  have hD := unequalFixedDifferenceFourRealD_pos hm
  positivity

theorem unequalFixedDifferenceFourRealKappa_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealKappa m := by
  have hquad : 0 < 5 * m ^ 2 - 4 * m + 3 := by
    nlinarith [sq_nonneg (m - 1)]
  unfold unequalFixedDifferenceFourRealKappa
  exact div_pos
    (mul_pos (by linarith) hquad)
    (unequalFixedDifferenceFourRealKappaDenominator_pos hm)

theorem unequalFixedDifferenceFourRealKappa_lt_one
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealKappa m < 1 := by
  have hu : 0 ≤ m - 7 := by linarith
  have hgap :
      0 <
        m ^ 5 + 2 * m ^ 4 - 11 * m ^ 3 - 7 * m ^ 2
          + 14 * m - 15 := by
    rw [show
      m ^ 5 + 2 * m ^ 4 - 11 * m ^ 3 - 7 * m ^ 2
          + 14 * m - 15
        =
      (m - 7) ^ 5 + 37 * (m - 7) ^ 4
        + 535 * (m - 7) ^ 3 + 3780 * (m - 7) ^ 2
        + 13048 * (m - 7) + 17576 by ring]
    positivity
  unfold unequalFixedDifferenceFourRealKappa
  rw [div_lt_one (unequalFixedDifferenceFourRealKappaDenominator_pos hm)]
  unfold unequalFixedDifferenceFourRealD
  nlinarith

theorem unequalFixedDifferenceFourRealC_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealC m := by
  have hnum : 0 < 12 * m ^ 2 + 2 * m - 1 := by
    nlinarith [sq_nonneg m]
  unfold unequalFixedDifferenceFourRealC
  exact div_pos hnum (mul_pos (by positivity) (by linarith))

theorem unequalFixedDifferenceFourRealB0_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealB0 m := by
  have hnum : 0 < unequalFD4HeadZero m :=
    unequalFD4HeadZero_pos hm
  have hden := unequalFixedDifferenceFourRealB0Denominator_pos hm
  unfold unequalFixedDifferenceFourRealB0 unequalFD4HeadZero at *
  exact div_pos hnum hden

theorem unequalFixedDifferenceFourRealMPlus_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealMPlus m := by
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have hc := unequalFixedDifferenceFourRealC_pos hm
  have hden23 : 0 < (m - 2) * (m - 3) :=
    mul_pos (by linarith) (by linarith)
  have hden45 : 0 < (m - 4) * (m - 5) :=
    mul_pos (by linarith) (by linarith)
  unfold unequalFixedDifferenceFourRealMPlus
  exact mul_pos
    (mul_pos (sq_pos_of_pos hq)
      (div_pos (mul_pos (by linarith) (by linarith)) hden23))
    (add_pos (sq_pos_of_pos hc)
      (div_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
        hden45))

theorem unequalFixedDifferenceFourRealMMinus_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealMMinus m := by
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have hc := unequalFixedDifferenceFourRealC_pos hm
  have hden23 : 0 < (m - 2) * (m - 3) :=
    mul_pos (by linarith) (by linarith)
  unfold unequalFixedDifferenceFourRealMMinus
  exact mul_pos (sq_pos_of_pos hq)
    (add_pos (sq_pos_of_pos hc)
      (div_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
        hden23))

theorem unequalFixedDifferenceFourRealMMinus_lt_MPlus
    {m : ℝ} (hm : 7 ≤ m) :
    unequalFixedDifferenceFourRealMMinus m
      < unequalFixedDifferenceFourRealMPlus m := by
  have hq2 : 0 < unequalFixedDifferenceFourRealQ m ^ 2 :=
    sq_pos_of_pos (unequalFixedDifferenceFourRealQ_pos hm)
  have hc := unequalFixedDifferenceFourRealC_pos hm
  have hx : 0 < m := by linarith
  have hnum : 0 < 60 * m ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hx)
  have hden23 : 0 < (m - 2) * (m - 3) :=
    mul_pos (by linarith) (by linarith)
  have hden45 : 0 < (m - 4) * (m - 5) :=
    mul_pos (by linarith) (by linarith)
  have hden_lt : (m - 4) * (m - 5) < (m - 2) * (m - 3) := by
    nlinarith
  have hinv :
      60 * m ^ 2 / ((m - 2) * (m - 3))
        <
      60 * m ^ 2 / ((m - 4) * (m - 5)) := by
    rw [div_lt_div_iff₀ hden23 hden45]
    exact mul_lt_mul_of_pos_left hden_lt hnum
  have hbracket :
      unequalFixedDifferenceFourRealC m ^ 2
          + 60 * m ^ 2 / ((m - 2) * (m - 3))
        <
      unequalFixedDifferenceFourRealC m ^ 2
          + 60 * m ^ 2 / ((m - 4) * (m - 5)) := by
    linarith
  have hfactor :
      1 < (m + 1) * (m + 2) / ((m - 2) * (m - 3)) := by
    apply (lt_div_iff₀ hden23).2
    nlinarith
  have hbracket_pos :
      0 <
        unequalFixedDifferenceFourRealC m ^ 2
          + 60 * m ^ 2 / ((m - 4) * (m - 5)) := by
    exact add_pos (sq_pos_of_pos hc) (div_pos hnum hden45)
  unfold unequalFixedDifferenceFourRealMMinus
    unequalFixedDifferenceFourRealMPlus
  calc
    unequalFixedDifferenceFourRealQ m ^ 2
          * (unequalFixedDifferenceFourRealC m ^ 2
            + 60 * m ^ 2 / ((m - 2) * (m - 3)))
        <
      unequalFixedDifferenceFourRealQ m ^ 2
          * (unequalFixedDifferenceFourRealC m ^ 2
            + 60 * m ^ 2 / ((m - 4) * (m - 5))) :=
        mul_lt_mul_of_pos_left hbracket hq2
    _ <
      unequalFixedDifferenceFourRealQ m ^ 2
        * ((m + 1) * (m + 2) / ((m - 2) * (m - 3)))
        * (unequalFixedDifferenceFourRealC m ^ 2
          + 60 * m ^ 2 / ((m - 4) * (m - 5))) := by
      have hscale :=
        mul_lt_mul_of_pos_right hfactor hbracket_pos
      nlinarith

theorem unequalFixedDifferenceFourRealEpsilon_pos
    {m : ℝ} (hm : 7 ≤ m) :
    0 < unequalFixedDifferenceFourRealEpsilon m := by
  unfold unequalFixedDifferenceFourRealEpsilon
  exact div_pos
    (unequalFixedDifferenceFourRealB0_pos hm)
    (unequalFixedDifferenceFourRealMPlus_pos hm)

/--
The ratio-free deterministic endgame for the real-parameter family choice
`ε(m) = b₀(m) / M₊(m)`.
-/
theorem unequalFixedDifferenceFourReal_reducedCoefficient_neg
    {m : ℝ} (hm : 7 ≤ m) :
    -2 * unequalFixedDifferenceFourRealEpsilon m
          * unequalFixedDifferenceFourRealB0 m
        + unequalFixedDifferenceFourRealEpsilon m ^ 2
          * unequalFixedDifferenceFourRealMPlus m
      < 0 := by
  have hb := unequalFixedDifferenceFourRealB0_pos hm
  have hM := unequalFixedDifferenceFourRealMPlus_pos hm
  have heq :
      -2 * unequalFixedDifferenceFourRealEpsilon m
            * unequalFixedDifferenceFourRealB0 m
          + unequalFixedDifferenceFourRealEpsilon m ^ 2
            * unequalFixedDifferenceFourRealMPlus m
        =
      -(unequalFixedDifferenceFourRealB0 m ^ 2
        / unequalFixedDifferenceFourRealMPlus m) := by
    unfold unequalFixedDifferenceFourRealEpsilon
    field_simp [hM.ne']
    ring
  rw [heq]
  exact neg_neg_of_pos (div_pos (sq_pos_of_pos hb) hM)

/--
The ratio-free reduced-risk inequality for the real-parameter family.

Once the analytic charts supply

`B ≤ -b₀(m) (1-s)²` and `C ≤ M₊(m) (1-s)²`,

the fixed pair-dependent choice `ε(m) = b₀(m) / M₊(m)` makes the reduced
quadratic strictly negative for every `s < 1`.
-/
theorem unequalFixedDifferenceFourReal_reducedRisk_neg_of_bounds
    {m : ℝ} (hm : 7 ≤ m) {s B C : ℝ} (hs : s < 1)
    (hB :
      B ≤ -unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2)
    (hC :
      C ≤ unequalFixedDifferenceFourRealMPlus m * (1 - s) ^ 2) :
    2 * unequalFixedDifferenceFourRealEpsilon m * B
        + unequalFixedDifferenceFourRealEpsilon m ^ 2 * C
      < 0 := by
  have hε := unequalFixedDifferenceFourRealEpsilon_pos hm
  have hε2 : 0 ≤ unequalFixedDifferenceFourRealEpsilon m ^ 2 :=
    sq_nonneg _
  have hsq : 0 < (1 - s) ^ 2 := by
    positivity
  have hcoefficient :=
    unequalFixedDifferenceFourReal_reducedCoefficient_neg hm
  calc
    2 * unequalFixedDifferenceFourRealEpsilon m * B
          + unequalFixedDifferenceFourRealEpsilon m ^ 2 * C
        ≤
      2 * unequalFixedDifferenceFourRealEpsilon m
          * (-unequalFixedDifferenceFourRealB0 m * (1 - s) ^ 2)
        + unequalFixedDifferenceFourRealEpsilon m ^ 2
          * (unequalFixedDifferenceFourRealMPlus m * (1 - s) ^ 2) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hB
                (mul_nonneg (by norm_num) hε.le))
              (mul_le_mul_of_nonneg_left hC hε2)
    _ =
      (1 - s) ^ 2
        * (-2 * unequalFixedDifferenceFourRealEpsilon m
            * unequalFixedDifferenceFourRealB0 m
          + unequalFixedDifferenceFourRealEpsilon m ^ 2
            * unequalFixedDifferenceFourRealMPlus m) := by
          ring
    _ < 0 := mul_neg_of_pos_of_neg hsq hcoefficient

end

end GraybillDeal
