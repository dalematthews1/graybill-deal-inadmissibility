import GraybillDeal.Algebra
import Mathlib.Tactic.FieldSimp

/-!
# Sample-size-uniform algebra for the Graybill--Deal certificate

This file starts the extension of the fixed `n = 13` analytic certificate to
an arbitrary equal sample size.  We write `ν = n - 1` for the residual
degrees of freedom.

After pairing the centered beta integral and discarding the positive series
tail, the normalized first three terms are the quadratic

`Lν(z) = Aν + Bν z + Cν z²`, `0 ≤ z ≤ 1`.

The main result below proves `Lν(z) > 0` for every natural `ν ≥ 9`, exactly
the range corresponding to equal sample sizes `n ≥ 10`.  The proof follows
the two regimes in Section 7 of the counterexample note:

* through `ν = 134`, the discriminant is negative;
* from `ν = 135` onward, the vertex lies to the right of `1`, so the
  endpoint value at `z = 1` is a positive lower bound.

No probability or integration facts are used in this module.
-/

namespace GraybillDeal

noncomputable section

/-- The constant coefficient in the general first-three-term certificate. -/
def generalA (ν : ℝ) : ℝ :=
  (ν - 4) / (2 * (ν - 1))

/-- The (negative) linear coefficient in the general certificate. -/
def generalB (ν : ℝ) : ℝ :=
  -(ν ^ 2 + 4 * ν + 40) / (2 * (ν - 1) * (ν + 5))

/-- The positive quadratic coefficient in the general certificate. -/
def generalC (ν : ℝ) : ℝ :=
  15 * (5 * ν ^ 2 - 19 * ν - 28) /
    (2 * (ν - 1) * (ν + 5) * (ν + 7))

/-- The normalized first three integrated series terms. -/
def generalLowerQuadratic (ν z : ℝ) : ℝ :=
  generalA ν + generalB ν * z + generalC ν * z ^ 2

/-- The polynomial controlling the discriminant of `generalLowerQuadratic`. -/
def generalDiscriminantNumerator (ν : ℝ) : ℝ :=
  ν ^ 5 - 285 * ν ^ 4 + 992 * ν ^ 3 + 9812 * ν ^ 2
    - 17280 * ν - 22400

/-- An auxiliary cubic used to control the discriminant for `ν ≤ 134`. -/
def generalDiscriminantCubic (ν : ℝ) : ℝ :=
  ν ^ 3 - 285 * ν ^ 2 + 992 * ν + 9812

/-- The polynomial controlling whether the vertex lies to the right of `1`. -/
def generalVertexNumerator (ν : ℝ) : ℝ :=
  ν ^ 3 - 139 * ν ^ 2 + 638 * ν + 1120

/-- The global real-line minimum furnished by completing the square. -/
def generalVertexLower (ν : ℝ) : ℝ :=
  (4 * generalA ν * generalC ν - generalB ν ^ 2) /
    (4 * generalC ν)

theorem generalA_pos {ν : ℝ} (hν : 9 ≤ ν) :
    0 < generalA ν := by
  unfold generalA
  apply div_pos <;> nlinarith

theorem generalB_neg {ν : ℝ} (hν : 9 ≤ ν) :
    generalB ν < 0 := by
  unfold generalB
  have hnum : 0 < ν ^ 2 + 4 * ν + 40 := by positivity
  have h1 : 0 < ν - 1 := by linarith
  have h5 : 0 < ν + 5 := by linarith
  have hden : 0 < 2 * (ν - 1) * (ν + 5) :=
    mul_pos (mul_pos (by norm_num) h1) h5
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden

theorem generalC_pos {ν : ℝ} (hν : 9 ≤ ν) :
    0 < generalC ν := by
  unfold generalC
  have hpoly : 0 < 5 * ν ^ 2 - 19 * ν - 28 := by
    nlinarith [sq_nonneg (ν - 9)]
  have h1 : 0 < ν - 1 := by linarith
  have h5 : 0 < ν + 5 := by linarith
  have h7 : 0 < ν + 7 := by linarith
  exact div_pos (mul_pos (by norm_num) hpoly)
    (mul_pos (mul_pos (mul_pos (by norm_num) h1) h5) h7)

theorem generalDiscriminantNumerator_eq {ν : ℝ} :
    generalDiscriminantNumerator ν
      =
    ν ^ 2 * generalDiscriminantCubic ν - 17280 * ν - 22400 := by
  unfold generalDiscriminantNumerator generalDiscriminantCubic
  ring

theorem generalDiscriminantCubic_eq_at_nine {ν : ℝ} :
    generalDiscriminantCubic ν
      =
    -3616 + (ν - 9) * (ν ^ 2 - 276 * ν - 1492) := by
  unfold generalDiscriminantCubic
  ring

theorem generalDiscriminantCubic_neg {ν : ℝ}
    (hνlo : 9 ≤ ν) (hνhi : ν ≤ 134) :
    generalDiscriminantCubic ν < 0 := by
  have hprod : 0 ≤ ν * (134 - ν) := by positivity
  have hquad : ν ^ 2 - 276 * ν - 1492 < 0 := by
    nlinarith
  rw [generalDiscriminantCubic_eq_at_nine]
  have hmul :
      (ν - 9) * (ν ^ 2 - 276 * ν - 1492) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hquad)
  linarith

theorem generalDiscriminantNumerator_neg {ν : ℝ}
    (hνlo : 9 ≤ ν) (hνhi : ν ≤ 134) :
    generalDiscriminantNumerator ν < 0 := by
  have hcubic := generalDiscriminantCubic_neg hνlo hνhi
  have hνpos : 0 < ν := by linarith
  have hmul : ν ^ 2 * generalDiscriminantCubic ν < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos hνpos) hcubic
  rw [generalDiscriminantNumerator_eq]
  nlinarith

theorem general_discriminant_gap_eq {ν : ℝ} (hν : 9 ≤ ν) :
    4 * generalA ν * generalC ν - generalB ν ^ 2
      =
    -generalDiscriminantNumerator ν /
      (4 * (ν - 1) ^ 2 * (ν + 5) ^ 2 * (ν + 7)) := by
  have h1 : ν - 1 ≠ 0 := by nlinarith
  have h5 : ν + 5 ≠ 0 := by nlinarith
  have h7 : ν + 7 ≠ 0 := by nlinarith
  unfold generalA generalB generalC
  field_simp [h1, h5, h7]
  unfold generalDiscriminantNumerator
  ring

theorem general_discriminant_gap_pos {ν : ℝ}
    (hνlo : 9 ≤ ν) (hνhi : ν ≤ 134) :
    0 < 4 * generalA ν * generalC ν - generalB ν ^ 2 := by
  rw [general_discriminant_gap_eq hνlo]
  have hnum : 0 < -generalDiscriminantNumerator ν := by
    linarith [generalDiscriminantNumerator_neg hνlo hνhi]
  have hden :
      0 < 4 * (ν - 1) ^ 2 * (ν + 5) ^ 2 * (ν + 7) := by
    have h1 : 0 < ν - 1 := by linarith
    have h5 : 0 < ν + 5 := by linarith
    have h7 : 0 < ν + 7 := by linarith
    positivity
  exact div_pos hnum hden

theorem generalLowerQuadratic_eq_completedSquare {ν z : ℝ}
    (hν : 9 ≤ ν) :
    generalLowerQuadratic ν z
      =
    ((2 * generalC ν * z + generalB ν) ^ 2
        + (4 * generalA ν * generalC ν - generalB ν ^ 2)) /
      (4 * generalC ν) := by
  have hC : generalC ν ≠ 0 := ne_of_gt (generalC_pos hν)
  unfold generalLowerQuadratic
  field_simp [hC]
  ring

theorem generalVertexLower_pos {ν : ℝ}
    (hνlo : 9 ≤ ν) (hνhi : ν ≤ 134) :
    0 < generalVertexLower ν := by
  unfold generalVertexLower
  exact div_pos (general_discriminant_gap_pos hνlo hνhi)
    (by positivity [generalC_pos hνlo])

theorem generalVertexLower_le {ν z : ℝ} (hν : 9 ≤ ν) :
    generalVertexLower ν ≤ generalLowerQuadratic ν z := by
  rw [generalLowerQuadratic_eq_completedSquare hν]
  unfold generalVertexLower
  have hden : 0 < 4 * generalC ν := by positivity [generalC_pos hν]
  apply div_le_div_of_nonneg_right _ (le_of_lt hden)
  nlinarith [sq_nonneg (2 * generalC ν * z + generalB ν)]

theorem generalVertexNumerator_eq_at_135 {ν : ℝ} :
    generalVertexNumerator ν
      =
    14350 + (ν - 135) * (ν ^ 2 - 4 * ν + 98) := by
  unfold generalVertexNumerator
  ring

theorem generalVertexNumerator_pos {ν : ℝ} (hν : 135 ≤ ν) :
    0 < generalVertexNumerator ν := by
  rw [generalVertexNumerator_eq_at_135]
  have hquad : 0 < ν ^ 2 - 4 * ν + 98 := by
    nlinarith [sq_nonneg (ν - 2)]
  have hmul : 0 ≤ (ν - 135) * (ν ^ 2 - 4 * ν + 98) := by
    positivity
  linarith

theorem general_B_add_two_C_eq {ν : ℝ} (hν : 9 ≤ ν) :
    generalB ν + 2 * generalC ν
      =
    -generalVertexNumerator ν /
      (2 * (ν - 1) * (ν + 5) * (ν + 7)) := by
  have h1 : ν - 1 ≠ 0 := by nlinarith
  have h5 : ν + 5 ≠ 0 := by nlinarith
  have h7 : ν + 7 ≠ 0 := by nlinarith
  unfold generalB generalC
  field_simp [h1, h5, h7]
  unfold generalVertexNumerator
  ring

theorem general_B_add_two_C_neg {ν : ℝ} (hν : 135 ≤ ν) :
    generalB ν + 2 * generalC ν < 0 := by
  rw [general_B_add_two_C_eq (by linarith)]
  have hnum : -generalVertexNumerator ν < 0 := by
    linarith [generalVertexNumerator_pos hν]
  have h1 : 0 < ν - 1 := by linarith
  have h5 : 0 < ν + 5 := by linarith
  have h7 : 0 < ν + 7 := by linarith
  have hden : 0 < 2 * (ν - 1) * (ν + 5) * (ν + 7) :=
    mul_pos (mul_pos (mul_pos (by norm_num) h1) h5) h7
  exact div_neg_of_neg_of_pos hnum hden

theorem generalLowerQuadratic_one_eq {ν : ℝ} (hν : 9 ≤ ν) :
    generalLowerQuadratic ν 1
      =
    6 * (12 * ν ^ 2 - 61 * ν - 140) /
      (2 * (ν - 1) * (ν + 5) * (ν + 7)) := by
  have h1 : ν - 1 ≠ 0 := by nlinarith
  have h5 : ν + 5 ≠ 0 := by nlinarith
  have h7 : ν + 7 ≠ 0 := by nlinarith
  unfold generalLowerQuadratic generalA generalB generalC
  field_simp [h1, h5, h7]
  ring

theorem generalLowerQuadratic_one_pos {ν : ℝ} (hν : 135 ≤ ν) :
    0 < generalLowerQuadratic ν 1 := by
  rw [generalLowerQuadratic_one_eq (by linarith)]
  have hpoly : 0 < 12 * ν ^ 2 - 61 * ν - 140 := by
    nlinarith [sq_nonneg (ν - 135)]
  have h1 : 0 < ν - 1 := by linarith
  have h5 : 0 < ν + 5 := by linarith
  have h7 : 0 < ν + 7 := by linarith
  exact div_pos (mul_pos (by norm_num) hpoly)
    (mul_pos (mul_pos (mul_pos (by norm_num) h1) h5) h7)

theorem generalLowerQuadratic_one_le {ν z : ℝ}
    (hν : 135 ≤ ν) (_hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    generalLowerQuadratic ν 1 ≤ generalLowerQuadratic ν z := by
  have hC := generalC_pos (show 9 ≤ ν by linarith)
  have hslope :
      generalB ν + generalC ν * (z + 1) < 0 := by
    have hcz : generalC ν * (z + 1) ≤ generalC ν * 2 := by
      exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hC)
    linarith [general_B_add_two_C_neg hν]
  have hfactor : z - 1 ≤ 0 := by linarith
  have hproduct :
      0 ≤ (z - 1) * (generalB ν + generalC ν * (z + 1)) :=
    mul_nonneg_of_nonpos_of_nonpos hfactor (le_of_lt hslope)
  unfold generalLowerQuadratic
  nlinarith

/--
The sample-size-dependent first-three-term lower bound is strictly positive
for every residual degree of freedom `ν ≥ 9`.
-/
theorem generalLowerQuadratic_pos_nat
    (ν : ℕ) (hν : 9 ≤ ν) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < generalLowerQuadratic (ν : ℝ) z := by
  by_cases hsmall : ν ≤ 134
  · have hνlo : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
    have hνhi : (ν : ℝ) ≤ 134 := by exact_mod_cast hsmall
    exact (generalVertexLower_pos hνlo hνhi).trans_le
      (generalVertexLower_le hνlo)
  · have hlarge : 135 ≤ ν := by
      exact Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hsmall)
    have hlargeR : (135 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hlarge
    exact (generalLowerQuadratic_one_pos hlargeR).trans_le
      (generalLowerQuadratic_one_le hlargeR hz0 hz1)

/--
The same positivity theorem stated directly in terms of equal sample size
`n`, with residual degrees of freedom `ν = n - 1`.
-/
theorem generalLowerQuadratic_pos_sampleSize
    (n : ℕ) (hn : 10 ≤ n) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < generalLowerQuadratic ((n - 1 : ℕ) : ℝ) z := by
  have hν : 9 ≤ n - 1 := by
    have := Nat.sub_le_sub_right hn 1
    norm_num at this ⊢
    exact this
  exact generalLowerQuadratic_pos_nat (n - 1) hν hz0 hz1

/--
The rational threshold obtained by evaluating the exact linear/quadratic
integral ratio in the boundary limit `|s| → 1`.  Identifying this algebraic
quantity with that analytic limit belongs to the generalized integration
layer; here we record the formula and its decisive large-`ν` comparison.
-/
def generalEndpointThreshold (ν : ℝ) : ℝ :=
  288 * (ν - 8) / ((ν + 2) * (7 * ν ^ 2 - 32 * ν + 768))

theorem generalEndpointThreshold_pos {ν : ℝ} (hν : 9 ≤ ν) :
    0 < generalEndpointThreshold ν := by
  unfold generalEndpointThreshold
  have hquad : 0 < 7 * ν ^ 2 - 32 * ν + 768 := by
    nlinarith [sq_nonneg (ν - 9)]
  have hnum : 0 < 288 * (ν - 8) := by
    exact mul_pos (by norm_num) (by linarith)
  have hden :
      0 < (ν + 2) * (7 * ν ^ 2 - 32 * ν + 768) :=
    mul_pos (by linarith) hquad
  exact div_pos hnum hden

/--
The fixed `n = 13` choice `1 / 2000` is already larger than the boundary
threshold for every real `ν ≥ 284`.  Thus it cannot be the coefficient in a
single all-sample-size theorem once the endpoint-limit identity is connected
to the risk calculation.
-/
theorem generalEndpointThreshold_lt_one_div_2000
    {ν : ℝ} (hν : 284 ≤ ν) :
    generalEndpointThreshold ν < 1 / 2000 := by
  have hquad : 0 < 7 * ν ^ 2 - 32 * ν + 768 := by
    nlinarith [sq_nonneg (ν - 284)]
  have hden :
      0 < (ν + 2) * (7 * ν ^ 2 - 32 * ν + 768) := by
    positivity
  unfold generalEndpointThreshold
  rw [div_lt_iff₀ hden]
  have haux : 0 < 7 * ν ^ 2 + 1970 * ν - 15816 := by
    nlinarith [sq_nonneg (ν - 284)]
  have hprod :
      0 ≤ (ν - 284) * (7 * ν ^ 2 + 1970 * ν - 15816) := by
    positivity
  have hpoly :
      0 < 7 * ν ^ 3 - 18 * ν ^ 2 - 575296 * ν + 4609536 := by
    calc
      7 * ν ^ 3 - 18 * ν ^ 2 - 575296 * ν + 4609536
          =
        117792
          + (ν - 284) * (7 * ν ^ 2 + 1970 * ν - 15816) := by
            ring
      _ > 0 := by linarith
  nlinarith

/--
For every fixed `ν ≥ 9`, positive moment factor `M`, and positive quadratic
allowance `H`, some positive perturbation size works uniformly for all
`z ∈ [0,1]`.  This is the purely algebraic final step once the generalized
integral bounds have supplied `M`, `H`, and `Lν`.
-/
theorem exists_general_epsilon
    (ν : ℕ) (hν : 9 ≤ ν) (M H : ℝ) (hM : 0 < M) (hH : 0 < H) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
        ε * H < M * generalLowerQuadratic (ν : ℝ) z := by
  by_cases hsmall : ν ≤ 134
  · let ell := generalVertexLower (ν : ℝ)
    have hνlo : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
    have hνhi : (ν : ℝ) ≤ 134 := by exact_mod_cast hsmall
    have hell : 0 < ell := generalVertexLower_pos hνlo hνhi
    refine ⟨M * ell / (2 * H), ?_, ?_⟩
    · positivity
    · intro z hz0 hz1
      have hlower : ell ≤ generalLowerQuadratic (ν : ℝ) z :=
        generalVertexLower_le hνlo
      have hMell : 0 < M * ell := mul_pos hM hell
      have hhalf : M * ell / 2 < M * ell := by linarith
      calc
        M * ell / (2 * H) * H = M * ell / 2 := by
          field_simp [ne_of_gt hH]
        _ < M * ell := hhalf
        _ ≤ M * generalLowerQuadratic (ν : ℝ) z :=
          mul_le_mul_of_nonneg_left hlower (le_of_lt hM)
  · have hlarge : 135 ≤ ν := by
      exact Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hsmall)
    have hlargeR : (135 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hlarge
    let ell := generalLowerQuadratic (ν : ℝ) 1
    have hell : 0 < ell := generalLowerQuadratic_one_pos hlargeR
    refine ⟨M * ell / (2 * H), ?_, ?_⟩
    · positivity
    · intro z hz0 hz1
      have hlower : ell ≤ generalLowerQuadratic (ν : ℝ) z :=
        generalLowerQuadratic_one_le hlargeR hz0 hz1
      have hMell : 0 < M * ell := mul_pos hM hell
      have hhalf : M * ell / 2 < M * ell := by linarith
      calc
        M * ell / (2 * H) * H = M * ell / 2 := by
          field_simp [ne_of_gt hH]
        _ < M * ell := hhalf
        _ ≤ M * generalLowerQuadratic (ν : ℝ) z :=
          mul_le_mul_of_nonneg_left hlower (le_of_lt hM)

end

end GraybillDeal
