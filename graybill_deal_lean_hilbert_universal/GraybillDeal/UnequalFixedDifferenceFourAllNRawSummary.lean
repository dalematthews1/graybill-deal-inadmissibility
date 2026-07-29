import GraybillDeal.UnequalFixedDifferenceFourAllNAlgebra
import GraybillDeal.GeneralGaussianMeanBridge
import GraybillDeal.GeneralSummaryIndependence
import GraybillDeal.UnequalBlocks
import GraybillDeal.UnequalSummaryTransform

/-!
# Raw canonical summaries for the fixed-difference-four family

This module assembles the probability-law side of the family

`(n₁,n₂) = (n,n+4)`, `n ≥ 13`.

Internally the sample index types are kept in residual-degrees-of-freedom
form.  Thus

* `ν₁ = n-1` and `X : Fin (ν₁+1) → Ω → ℝ`;
* `ν₂ = n+3` and `Y : Fin (ν₂+1) → Ω → ℝ`.

With `U₁ = RSS₁/v₁` and `U₂ = RSS₂/v₂`, the canonical summaries satisfy

* `P = U₁/(U₁+U₂) ~ Beta(m-1,m+1)`;
* `L = U₁+U₂ ~ Gamma(2m,1/2)`,
  where `m=(n+1)/2`;
* `V = D²/(v₁/n₁+v₂/n₂) ~ Gamma(1/2,1/2)`;
* `(centered,D,P,L)` are mutually independent.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Family indices and raw summaries -/

/-- Residual degrees of freedom of the smaller sample. -/
def unequalFixedDifferenceFourAllNResidualDF1 (n : ℕ) : ℕ :=
  n - 1

/-- Residual degrees of freedom of the larger sample. -/
def unequalFixedDifferenceFourAllNResidualDF2 (n : ℕ) : ℕ :=
  n + 3

/-- The residual-DF presentation of the first sample has exactly `n`
observations. -/
@[simp]
theorem unequalFixedDifferenceFourAllNResidualDF1_add_one
    {n : ℕ} (hn : 1 ≤ n) :
    unequalFixedDifferenceFourAllNResidualDF1 n + 1 = n := by
  unfold unequalFixedDifferenceFourAllNResidualDF1
  omega

/-- The residual-DF presentation of the second sample has exactly `n+4`
observations. -/
@[simp]
theorem unequalFixedDifferenceFourAllNResidualDF2_add_one
    (n : ℕ) :
    unequalFixedDifferenceFourAllNResidualDF2 n + 1 = n + 4 := by
  unfold unequalFixedDifferenceFourAllNResidualDF2
  omega

/-- Standardized first residual sum of squares. -/
def unequalFixedDifferenceFourAllNNormalRawU1
    (n : ℕ) (v₁ : NNReal)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ) :
    Ω → ℝ :=
  scaledResidualSumSquaresN
    (unequalFixedDifferenceFourAllNResidualDF1 n) (v₁ : ℝ) X

/-- Standardized second residual sum of squares. -/
def unequalFixedDifferenceFourAllNNormalRawU2
    (n : ℕ) (v₂ : NNReal)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ) :
    Ω → ℝ :=
  scaledResidualSumSquaresN
    (unequalFixedDifferenceFourAllNResidualDF2 n) (v₂ : ℝ) Y

/-- The asymmetric beta ratio coordinate. -/
def unequalFixedDifferenceFourAllNNormalRawP
    (n : ℕ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ) :
    Ω → ℝ :=
  fun ω =>
    unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
      / (unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
        + unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω)

/-- The common gamma sum coordinate. -/
def unequalFixedDifferenceFourAllNNormalRawL
    (n : ℕ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ) :
    Ω → ℝ :=
  fun ω =>
    unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
      + unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω

/-- Variance of the difference of the two sample means. -/
def unequalFixedDifferenceFourAllNNormalMeanVarianceSum
    (n : ℕ) (v₁ v₂ : NNReal) : ℝ :=
  (v₁ : ℝ) / (unequalFixedDifferenceFourAllNResidualDF1 n + 1)
    + (v₂ : ℝ) / (unequalFixedDifferenceFourAllNResidualDF2 n + 1)

/-- The standardized squared difference of the two sample means. -/
def unequalFixedDifferenceFourAllNNormalRawV
    (n : ℕ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ) :
    Ω → ℝ :=
  fun ω =>
    generalStandardizedDifference 0
      (unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂)
      (meanDifferenceU
        (unequalFixedDifferenceFourAllNResidualDF1 n)
        (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω)

/-- The centered known-variance oracle error for the family member `n`. -/
def unequalFixedDifferenceFourAllNOracleCenteredError
    (n : ℕ) (μ : ℝ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ) :
    Ω → ℝ :=
  oracleCenteredErrorU
    (unequalFixedDifferenceFourAllNResidualDF1 n)
    (unequalFixedDifferenceFourAllNResidualDF2 n) μ
    (oracleVarianceWeightU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
    X Y

/-! ## Measurability -/

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourAllNNormalRawU1
    {n : ℕ} {v₁ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    Measurable (unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X) :=
  measurable_scaledResidualSumSquaresN hX _

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourAllNNormalRawU2
    {n : ℕ} {v₂ : NNReal}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y) :=
  measurable_scaledResidualSumSquaresN hY _

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourAllNNormalRawP
    {n : ℕ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y) := by
  unfold unequalFixedDifferenceFourAllNNormalRawP
  fun_prop

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourAllNNormalRawL
    {n : ℕ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y) := by
  unfold unequalFixedDifferenceFourAllNNormalRawL
  fun_prop

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourAllNNormalRawV
    {n : ℕ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y) := by
  unfold unequalFixedDifferenceFourAllNNormalRawV
  fun_prop

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourAllNOracleCenteredError
    {n : ℕ} {μ : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable
      (unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y) := by
  unfold unequalFixedDifferenceFourAllNOracleCenteredError
  exact measurable_oracleCenteredErrorU hX hY _ _

/-! ## Packaged component laws -/

/-- All raw-summary laws and independence facts for family member `n`. -/
structure UnequalFixedDifferenceFourAllNRawNormalSummaryLaws
    (n : ℕ) (μ : ℝ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (Pmeasure : Measure Ω) : Prop where
  p_law :
    HasLaw (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
      (betaMeasure
        (unequalFixedDifferenceFourSampleM n - 1)
        (unequalFixedDifferenceFourSampleM n + 1)) Pmeasure
  l_law :
    HasLaw (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y)
      (gammaMeasure
        (2 * unequalFixedDifferenceFourSampleM n) (1 / 2)) Pmeasure
  v_law :
    HasLaw (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y)
      (gammaMeasure (1 / 2) (1 / 2)) Pmeasure
  p_l_indep :
    IndepFun (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
      (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y) Pmeasure
  p_lv_indep :
    IndepFun (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
      (fun ω =>
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω,
          unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y ω)) Pmeasure
  v_l_indep :
    IndepFun (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y)
      (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y) Pmeasure
  centered_d_indep :
    IndepFun
      (unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y)
      (meanDifferenceU
        (unequalFixedDifferenceFourAllNResidualDF1 n)
        (unequalFixedDifferenceFourAllNResidualDF2 n) X Y) Pmeasure
  centeredD_pL_indep :
    IndepFun
      (fun ω =>
        (unequalFixedDifferenceFourAllNOracleCenteredError
            n μ v₁ v₂ X Y ω,
          meanDifferenceU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω))
      (fun ω =>
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω,
          unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω))
      Pmeasure
  centered_d_p_l_indep :
    IndepFun
      (unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y)
      (fun ω =>
        (meanDifferenceU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω,
          (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω,
            unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω)))
      Pmeasure
  summary_iIndep :
    iIndepFun
      ![
        unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y,
        meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y,
        unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y,
        unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y]
      Pmeasure
  centered_sq :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourAllNOracleCenteredError
          n μ v₁ v₂ X Y ω ^ 2)
      Pmeasure
  centered_zero :
    (∫ ω,
      unequalFixedDifferenceFourAllNOracleCenteredError
        n μ v₁ v₂ X Y ω ∂Pmeasure) = 0

/-! ## Assembly from the raw normal model -/

/--
Assembly of all summary laws for the family member indexed by `n`, directly
from the two unequal raw normal samples.
-/
theorem unequalFixedDifferenceFourAllNRawNormalSummaryLaws_of_normal_samples
    {n : ℕ} (hn : 13 ≤ n)
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y Pmeasure μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    UnequalFixedDifferenceFourAllNRawNormalSummaryLaws
      n μ v₁ v₂ X Y Pmeasure := by
  letI : IsProbabilityMeasure Pmeasure :=
    h.indep.isProbabilityMeasure
  have hn1 : 1 ≤ n := by omega
  have hmR :
      7 ≤ unequalFixedDifferenceFourSampleM n :=
    unequalFixedDifferenceFourSampleM_ge_seven hn
  have hν₁ :
      0 < unequalFixedDifferenceFourAllNResidualDF1 n := by
    unfold unequalFixedDifferenceFourAllNResidualDF1
    omega
  have hν₂ :
      0 < unequalFixedDifferenceFourAllNResidualDF2 n := by
    unfold unequalFixedDifferenceFourAllNResidualDF2
    omega
  have hshape₁ :
      ((unequalFixedDifferenceFourAllNResidualDF1 n : ℕ) : ℝ) / 2
        = unequalFixedDifferenceFourSampleM n - 1 := by
    unfold unequalFixedDifferenceFourAllNResidualDF1
      unequalFixedDifferenceFourSampleM
    rw [Nat.cast_sub hn1]
    push_cast
    ring
  have hshape₂ :
      ((unequalFixedDifferenceFourAllNResidualDF2 n : ℕ) : ℝ) / 2
        = unequalFixedDifferenceFourSampleM n + 1 := by
    unfold unequalFixedDifferenceFourAllNResidualDF2
      unequalFixedDifferenceFourSampleM
    push_cast
    ring
  have hU₁ :
      HasLaw (unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X)
        (gammaMeasure
          (unequalFixedDifferenceFourSampleM n - 1) (1 / 2))
        Pmeasure := by
    simpa only [unequalFixedDifferenceFourAllNNormalRawU1, hshape₁] using
      h.hasLaw_scaledResidualSumSquaresX hν₁ hv₁
  have hU₂ :
      HasLaw (unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y)
        (gammaMeasure
          (unequalFixedDifferenceFourSampleM n + 1) (1 / 2))
        Pmeasure := by
    simpa only [unequalFixedDifferenceFourAllNNormalRawU2, hshape₂] using
      h.hasLaw_scaledResidualSumSquaresY hν₂ hv₂
  have hU₁U₂ :
      IndepFun
        (unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X)
        (unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y) Pmeasure := by
    simpa only [unequalFixedDifferenceFourAllNNormalRawU1,
      unequalFixedDifferenceFourAllNNormalRawU2] using
      h.indepFun_scaledResidualSumSquares
  have hvarianceSum :
      0 < unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂ := by
    unfold unequalFixedDifferenceFourAllNNormalMeanVarianceSum
    positivity
  have hvarianceSum_raw :
      0 <
        (v₁ : ℝ)
            / (unequalFixedDifferenceFourAllNResidualDF1 n + 1)
          + (v₂ : ℝ)
            / (unequalFixedDifferenceFourAllNResidualDF2 n + 1) := by
    simpa only [unequalFixedDifferenceFourAllNNormalMeanVarianceSum] using
      hvarianceSum
  have hCD :
      IndepFun
        (unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y)
        (meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
        Pmeasure := by
    simpa only [unequalFixedDifferenceFourAllNOracleCenteredError] using
      h.indepFun_oracleCenteredError_meanDifference hvarianceSum_raw
  have hcenteredD_U :
      IndepFun
        (fun ω =>
          (unequalFixedDifferenceFourAllNOracleCenteredError
              n μ v₁ v₂ X Y ω,
            meanDifferenceU
              (unequalFixedDifferenceFourAllNResidualDF1 n)
              (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω))
        (fun ω =>
          (unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω,
            unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω))
        Pmeasure := by
    have hout :=
      (h.indepFun_oracleCenteredError_meanDifference_residualSumSquaresPair
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)).comp
        measurable_id
        (show Measurable
            (fun z : ℝ × ℝ =>
              (z.1 / (v₁ : ℝ), z.2 / (v₂ : ℝ))) by
          fun_prop)
    apply hout.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl
  have hcenteredMeas :
      Measurable
        (unequalFixedDifferenceFourAllNOracleCenteredError
          n μ v₁ v₂ X Y) :=
    measurable_unequalFixedDifferenceFourAllNOracleCenteredError hX hY
  have hDmeas :
      Measurable
        (meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y) :=
    measurable_meanDifferenceU hX hY
  have hU₁meas :
      Measurable (unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X) :=
    measurable_unequalFixedDifferenceFourAllNNormalRawU1 hX
  have hU₂meas :
      Measurable (unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y) :=
    measurable_unequalFixedDifferenceFourAllNNormalRawU2 hY
  obtain ⟨hP, hL, hsummaryRaw⟩ :=
    betaGamma_laws_and_iIndepFun_unequalTransformedSummary4_of_blocks
      (a := unequalFixedDifferenceFourSampleM n - 1)
      (b := unequalFixedDifferenceFourSampleM n + 1) (r := 1 / 2)
      (by linarith) (by linarith) (by norm_num)
      (unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y)
      (meanDifferenceU
        (unequalFixedDifferenceFourAllNResidualDF1 n)
        (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
      (unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X)
      (unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y)
      Pmeasure hcenteredMeas hDmeas hU₁meas hU₂meas
      hU₁ hU₂ hCD hU₁U₂ hcenteredD_U
  have hsummary :
      iIndepFun
        ![
          unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y,
          meanDifferenceU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) X Y,
          unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y,
          unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y]
        Pmeasure := by
    apply hsummaryRaw.congr
    intro i
    fin_cases i <;>
      filter_upwards [] with ω <;>
        rfl
  have hDlaw :
      HasLaw
        (meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
        (gaussianReal 0
          (unequalFixedDifferenceFourAllNNormalMeanVarianceSum
            n v₁ v₂).toNNReal)
        Pmeasure := by
    convert h.hasLaw_meanDifference using 1
    congr 1
    apply NNReal.eq
    rw [Real.coe_toNNReal _ hvarianceSum.le]
    unfold unequalFixedDifferenceFourAllNNormalMeanVarianceSum
    push_cast
    rfl
  have hV :
      HasLaw
        (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y)
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
    unfold unequalFixedDifferenceFourAllNNormalRawV
    have hDlaw' :
        HasLaw
          (meanDifferenceU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
          (gaussianReal 0
            (unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂
              / (((0 : ℕ) : ℝ) + 1)).toNNReal)
          Pmeasure := by
      convert hDlaw using 1 <;> norm_num
    simpa only [Nat.cast_zero] using
      (hasLaw_generalStandardizedDifference_of_gaussian
        0 (unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂)
        (meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
        Pmeasure hvarianceSum hDlaw')
  have hPmeas :
      Measurable
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y) :=
    measurable_unequalFixedDifferenceFourAllNNormalRawP hX hY
  have hLmeas :
      Measurable
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y) :=
    measurable_unequalFixedDifferenceFourAllNNormalRawL hX hY
  have hPL :
      IndepFun
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y)
        Pmeasure := by
    simpa using
      hsummary.indepFun
        (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hP_LV :
      IndepFun
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
        (fun ω =>
          (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω,
            unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y ω))
        Pmeasure := by
    simpa only [unequalFixedDifferenceFourAllNNormalRawV] using
      indepFun_p_l_generalStandardizedDifference_of_iIndepFun_summary4
        0 (unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂)
        (unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y)
        (meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y)
        Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hVL :
      IndepFun
        (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y)
        Pmeasure := by
    change
      IndepFun
        (fun ω =>
          generalStandardizedDifference 0
            (unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂)
            (meanDifferenceU
              (unequalFixedDifferenceFourAllNResidualDF1 n)
              (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω))
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y)
        Pmeasure
    exact
      indepFun_generalStandardizedDifference_l_of_iIndepFun_summary4
        0 (unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂)
        (unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y)
        (meanDifferenceU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y)
        Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hcentered_nested :
      IndepFun
        (unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y)
        (fun ω =>
          (meanDifferenceU
              (unequalFixedDifferenceFourAllNResidualDF1 n)
              (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω,
            (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω,
              unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω)))
        Pmeasure :=
    indepFun_centered_d_p_l_of_iIndepFun_generalSummary4
      (unequalFixedDifferenceFourAllNOracleCenteredError n μ v₁ v₂ X Y)
      (meanDifferenceU
        (unequalFixedDifferenceFourAllNResidualDF1 n)
        (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
      (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y)
      (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y)
      Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hcentered_sq :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourAllNOracleCenteredError
            n μ v₁ v₂ X Y ω ^ 2)
        Pmeasure := by
    have hmeanX :
        MemLp
          (sampleMeanN
            (unequalFixedDifferenceFourAllNResidualDF1 n) X)
          2 Pmeasure :=
      h.hasGaussianLaw_sampleMeanX.memLp_two
    have hmeanY :
        MemLp
          (sampleMeanN
            (unequalFixedDifferenceFourAllNResidualDF2 n) Y)
          2 Pmeasure :=
      h.hasGaussianLaw_sampleMeanY.memLp_two
    have hC2 :
        MemLp
          (unequalFixedDifferenceFourAllNOracleCenteredError
            n μ v₁ v₂ X Y)
          2 Pmeasure := by
      have hraw :=
        (hmeanX.add
          ((hmeanY.sub hmeanX).const_mul
            (oracleVarianceWeightU
              (unequalFixedDifferenceFourAllNResidualDF1 n)
              (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂))).sub
          (memLp_const (μ := Pmeasure) μ)
      apply hraw.ae_eq
      filter_upwards [] with ω
      rfl
    exact (memLp_two_iff_integrable_sq hC2.1).1 hC2
  have hcentered_zero :
      (∫ ω,
        unequalFixedDifferenceFourAllNOracleCenteredError
          n μ v₁ v₂ X Y ω ∂Pmeasure) = 0 := by
    have hXint :
        Integrable
          (sampleMeanN
            (unequalFixedDifferenceFourAllNResidualDF1 n) X)
          Pmeasure :=
      h.hasGaussianLaw_sampleMeanX.integrable
    have hYint :
        Integrable
          (sampleMeanN
            (unequalFixedDifferenceFourAllNResidualDF2 n) Y)
          Pmeasure :=
      h.hasGaussianLaw_sampleMeanY.integrable
    have hDint :
        Integrable
          (meanDifferenceU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) X Y)
          Pmeasure := by
      unfold meanDifferenceU
      exact hYint.sub hXint
    unfold unequalFixedDifferenceFourAllNOracleCenteredError
      oracleCenteredErrorU
    change
      (∫ ω,
        (sampleMeanN
            (unequalFixedDifferenceFourAllNResidualDF1 n) X
          + fun ω =>
            oracleVarianceWeightU
                (unequalFixedDifferenceFourAllNResidualDF1 n)
                (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂
              * meanDifferenceU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω) ω
          - (fun _ : Ω => μ) ω ∂Pmeasure) = 0
    rw [integral_sub
      (hXint.add
        (hDint.const_mul
          (oracleVarianceWeightU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)))
      (integrable_const μ)]
    change
      (∫ a,
        sampleMeanN
            (unequalFixedDifferenceFourAllNResidualDF1 n) X a
          + oracleVarianceWeightU
              (unequalFixedDifferenceFourAllNResidualDF1 n)
              (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂
              * meanDifferenceU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) X Y a
          ∂Pmeasure)
        - (∫ _ : Ω, μ ∂Pmeasure) = 0
    rw [integral_add hXint
      (hDint.const_mul
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)),
      integral_const_mul, h.integral_meanDifference,
      h.integral_sampleMeanX]
    simp
  refine
    { p_law := ?_
      l_law := ?_
      v_law := hV
      p_l_indep := hPL
      p_lv_indep := hP_LV
      v_l_indep := hVL
      centered_d_indep := hCD
      centeredD_pL_indep := ?_
      centered_d_p_l_indep := hcentered_nested
      summary_iIndep := hsummary
      centered_sq := hcentered_sq
      centered_zero := hcentered_zero }
  · change
      HasLaw
        (fun ω =>
          unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
            / (unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
              + unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω))
        (betaMeasure
          (unequalFixedDifferenceFourSampleM n - 1)
          (unequalFixedDifferenceFourSampleM n + 1))
        Pmeasure
    exact hP
  · change
      HasLaw
        (fun ω =>
          unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
            + unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω)
        (gammaMeasure
          (2 * unequalFixedDifferenceFourSampleM n) (1 / 2))
        Pmeasure
    convert hL using 1 <;> ring
  · have hout :=
      hcenteredD_U.comp measurable_id measurable_betaGammaRatioSum
    apply hout.congr
    · filter_upwards [] with ω
      rfl
    · filter_upwards [] with ω
      rfl

end

end GraybillDeal
