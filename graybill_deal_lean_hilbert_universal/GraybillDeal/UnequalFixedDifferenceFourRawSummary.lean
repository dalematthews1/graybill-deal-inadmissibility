import GraybillDeal.GeneralGaussianMeanBridge
import GraybillDeal.GeneralSummaryIndependence
import GraybillDeal.UnequalBlocks
import GraybillDeal.UnequalSummaryTransform

/-!
# Raw canonical summaries for the fixed-difference-four family

This module assembles the probability-law side of the family

`(n₁,n₂) = (2m-1,2m+3)`, `m ≥ 7`.

Internally the sample index types are kept in residual-degrees-of-freedom
form.  Thus

* `ν₁ = 2(m-1)` and `X : Fin (ν₁+1) → Ω → ℝ`;
* `ν₂ = 2(m+1)` and `Y : Fin (ν₂+1) → Ω → ℝ`.

With `U₁ = RSS₁/v₁` and `U₂ = RSS₂/v₂`, the canonical summaries satisfy

* `P = U₁/(U₁+U₂) ~ Beta(m-1,m+1)`;
* `L = U₁+U₂ ~ Gamma(2m,1/2)`;
* `V = D²/(v₁/n₁+v₂/n₂) ~ Gamma(1/2,1/2)`;
* `(centered,D,P,L)` are mutually independent.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Family indices and raw summaries -/

/-- Residual degrees of freedom of the smaller sample. -/
def unequalFixedDifferenceFourResidualDF1 (m : ℕ) : ℕ :=
  2 * (m - 1)

/-- Residual degrees of freedom of the larger sample. -/
def unequalFixedDifferenceFourResidualDF2 (m : ℕ) : ℕ :=
  2 * (m + 1)

/-- Standardized first residual sum of squares. -/
def unequalFixedDifferenceFourNormalRawU1
    (m : ℕ) (v₁ : NNReal)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ) :
    Ω → ℝ :=
  scaledResidualSumSquaresN
    (unequalFixedDifferenceFourResidualDF1 m) (v₁ : ℝ) X

/-- Standardized second residual sum of squares. -/
def unequalFixedDifferenceFourNormalRawU2
    (m : ℕ) (v₂ : NNReal)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ) :
    Ω → ℝ :=
  scaledResidualSumSquaresN
    (unequalFixedDifferenceFourResidualDF2 m) (v₂ : ℝ) Y

/-- The asymmetric beta ratio coordinate. -/
def unequalFixedDifferenceFourNormalRawP
    (m : ℕ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ) :
    Ω → ℝ :=
  fun ω =>
    unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
      / (unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
        + unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω)

/-- The common gamma sum coordinate. -/
def unequalFixedDifferenceFourNormalRawL
    (m : ℕ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ) :
    Ω → ℝ :=
  fun ω =>
    unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
      + unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω

/-- Variance of the difference of the two sample means. -/
def unequalFixedDifferenceFourNormalMeanVarianceSum
    (m : ℕ) (v₁ v₂ : NNReal) : ℝ :=
  (v₁ : ℝ) / (unequalFixedDifferenceFourResidualDF1 m + 1)
    + (v₂ : ℝ) / (unequalFixedDifferenceFourResidualDF2 m + 1)

/-- The standardized squared difference of the two sample means. -/
def unequalFixedDifferenceFourNormalRawV
    (m : ℕ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ) :
    Ω → ℝ :=
  fun ω =>
    generalStandardizedDifference 0
      (unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂)
      (meanDifferenceU
        (unequalFixedDifferenceFourResidualDF1 m)
        (unequalFixedDifferenceFourResidualDF2 m) X Y ω)

/-- The centered known-variance oracle error for the family member `m`. -/
def unequalFixedDifferenceFourOracleCenteredError
    (m : ℕ) (μ : ℝ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ) :
    Ω → ℝ :=
  oracleCenteredErrorU
    (unequalFixedDifferenceFourResidualDF1 m)
    (unequalFixedDifferenceFourResidualDF2 m) μ
    (oracleVarianceWeightU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
    X Y

/-! ## Measurability -/

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourNormalRawU1
    {m : ℕ} {v₁ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    Measurable (unequalFixedDifferenceFourNormalRawU1 m v₁ X) :=
  measurable_scaledResidualSumSquaresN hX _

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourNormalRawU2
    {m : ℕ} {v₂ : NNReal}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (unequalFixedDifferenceFourNormalRawU2 m v₂ Y) :=
  measurable_scaledResidualSumSquaresN hY _

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourNormalRawP
    {m : ℕ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y) := by
  unfold unequalFixedDifferenceFourNormalRawP
  fun_prop

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourNormalRawL
    {m : ℕ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y) := by
  unfold unequalFixedDifferenceFourNormalRawL
  fun_prop

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourNormalRawV
    {m : ℕ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y) := by
  unfold unequalFixedDifferenceFourNormalRawV
  fun_prop

@[fun_prop]
theorem measurable_unequalFixedDifferenceFourOracleCenteredError
    {m : ℕ} {μ : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) :
    Measurable
      (unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y) := by
  unfold unequalFixedDifferenceFourOracleCenteredError
  exact measurable_oracleCenteredErrorU hX hY _ _

/-! ## Packaged component laws -/

/-- All raw-summary laws and independence facts for family member `m`. -/
structure UnequalFixedDifferenceFourRawNormalSummaryLaws
    (m : ℕ) (μ : ℝ) (v₁ v₂ : NNReal)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (Pmeasure : Measure Ω) : Prop where
  p_law :
    HasLaw (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
      (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1)) Pmeasure
  l_law :
    HasLaw (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y)
      (gammaMeasure (2 * (m : ℝ)) (1 / 2)) Pmeasure
  v_law :
    HasLaw (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y)
      (gammaMeasure (1 / 2) (1 / 2)) Pmeasure
  p_l_indep :
    IndepFun (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
      (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y) Pmeasure
  p_lv_indep :
    IndepFun (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
      (fun ω =>
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω,
          unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y ω)) Pmeasure
  v_l_indep :
    IndepFun (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y)
      (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y) Pmeasure
  centered_d_indep :
    IndepFun
      (unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y)
      (meanDifferenceU
        (unequalFixedDifferenceFourResidualDF1 m)
        (unequalFixedDifferenceFourResidualDF2 m) X Y) Pmeasure
  centeredD_pL_indep :
    IndepFun
      (fun ω =>
        (unequalFixedDifferenceFourOracleCenteredError
            m μ v₁ v₂ X Y ω,
          meanDifferenceU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) X Y ω))
      (fun ω =>
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω,
          unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω))
      Pmeasure
  centered_d_p_l_indep :
    IndepFun
      (unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y)
      (fun ω =>
        (meanDifferenceU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) X Y ω,
          (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω,
            unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω)))
      Pmeasure
  summary_iIndep :
    iIndepFun
      ![
        unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y,
        meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y,
        unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y,
        unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y]
      Pmeasure
  centered_sq :
    Integrable
      (fun ω =>
        unequalFixedDifferenceFourOracleCenteredError
          m μ v₁ v₂ X Y ω ^ 2)
      Pmeasure
  centered_zero :
    (∫ ω,
      unequalFixedDifferenceFourOracleCenteredError
        m μ v₁ v₂ X Y ω ∂Pmeasure) = 0

/-! ## Assembly from the raw normal model -/

/--
Assembly of all summary laws for the family member indexed by `m`, directly
from the two unequal raw normal samples.
-/
theorem unequalFixedDifferenceFourRawNormalSummaryLaws_of_normal_samples
    {m : ℕ} (hm : 7 ≤ m)
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {Pmeasure : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y Pmeasure μ v₁ v₂)
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i))
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    UnequalFixedDifferenceFourRawNormalSummaryLaws
      m μ v₁ v₂ X Y Pmeasure := by
  letI : IsProbabilityMeasure Pmeasure :=
    h.indep.isProbabilityMeasure
  have hm1 : 1 ≤ m := by omega
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hν₁ :
      0 < unequalFixedDifferenceFourResidualDF1 m := by
    unfold unequalFixedDifferenceFourResidualDF1
    omega
  have hν₂ :
      0 < unequalFixedDifferenceFourResidualDF2 m := by
    unfold unequalFixedDifferenceFourResidualDF2
    omega
  have hshape₁ :
      ((unequalFixedDifferenceFourResidualDF1 m : ℕ) : ℝ) / 2
        = (m : ℝ) - 1 := by
    unfold unequalFixedDifferenceFourResidualDF1
    rw [Nat.cast_mul, Nat.cast_sub hm1]
    push_cast
    ring
  have hshape₂ :
      ((unequalFixedDifferenceFourResidualDF2 m : ℕ) : ℝ) / 2
        = (m : ℝ) + 1 := by
    unfold unequalFixedDifferenceFourResidualDF2
    push_cast
    ring
  have hU₁ :
      HasLaw (unequalFixedDifferenceFourNormalRawU1 m v₁ X)
        (gammaMeasure ((m : ℝ) - 1) (1 / 2)) Pmeasure := by
    simpa only [unequalFixedDifferenceFourNormalRawU1, hshape₁] using
      h.hasLaw_scaledResidualSumSquaresX hν₁ hv₁
  have hU₂ :
      HasLaw (unequalFixedDifferenceFourNormalRawU2 m v₂ Y)
        (gammaMeasure ((m : ℝ) + 1) (1 / 2)) Pmeasure := by
    simpa only [unequalFixedDifferenceFourNormalRawU2, hshape₂] using
      h.hasLaw_scaledResidualSumSquaresY hν₂ hv₂
  have hU₁U₂ :
      IndepFun
        (unequalFixedDifferenceFourNormalRawU1 m v₁ X)
        (unequalFixedDifferenceFourNormalRawU2 m v₂ Y) Pmeasure := by
    simpa only [unequalFixedDifferenceFourNormalRawU1,
      unequalFixedDifferenceFourNormalRawU2] using
      h.indepFun_scaledResidualSumSquares
  have hvarianceSum :
      0 < unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂ := by
    unfold unequalFixedDifferenceFourNormalMeanVarianceSum
    positivity
  have hvarianceSum_raw :
      0 <
        (v₁ : ℝ)
            / (unequalFixedDifferenceFourResidualDF1 m + 1)
          + (v₂ : ℝ)
            / (unequalFixedDifferenceFourResidualDF2 m + 1) := by
    simpa only [unequalFixedDifferenceFourNormalMeanVarianceSum] using
      hvarianceSum
  have hCD :
      IndepFun
        (unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y)
        (meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y)
        Pmeasure := by
    simpa only [unequalFixedDifferenceFourOracleCenteredError] using
      h.indepFun_oracleCenteredError_meanDifference hvarianceSum_raw
  have hcenteredD_U :
      IndepFun
        (fun ω =>
          (unequalFixedDifferenceFourOracleCenteredError
              m μ v₁ v₂ X Y ω,
            meanDifferenceU
              (unequalFixedDifferenceFourResidualDF1 m)
              (unequalFixedDifferenceFourResidualDF2 m) X Y ω))
        (fun ω =>
          (unequalFixedDifferenceFourNormalRawU1 m v₁ X ω,
            unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω))
        Pmeasure := by
    have hout :=
      (h.indepFun_oracleCenteredError_meanDifference_residualSumSquaresPair
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)).comp
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
        (unequalFixedDifferenceFourOracleCenteredError
          m μ v₁ v₂ X Y) :=
    measurable_unequalFixedDifferenceFourOracleCenteredError hX hY
  have hDmeas :
      Measurable
        (meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y) :=
    measurable_meanDifferenceU hX hY
  have hU₁meas :
      Measurable (unequalFixedDifferenceFourNormalRawU1 m v₁ X) :=
    measurable_unequalFixedDifferenceFourNormalRawU1 hX
  have hU₂meas :
      Measurable (unequalFixedDifferenceFourNormalRawU2 m v₂ Y) :=
    measurable_unequalFixedDifferenceFourNormalRawU2 hY
  obtain ⟨hP, hL, hsummaryRaw⟩ :=
    betaGamma_laws_and_iIndepFun_unequalTransformedSummary4_of_blocks
      (a := (m : ℝ) - 1) (b := (m : ℝ) + 1) (r := 1 / 2)
      (by linarith) (by linarith) (by norm_num)
      (unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y)
      (meanDifferenceU
        (unequalFixedDifferenceFourResidualDF1 m)
        (unequalFixedDifferenceFourResidualDF2 m) X Y)
      (unequalFixedDifferenceFourNormalRawU1 m v₁ X)
      (unequalFixedDifferenceFourNormalRawU2 m v₂ Y)
      Pmeasure hcenteredMeas hDmeas hU₁meas hU₂meas
      hU₁ hU₂ hCD hU₁U₂ hcenteredD_U
  have hsummary :
      iIndepFun
        ![
          unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y,
          meanDifferenceU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) X Y,
          unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y,
          unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y]
        Pmeasure := by
    apply hsummaryRaw.congr
    intro i
    fin_cases i <;>
      filter_upwards [] with ω <;>
        rfl
  have hDlaw :
      HasLaw
        (meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y)
        (gaussianReal 0
          (unequalFixedDifferenceFourNormalMeanVarianceSum
            m v₁ v₂).toNNReal)
        Pmeasure := by
    convert h.hasLaw_meanDifference using 1
    congr 1
    apply NNReal.eq
    rw [Real.coe_toNNReal _ hvarianceSum.le]
    unfold unequalFixedDifferenceFourNormalMeanVarianceSum
    push_cast
    rfl
  have hV :
      HasLaw
        (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y)
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure := by
    unfold unequalFixedDifferenceFourNormalRawV
    have hDlaw' :
        HasLaw
          (meanDifferenceU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) X Y)
          (gaussianReal 0
            (unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂
              / (((0 : ℕ) : ℝ) + 1)).toNNReal)
          Pmeasure := by
      convert hDlaw using 1 <;> norm_num
    simpa only [Nat.cast_zero] using
      (hasLaw_generalStandardizedDifference_of_gaussian
        0 (unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂)
        (meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y)
        Pmeasure hvarianceSum hDlaw')
  have hPmeas :
      Measurable
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y) :=
    measurable_unequalFixedDifferenceFourNormalRawP hX hY
  have hLmeas :
      Measurable
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y) :=
    measurable_unequalFixedDifferenceFourNormalRawL hX hY
  have hPL :
      IndepFun
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y)
        Pmeasure := by
    simpa using
      hsummary.indepFun
        (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hP_LV :
      IndepFun
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
        (fun ω =>
          (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω,
            unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y ω))
        Pmeasure := by
    simpa only [unequalFixedDifferenceFourNormalRawV] using
      indepFun_p_l_generalStandardizedDifference_of_iIndepFun_summary4
        0 (unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂)
        (unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y)
        (meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y)
        Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hVL :
      IndepFun
        (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y)
        Pmeasure := by
    change
      IndepFun
        (fun ω =>
          generalStandardizedDifference 0
            (unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂)
            (meanDifferenceU
              (unequalFixedDifferenceFourResidualDF1 m)
              (unequalFixedDifferenceFourResidualDF2 m) X Y ω))
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y)
        Pmeasure
    exact
      indepFun_generalStandardizedDifference_l_of_iIndepFun_summary4
        0 (unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂)
        (unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y)
        (meanDifferenceU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) X Y)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y)
        Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hcentered_nested :
      IndepFun
        (unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y)
        (fun ω =>
          (meanDifferenceU
              (unequalFixedDifferenceFourResidualDF1 m)
              (unequalFixedDifferenceFourResidualDF2 m) X Y ω,
            (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω,
              unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω)))
        Pmeasure :=
    indepFun_centered_d_p_l_of_iIndepFun_generalSummary4
      (unequalFixedDifferenceFourOracleCenteredError m μ v₁ v₂ X Y)
      (meanDifferenceU
        (unequalFixedDifferenceFourResidualDF1 m)
        (unequalFixedDifferenceFourResidualDF2 m) X Y)
      (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y)
      (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y)
      Pmeasure hcenteredMeas hDmeas hPmeas hLmeas hsummary
  have hcentered_sq :
      Integrable
        (fun ω =>
          unequalFixedDifferenceFourOracleCenteredError
            m μ v₁ v₂ X Y ω ^ 2)
        Pmeasure := by
    have hmeanX :
        MemLp
          (sampleMeanN
            (unequalFixedDifferenceFourResidualDF1 m) X)
          2 Pmeasure :=
      h.hasGaussianLaw_sampleMeanX.memLp_two
    have hmeanY :
        MemLp
          (sampleMeanN
            (unequalFixedDifferenceFourResidualDF2 m) Y)
          2 Pmeasure :=
      h.hasGaussianLaw_sampleMeanY.memLp_two
    have hC2 :
        MemLp
          (unequalFixedDifferenceFourOracleCenteredError
            m μ v₁ v₂ X Y)
          2 Pmeasure := by
      have hraw :=
        (hmeanX.add
          ((hmeanY.sub hmeanX).const_mul
            (oracleVarianceWeightU
              (unequalFixedDifferenceFourResidualDF1 m)
              (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂))).sub
          (memLp_const (μ := Pmeasure) μ)
      apply hraw.ae_eq
      filter_upwards [] with ω
      rfl
    exact (memLp_two_iff_integrable_sq hC2.1).1 hC2
  have hcentered_zero :
      (∫ ω,
        unequalFixedDifferenceFourOracleCenteredError
          m μ v₁ v₂ X Y ω ∂Pmeasure) = 0 := by
    have hXint :
        Integrable
          (sampleMeanN
            (unequalFixedDifferenceFourResidualDF1 m) X)
          Pmeasure :=
      h.hasGaussianLaw_sampleMeanX.integrable
    have hYint :
        Integrable
          (sampleMeanN
            (unequalFixedDifferenceFourResidualDF2 m) Y)
          Pmeasure :=
      h.hasGaussianLaw_sampleMeanY.integrable
    have hDint :
        Integrable
          (meanDifferenceU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) X Y)
          Pmeasure := by
      unfold meanDifferenceU
      exact hYint.sub hXint
    unfold unequalFixedDifferenceFourOracleCenteredError
      oracleCenteredErrorU
    change
      (∫ ω,
        (sampleMeanN
            (unequalFixedDifferenceFourResidualDF1 m) X
          + fun ω =>
            oracleVarianceWeightU
                (unequalFixedDifferenceFourResidualDF1 m)
                (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂
              * meanDifferenceU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) X Y ω) ω
          - (fun _ : Ω => μ) ω ∂Pmeasure) = 0
    rw [integral_sub
      (hXint.add
        (hDint.const_mul
          (oracleVarianceWeightU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)))
      (integrable_const μ)]
    change
      (∫ a,
        sampleMeanN
            (unequalFixedDifferenceFourResidualDF1 m) X a
          + oracleVarianceWeightU
              (unequalFixedDifferenceFourResidualDF1 m)
              (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂
              * meanDifferenceU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) X Y a
          ∂Pmeasure)
        - (∫ _ : Ω, μ ∂Pmeasure) = 0
    rw [integral_add hXint
      (hDint.const_mul
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)),
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
          unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
            / (unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
              + unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω))
        (betaMeasure ((m : ℝ) - 1) ((m : ℝ) + 1))
        Pmeasure
    exact hP
  · change
      HasLaw
        (fun ω =>
          unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
            + unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω)
        (gammaMeasure (2 * (m : ℝ)) (1 / 2))
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
