import GraybillDeal.UnequalFixedDifferenceFourRealCanonical
import GraybillDeal.UnequalFixedDifferenceFourAllNRawSummary
import GraybillDeal.UnequalFixedDifferenceFourAllNRawEstimator
import GraybillDeal.UnequalFixedDifferenceFourAllNRawPositivity

/-!
# Raw/canonical coordinate identities for the fixed-difference-four family

For sample sizes `(n₁,n₂)=(n,n+4)`, `n ≥ 13`, this module identifies the
real-parameter canonical coordinates at `mₙ=(n+1)/2` with the literal
Graybill--Deal quantities.  The key normalization is

`A₁+A₂ = λ L D_{mₙ}(θ,P)/(4mₙ)`,

where `Aᵢ` are the two estimated sample-mean variances, `λ` is the true
variance of the sample-mean difference, and `(P,L)` are the beta--gamma
residual coordinates.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem unequalFD4AllNRawCoordinates_cast_df_one
    {n : ℕ} (hn : 13 ≤ n) :
    (unequalFixedDifferenceFourAllNResidualDF1 n : ℝ)
      = 2 * (unequalFixedDifferenceFourSampleM n - 1) := by
  have hn1 : 1 ≤ n := by omega
  unfold unequalFixedDifferenceFourAllNResidualDF1
    unequalFixedDifferenceFourSampleM
  rw [Nat.cast_sub hn1]
  push_cast
  ring

private theorem unequalFD4AllNRawCoordinates_cast_df_two
    (n : ℕ) :
    (unequalFixedDifferenceFourAllNResidualDF2 n : ℝ)
      = 2 * (unequalFixedDifferenceFourSampleM n + 1) := by
  unfold unequalFixedDifferenceFourAllNResidualDF2
    unequalFixedDifferenceFourSampleM
  push_cast
  ring

private theorem unequalFD4AllNRawCoordinates_cast_df_one_ne
    {n : ℕ} (hn : 13 ≤ n) :
    (unequalFixedDifferenceFourAllNResidualDF1 n : ℝ) ≠ 0 := by
  rw [unequalFD4AllNRawCoordinates_cast_df_one hn]
  have hmR :
      (7 : ℝ) ≤ unequalFixedDifferenceFourSampleM n :=
    unequalFixedDifferenceFourSampleM_ge_seven hn
  apply ne_of_gt
  nlinarith

private theorem unequalFD4AllNRawCoordinates_cast_df_two_ne
    (n : ℕ) :
    (unequalFixedDifferenceFourAllNResidualDF2 n : ℝ) ≠ 0 := by
  exact_mod_cast
    (show unequalFixedDifferenceFourAllNResidualDF2 n ≠ 0 by
      unfold unequalFixedDifferenceFourAllNResidualDF2
      omega)

private theorem unequalFD4AllNRawCoordinates_denom_ratio_sum
    {n : ℕ} (hn : 13 ≤ n)
    {τ₁ τ₂ u₁ u₂ : ℝ}
    (hτ : τ₁ + τ₂ ≠ 0) (hu : u₁ + u₂ ≠ 0) :
    (τ₁ + τ₂) * (u₁ + u₂)
          * unequalFixedDifferenceFourRealCanonicalDenom (unequalFixedDifferenceFourSampleM n)
              (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        / (4 * unequalFixedDifferenceFourSampleM n)
      =
    τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
      + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1)) := by
  have hmR :
      (7 : ℝ) ≤ unequalFixedDifferenceFourSampleM n :=
    unequalFixedDifferenceFourSampleM_ge_seven hn
  have hm0 : unequalFixedDifferenceFourSampleM n ≠ 0 := by
    linarith
  have hm1 : unequalFixedDifferenceFourSampleM n - 1 ≠ 0 := by
    linarith
  have hp1 : unequalFixedDifferenceFourSampleM n + 1 ≠ 0 := by
    linarith
  unfold unequalFixedDifferenceFourRealCanonicalDenom
    unequalFixedDifferenceFourRealT unequalFixedDifferenceFourRealQ
  field_simp [hτ, hu, hm0, hm1, hp1]
  ring

private theorem unequalFD4AllNRawCoordinates_R_ratio_sum
    {n : ℕ} (hn : 13 ≤ n)
    {τ₁ τ₂ u₁ u₂ : ℝ}
    (hτ : τ₁ + τ₂ ≠ 0) (hu : u₁ + u₂ ≠ 0)
    (hA :
      τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
          + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1))
        ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalR (unequalFixedDifferenceFourSampleM n)
        (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
      =
    (τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1)))
      /
    (τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
      + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1))) := by
  have hmR :
      (7 : ℝ) ≤ unequalFixedDifferenceFourSampleM n :=
    unequalFixedDifferenceFourSampleM_ge_seven hn
  have hm0 : unequalFixedDifferenceFourSampleM n ≠ 0 := by
    linarith
  have hm1 : unequalFixedDifferenceFourSampleM n - 1 ≠ 0 := by
    linarith
  have hden :
      unequalFixedDifferenceFourRealCanonicalDenom (unequalFixedDifferenceFourSampleM n)
          (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        ≠ 0 := by
    intro hzero
    have hid :=
      unequalFD4AllNRawCoordinates_denom_ratio_sum hn hτ hu
    rw [hzero] at hid
    simp only [mul_zero, zero_div] at hid
    exact hA hid.symm
  unfold unequalFixedDifferenceFourRealCanonicalR
  apply (div_eq_div_iff hden hA).2
  rw [← unequalFD4AllNRawCoordinates_denom_ratio_sum hn hτ hu]
  unfold unequalFixedDifferenceFourRealT
  field_simp [hτ, hu, hm0, hm1]
  ring

private theorem unequalFD4AllNRawCoordinates_Q_ratio_sum
    {n : ℕ} (hn : 13 ≤ n)
    {τ₁ τ₂ u₁ u₂ d : ℝ}
    (hτ : τ₁ + τ₂ ≠ 0) (hu : u₁ + u₂ ≠ 0)
    (hA :
      τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
          + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1))
        ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalQ (unequalFixedDifferenceFourSampleM n)
        (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        (u₁ + u₂) (d ^ 2 / (τ₁ + τ₂))
      =
    d ^ 2
      /
    (τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
      + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1))) := by
  have hmR :
      (7 : ℝ) ≤ unequalFixedDifferenceFourSampleM n :=
    unequalFixedDifferenceFourSampleM_ge_seven hn
  have hm0 : unequalFixedDifferenceFourSampleM n ≠ 0 := by
    linarith
  have hden :
      unequalFixedDifferenceFourRealCanonicalDenom (unequalFixedDifferenceFourSampleM n)
          (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        ≠ 0 := by
    intro hzero
    have hid :=
      unequalFD4AllNRawCoordinates_denom_ratio_sum hn hτ hu
    rw [hzero] at hid
    simp only [mul_zero, zero_div] at hid
    exact hA hid.symm
  have hUden :
      (u₁ + u₂)
          * unequalFixedDifferenceFourRealCanonicalDenom (unequalFixedDifferenceFourSampleM n)
              (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        ≠ 0 :=
    mul_ne_zero hu hden
  unfold unequalFixedDifferenceFourRealCanonicalQ
  apply (div_eq_div_iff hUden hA).2
  rw [← unequalFD4AllNRawCoordinates_denom_ratio_sum hn hτ hu]
  field_simp [hτ, hu, hm0]

/-! ## Elementary raw-summary identities -/

/-- The family oracle weight is the ratio of the two true mean variances. -/
theorem unequalFixedDifferenceFourAllNOracleVarianceWeight_eq
    (n : ℕ) (v₁ v₂ : NNReal) :
    oracleVarianceWeightU
        (unequalFixedDifferenceFourAllNResidualDF1 n)
        (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂
      =
    ((v₁ : ℝ) / (unequalFixedDifferenceFourAllNResidualDF1 n + 1))
      / unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂ := by
  rfl

/-- The first standardized residual coordinate is `ν₁ S₁²/v₁`. -/
theorem unequalFixedDifferenceFourAllNNormalRawU1_eq_sampleVariance
    {n : ℕ} (hn : 13 ≤ n)
    (v₁ : NNReal)
    (X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ)
    (ω : Ω) :
    unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
      =
    (unequalFixedDifferenceFourAllNResidualDF1 n : ℝ)
      * sampleVarianceN
          (unequalFixedDifferenceFourAllNResidualDF1 n) X ω
      / (v₁ : ℝ) := by
  have hν :
      0 < unequalFixedDifferenceFourAllNResidualDF1 n := by
    unfold unequalFixedDifferenceFourAllNResidualDF1
    omega
  unfold unequalFixedDifferenceFourAllNNormalRawU1
    scaledResidualSumSquaresN
  rw [← residualDF_mul_sampleVarianceN hν X ω]

/-- The second standardized residual coordinate is `ν₂ S₂²/v₂`. -/
theorem unequalFixedDifferenceFourAllNNormalRawU2_eq_sampleVariance
    {n : ℕ} (hn : 13 ≤ n)
    (v₂ : NNReal)
    (Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ)
    (ω : Ω) :
    unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω
      =
    (unequalFixedDifferenceFourAllNResidualDF2 n : ℝ)
      * sampleVarianceN
          (unequalFixedDifferenceFourAllNResidualDF2 n) Y ω
      / (v₂ : ℝ) := by
  have hν :
      0 < unequalFixedDifferenceFourAllNResidualDF2 n := by
    unfold unequalFixedDifferenceFourAllNResidualDF2
    omega
  unfold unequalFixedDifferenceFourAllNNormalRawU2
    scaledResidualSumSquaresN
  rw [← residualDF_mul_sampleVarianceN hν Y ω]

/-! ## Pointwise canonical/raw coordinate transport -/

/--
The family canonical denominator reconstructs the sum of the two estimated
sample-mean variances.
-/
theorem unequalFixedDifferenceFourAllNRawMeanVarianceSum_eq_canonical
    {n : ℕ} (hn : 13 ≤ n)
    {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω ≠ 0) :
    unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω
      =
    unequalFixedDifferenceFourAllNNormalMeanVarianceSum n v₁ v₂
      * unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω
      * unequalFixedDifferenceFourRealCanonicalDenom (unequalFixedDifferenceFourSampleM n)
          (oracleVarianceWeightU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
          (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω)
      / (4 * unequalFixedDifferenceFourSampleM n) := by
  let τ₁ : ℝ :=
    (v₁ : ℝ) / (unequalFixedDifferenceFourAllNResidualDF1 n + 1)
  let τ₂ : ℝ :=
    (v₂ : ℝ) / (unequalFixedDifferenceFourAllNResidualDF2 n + 1)
  let u₁ : ℝ :=
    unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
  let u₂ : ℝ :=
    unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω
  have hτ : τ₁ + τ₂ ≠ 0 := by
    apply ne_of_gt
    dsimp only [τ₁, τ₂]
    positivity
  have hu : u₁ + u₂ ≠ 0 := by
    simpa [u₁, u₂, unequalFixedDifferenceFourAllNNormalRawL] using hL
  have hid :=
    unequalFD4AllNRawCoordinates_denom_ratio_sum hn hτ hu
  have hdf₁ :=
    unequalFD4AllNRawCoordinates_cast_df_one hn
  have hdf₂ :=
    unequalFD4AllNRawCoordinates_cast_df_two n
  have hdf₁ne :=
    unequalFD4AllNRawCoordinates_cast_df_one_ne hn
  have hdf₂ne :=
    unequalFD4AllNRawCoordinates_cast_df_two_ne n
  have hright :
      τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
          + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1))
        =
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω := by
    dsimp only [τ₁, τ₂, u₁, u₂]
    rw [← hdf₁, ← hdf₂,
      unequalFixedDifferenceFourAllNNormalRawU1_eq_sampleVariance
        hn v₁ X ω,
      unequalFixedDifferenceFourAllNNormalRawU2_eq_sampleVariance
        hn v₂ Y ω]
    unfold unequalFixedDifferenceFourAllNRawMeanVarianceSum
      unequalFixedDifferenceFourAllNRawMeanVariance1
      unequalFixedDifferenceFourAllNRawMeanVariance2
    field_simp [hv₁.ne', hv₂.ne', hdf₁ne, hdf₂ne]
  rw [hright] at hid
  symm
  simpa [τ₁, τ₂, u₁, u₂,
    unequalFixedDifferenceFourAllNNormalMeanVarianceSum,
    unequalFixedDifferenceFourAllNNormalRawP,
    unequalFixedDifferenceFourAllNNormalRawL,
    unequalFixedDifferenceFourAllNOracleVarianceWeight_eq] using hid

/-- The canonical base weight is the literal Graybill--Deal weight. -/
theorem
    unequalFixedDifferenceFourAllNCanonicalR_eq_rawGraybillDealWeight
    {n : ℕ} (hn : 13 ≤ n)
    {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalR (unequalFixedDifferenceFourSampleM n)
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω)
      =
    unequalFixedDifferenceFourAllNRawGraybillDealWeight n X Y ω := by
  let τ₁ : ℝ :=
    (v₁ : ℝ) / (unequalFixedDifferenceFourAllNResidualDF1 n + 1)
  let τ₂ : ℝ :=
    (v₂ : ℝ) / (unequalFixedDifferenceFourAllNResidualDF2 n + 1)
  let u₁ : ℝ :=
    unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
  let u₂ : ℝ :=
    unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω
  have hτ : τ₁ + τ₂ ≠ 0 := by
    apply ne_of_gt
    dsimp only [τ₁, τ₂]
    positivity
  have hu : u₁ + u₂ ≠ 0 := by
    simpa [u₁, u₂, unequalFixedDifferenceFourAllNNormalRawL] using hL
  have hdf₁ := unequalFD4AllNRawCoordinates_cast_df_one hn
  have hdf₂ := unequalFD4AllNRawCoordinates_cast_df_two n
  have hdf₁ne := unequalFD4AllNRawCoordinates_cast_df_one_ne hn
  have hdf₂ne := unequalFD4AllNRawCoordinates_cast_df_two_ne n
  have hcomponent :
      τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
          + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1))
        =
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω := by
    dsimp only [τ₁, τ₂, u₁, u₂]
    rw [← hdf₁, ← hdf₂,
      unequalFixedDifferenceFourAllNNormalRawU1_eq_sampleVariance
        hn v₁ X ω,
      unequalFixedDifferenceFourAllNNormalRawU2_eq_sampleVariance
        hn v₂ Y ω]
    unfold unequalFixedDifferenceFourAllNRawMeanVarianceSum
      unequalFixedDifferenceFourAllNRawMeanVariance1
      unequalFixedDifferenceFourAllNRawMeanVariance2
    field_simp [hv₁.ne', hv₂.ne', hdf₁ne, hdf₂ne]
  have hcomponent_ne :
      τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
          + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1))
        ≠ 0 := by
    rwa [hcomponent]
  have hr :=
    unequalFD4AllNRawCoordinates_R_ratio_sum
      hn hτ hu hcomponent_ne
  rw [hcomponent] at hr
  have hfirst :
      τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
        =
      unequalFixedDifferenceFourAllNRawMeanVariance1 n X ω := by
    dsimp only [τ₁, u₁]
    rw [← hdf₁,
      unequalFixedDifferenceFourAllNNormalRawU1_eq_sampleVariance
        hn v₁ X ω]
    unfold unequalFixedDifferenceFourAllNRawMeanVariance1
    field_simp [hv₁.ne', hdf₁ne]
  rw [hfirst] at hr
  simpa [τ₁, τ₂, u₁, u₂,
    unequalFixedDifferenceFourAllNNormalRawP,
    unequalFixedDifferenceFourAllNOracleVarianceWeight_eq,
    unequalFixedDifferenceFourAllNNormalMeanVarianceSum,
    unequalFixedDifferenceFourAllNRawGraybillDealWeight] using hr

/-- The canonical quadratic coordinate is the literal raw statistic. -/
theorem
    unequalFixedDifferenceFourAllNCanonicalQ_eq_rawQuadraticStatistic
    {n : ℕ} (hn : 13 ≤ n)
    {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalQ (unequalFixedDifferenceFourSampleM n)
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y ω)
      =
    unequalFixedDifferenceFourAllNRawQuadraticStatistic n X Y ω := by
  let τ₁ : ℝ :=
    (v₁ : ℝ) / (unequalFixedDifferenceFourAllNResidualDF1 n + 1)
  let τ₂ : ℝ :=
    (v₂ : ℝ) / (unequalFixedDifferenceFourAllNResidualDF2 n + 1)
  let u₁ : ℝ :=
    unequalFixedDifferenceFourAllNNormalRawU1 n v₁ X ω
  let u₂ : ℝ :=
    unequalFixedDifferenceFourAllNNormalRawU2 n v₂ Y ω
  let d : ℝ :=
    meanDifferenceU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω
  have hτ : τ₁ + τ₂ ≠ 0 := by
    apply ne_of_gt
    dsimp only [τ₁, τ₂]
    positivity
  have hu : u₁ + u₂ ≠ 0 := by
    simpa [u₁, u₂, unequalFixedDifferenceFourAllNNormalRawL] using hL
  have hdf₁ := unequalFD4AllNRawCoordinates_cast_df_one hn
  have hdf₂ := unequalFD4AllNRawCoordinates_cast_df_two n
  have hdf₁ne := unequalFD4AllNRawCoordinates_cast_df_one_ne hn
  have hdf₂ne := unequalFD4AllNRawCoordinates_cast_df_two_ne n
  have hcomponent :
      τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
          + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1))
        =
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω := by
    dsimp only [τ₁, τ₂, u₁, u₂]
    rw [← hdf₁, ← hdf₂,
      unequalFixedDifferenceFourAllNNormalRawU1_eq_sampleVariance
        hn v₁ X ω,
      unequalFixedDifferenceFourAllNNormalRawU2_eq_sampleVariance
        hn v₂ Y ω]
    unfold unequalFixedDifferenceFourAllNRawMeanVarianceSum
      unequalFixedDifferenceFourAllNRawMeanVariance1
      unequalFixedDifferenceFourAllNRawMeanVariance2
    field_simp [hv₁.ne', hv₂.ne', hdf₁ne, hdf₂ne]
  have hcomponent_ne :
      τ₁ * u₁ / (2 * (unequalFixedDifferenceFourSampleM n - 1))
          + τ₂ * u₂ / (2 * (unequalFixedDifferenceFourSampleM n + 1))
        ≠ 0 := by
    rwa [hcomponent]
  have hq :=
    unequalFD4AllNRawCoordinates_Q_ratio_sum
      (d := d) hn hτ hu hcomponent_ne
  rw [hcomponent] at hq
  simpa [τ₁, τ₂, u₁, u₂, d,
    unequalFixedDifferenceFourAllNNormalRawP,
    unequalFixedDifferenceFourAllNNormalRawL,
    unequalFixedDifferenceFourAllNNormalRawV,
    generalStandardizedDifference,
    unequalFixedDifferenceFourAllNNormalMeanVarianceSum,
    unequalFixedDifferenceFourAllNOracleVarianceWeight_eq,
    unequalFixedDifferenceFourAllNRawQuadraticStatistic] using hq

/-- The canonical perturbation direction is the literal raw direction. -/
theorem unequalFixedDifferenceFourAllNCanonicalH_eq_rawDirection
    {n : ℕ} (hn : 13 ≤ n)
    {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalH (unequalFixedDifferenceFourSampleM n)
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y ω)
      =
    unequalDampedPhi
        (unequalFixedDifferenceFourRealT (unequalFixedDifferenceFourSampleM n))
        (unequalFixedDifferenceFourRealKappa (unequalFixedDifferenceFourSampleM n))
        (unequalFixedDifferenceFourAllNRawGraybillDealWeight n X Y ω)
      * (unequalFixedDifferenceFourRealC (unequalFixedDifferenceFourSampleM n)
        - unequalFixedDifferenceFourAllNRawQuadraticStatistic n X Y ω) := by
  unfold unequalFixedDifferenceFourRealCanonicalH
  rw [unequalFixedDifferenceFourAllNCanonicalR_eq_rawGraybillDealWeight
      hn hv₁ hv₂ hL hA,
    unequalFixedDifferenceFourAllNCanonicalQ_eq_rawQuadraticStatistic
      hn hv₁ hv₂ hL hA]

/-- The un-clipped canonical weight is the literal raw perturbation. -/
theorem unequalFixedDifferenceFourAllNCanonicalWeight_eq_rawPerturbedWeight
    {n : ℕ} (hn : 13 ≤ n)
    {ε : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalWeight (unequalFixedDifferenceFourSampleM n) ε
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y ω)
      =
    unequalFixedDifferenceFourAllNRawPerturbedWeight ε n X Y ω := by
  unfold unequalFixedDifferenceFourRealCanonicalWeight perturbation
    unequalFixedDifferenceFourAllNRawPerturbedWeight
  rw [unequalFixedDifferenceFourAllNCanonicalR_eq_rawGraybillDealWeight
      hn hv₁ hv₂ hL hA,
    unequalFixedDifferenceFourAllNCanonicalH_eq_rawDirection
      hn hv₁ hv₂ hL hA]
  ring

/-- The clipped canonical weight is the literal clipped perturbation. -/
theorem
    unequalFixedDifferenceFourAllNCanonicalClippedWeight_eq_rawClippedPerturbedWeight
    {n : ℕ} (hn : 13 ≤ n)
    {ε : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω ≠ 0) :
    unequalFixedDifferenceFourRealCanonicalClippedWeight (unequalFixedDifferenceFourSampleM n) ε
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y ω)
      =
    unequalFixedDifferenceFourAllNRawClippedPerturbedWeight
      ε n X Y ω := by
  unfold unequalFixedDifferenceFourRealCanonicalClippedWeight
    unequalFixedDifferenceFourAllNRawClippedPerturbedWeight
  rw [unequalFixedDifferenceFourAllNCanonicalWeight_eq_rawPerturbedWeight
    hn hv₁ hv₂ hL hA]

/-- The canonical baseline is the literal Graybill--Deal estimator. -/
theorem
    unequalFixedDifferenceFourAllNCanonicalBaseEstimator_eq_rawGraybillDealEstimator
    {n : ℕ} (hn : 13 ≤ n)
    {μ : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω ≠ 0) :
    μ
        + unequalFixedDifferenceFourAllNOracleCenteredError
            n μ v₁ v₂ X Y ω
        + meanDifferenceU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω
          * (unequalFixedDifferenceFourRealCanonicalR (unequalFixedDifferenceFourSampleM n)
                (oracleVarianceWeightU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
                (unequalFixedDifferenceFourAllNNormalRawP
                  n v₁ v₂ X Y ω)
              - oracleVarianceWeightU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
      =
    unequalFixedDifferenceFourAllNRawGraybillDealEstimator n X Y ω := by
  rw [unequalFixedDifferenceFourAllNCanonicalR_eq_rawGraybillDealWeight
      hn hv₁ hv₂ hL hA]
  unfold unequalFixedDifferenceFourAllNOracleCenteredError
    oracleCenteredErrorU
    unequalFixedDifferenceFourAllNRawGraybillDealEstimator
  ring

/-- The canonical competitor is the literal raw clipped competitor. -/
theorem
    unequalFixedDifferenceFourAllNCanonicalClippedEstimator_eq_rawClippedPerturbedEstimator
    {n : ℕ} (hn : 13 ≤ n)
    {ε μ : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourAllNRawMeanVarianceSum n X Y ω ≠ 0) :
    μ
        + unequalFixedDifferenceFourAllNOracleCenteredError
            n μ v₁ v₂ X Y ω
        + meanDifferenceU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω
          * (unequalFixedDifferenceFourRealCanonicalClippedWeight (unequalFixedDifferenceFourSampleM n) ε
                (oracleVarianceWeightU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
                (unequalFixedDifferenceFourAllNNormalRawP
                  n v₁ v₂ X Y ω)
                (unequalFixedDifferenceFourAllNNormalRawL
                  n v₁ v₂ X Y ω)
                (unequalFixedDifferenceFourAllNNormalRawV
                  n v₁ v₂ X Y ω)
              - oracleVarianceWeightU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
      =
    unequalFixedDifferenceFourAllNRawClippedPerturbedEstimator
      ε n X Y ω := by
  rw [
    unequalFixedDifferenceFourAllNCanonicalClippedWeight_eq_rawClippedPerturbedWeight
      hn hv₁ hv₂ hL hA]
  unfold unequalFixedDifferenceFourAllNOracleCenteredError
    oracleCenteredErrorU
    unequalFixedDifferenceFourAllNRawClippedPerturbedEstimator
  ring

/-! ## Almost-everywhere transport under the raw normal model -/

namespace TwoNormalSamplesU

variable
  {n : ℕ}
  {X : Fin (unequalFixedDifferenceFourAllNResidualDF1 n + 1) → Ω → ℝ}
  {Y : Fin (unequalFixedDifferenceFourAllNResidualDF2 n + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

theorem
    ae_eq_unequalFixedDifferenceFourAllNCanonicalR_rawGraybillDealWeight
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      unequalFixedDifferenceFourRealCanonicalR (unequalFixedDifferenceFourSampleM n)
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω))
      =ᵐ[P]
    unequalFixedDifferenceFourAllNRawGraybillDealWeight n X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourAllNNormalRawL hn hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourAllNRawMeanVarianceSum
        hn hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourAllNCanonicalR_eq_rawGraybillDealWeight
      hn hv₁ hv₂ hL hA

theorem
    ae_eq_unequalFixedDifferenceFourAllNCanonicalQ_rawQuadraticStatistic
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      unequalFixedDifferenceFourRealCanonicalQ (unequalFixedDifferenceFourSampleM n)
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y ω))
      =ᵐ[P]
    unequalFixedDifferenceFourAllNRawQuadraticStatistic n X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourAllNNormalRawL hn hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourAllNRawMeanVarianceSum
        hn hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourAllNCanonicalQ_eq_rawQuadraticStatistic
      hn hv₁ hv₂ hL hA

theorem
    ae_eq_unequalFixedDifferenceFourAllNCanonicalClippedWeight_raw
    (ε : ℝ)
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      unequalFixedDifferenceFourRealCanonicalClippedWeight (unequalFixedDifferenceFourSampleM n) ε
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourAllNResidualDF1 n)
          (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
        (unequalFixedDifferenceFourAllNNormalRawP n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawL n v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourAllNNormalRawV n v₁ v₂ X Y ω))
      =ᵐ[P]
    unequalFixedDifferenceFourAllNRawClippedPerturbedWeight
      ε n X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourAllNNormalRawL hn hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourAllNRawMeanVarianceSum
        hn hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourAllNCanonicalClippedWeight_eq_rawClippedPerturbedWeight
      hn hv₁ hv₂ hL hA

theorem
    ae_eq_unequalFixedDifferenceFourAllNCanonicalBaseEstimator_raw
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      μ
        + unequalFixedDifferenceFourAllNOracleCenteredError
            n μ v₁ v₂ X Y ω
        + meanDifferenceU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω
          * (unequalFixedDifferenceFourRealCanonicalR (unequalFixedDifferenceFourSampleM n)
                (oracleVarianceWeightU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
                (unequalFixedDifferenceFourAllNNormalRawP
                  n v₁ v₂ X Y ω)
              - oracleVarianceWeightU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂))
      =ᵐ[P]
    unequalFixedDifferenceFourAllNRawGraybillDealEstimator n X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourAllNNormalRawL hn hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourAllNRawMeanVarianceSum
        hn hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourAllNCanonicalBaseEstimator_eq_rawGraybillDealEstimator
      hn hv₁ hv₂ hL hA

theorem
    ae_eq_unequalFixedDifferenceFourAllNCanonicalClippedEstimator_raw
    (ε : ℝ)
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourAllNResidualDF1 n)
      (unequalFixedDifferenceFourAllNResidualDF2 n)
      X Y P μ v₁ v₂)
    (hn : 13 ≤ n)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      μ
        + unequalFixedDifferenceFourAllNOracleCenteredError
            n μ v₁ v₂ X Y ω
        + meanDifferenceU
            (unequalFixedDifferenceFourAllNResidualDF1 n)
            (unequalFixedDifferenceFourAllNResidualDF2 n) X Y ω
          * (unequalFixedDifferenceFourRealCanonicalClippedWeight (unequalFixedDifferenceFourSampleM n) ε
                (oracleVarianceWeightU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂)
                (unequalFixedDifferenceFourAllNNormalRawP
                  n v₁ v₂ X Y ω)
                (unequalFixedDifferenceFourAllNNormalRawL
                  n v₁ v₂ X Y ω)
                (unequalFixedDifferenceFourAllNNormalRawV
                  n v₁ v₂ X Y ω)
              - oracleVarianceWeightU
                  (unequalFixedDifferenceFourAllNResidualDF1 n)
                  (unequalFixedDifferenceFourAllNResidualDF2 n) v₁ v₂))
      =ᵐ[P]
    unequalFixedDifferenceFourAllNRawClippedPerturbedEstimator
      ε n X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourAllNNormalRawL hn hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourAllNRawMeanVarianceSum
        hn hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourAllNCanonicalClippedEstimator_eq_rawClippedPerturbedEstimator
      hn hv₁ hv₂ hL hA

end TwoNormalSamplesU

end

end GraybillDeal
