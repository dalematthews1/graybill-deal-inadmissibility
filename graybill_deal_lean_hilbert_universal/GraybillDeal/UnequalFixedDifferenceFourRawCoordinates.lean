import GraybillDeal.UnequalFixedDifferenceFourCanonical
import GraybillDeal.UnequalFixedDifferenceFourRawSummary
import GraybillDeal.UnequalFixedDifferenceFourRawEstimator
import GraybillDeal.UnequalFixedDifferenceFourRawPositivity

/-!
# Raw/canonical coordinate identities for the fixed-difference-four family

For `(n₁,n₂)=(2m-1,2m+3)`, this module identifies the direct canonical
coordinates with the literal Graybill--Deal quantities.  The key
normalization is

`A₁+A₂ = λ L D_m(θ,P)/(4m)`,

where `Aᵢ` are the two estimated sample-mean variances, `λ` is the true
variance of the sample-mean difference, and `(P,L)` are the beta--gamma
residual coordinates.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem unequalFD4RawCoordinates_cast_df_one
    {m : ℕ} (hm : 7 ≤ m) :
    (unequalFixedDifferenceFourResidualDF1 m : ℝ)
      = 2 * ((m : ℝ) - 1) := by
  have hm1 : 1 ≤ m := by omega
  unfold unequalFixedDifferenceFourResidualDF1
  rw [Nat.cast_mul, Nat.cast_sub hm1]
  push_cast
  ring

private theorem unequalFD4RawCoordinates_cast_df_two
    (m : ℕ) :
    (unequalFixedDifferenceFourResidualDF2 m : ℝ)
      = 2 * ((m : ℝ) + 1) := by
  unfold unequalFixedDifferenceFourResidualDF2
  push_cast
  ring

private theorem unequalFD4RawCoordinates_cast_df_one_ne
    {m : ℕ} (hm : 7 ≤ m) :
    (unequalFixedDifferenceFourResidualDF1 m : ℝ) ≠ 0 := by
  rw [unequalFD4RawCoordinates_cast_df_one hm]
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  apply ne_of_gt
  nlinarith

private theorem unequalFD4RawCoordinates_cast_df_two_ne
    (m : ℕ) :
    (unequalFixedDifferenceFourResidualDF2 m : ℝ) ≠ 0 := by
  rw [unequalFD4RawCoordinates_cast_df_two m]
  positivity

private theorem unequalFD4RawCoordinates_denom_ratio_sum
    {m : ℕ} (hm : 7 ≤ m)
    {τ₁ τ₂ u₁ u₂ : ℝ}
    (hτ : τ₁ + τ₂ ≠ 0) (hu : u₁ + u₂ ≠ 0) :
    (τ₁ + τ₂) * (u₁ + u₂)
          * unequalFixedDifferenceFourCanonicalDenom m
              (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        / (4 * (m : ℝ))
      =
    τ₁ * u₁ / (2 * ((m : ℝ) - 1))
      + τ₂ * u₂ / (2 * ((m : ℝ) + 1)) := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hp1 : (m : ℝ) + 1 ≠ 0 := by linarith
  unfold unequalFixedDifferenceFourCanonicalDenom
    unequalFixedDifferenceFourT unequalFixedDifferenceFourQ
  field_simp [hτ, hu, hm0, hm1, hp1]
  ring

private theorem unequalFD4RawCoordinates_R_ratio_sum
    {m : ℕ} (hm : 7 ≤ m)
    {τ₁ τ₂ u₁ u₂ : ℝ}
    (hτ : τ₁ + τ₂ ≠ 0) (hu : u₁ + u₂ ≠ 0)
    (hA :
      τ₁ * u₁ / (2 * ((m : ℝ) - 1))
          + τ₂ * u₂ / (2 * ((m : ℝ) + 1))
        ≠ 0) :
    unequalFixedDifferenceFourCanonicalR m
        (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
      =
    (τ₁ * u₁ / (2 * ((m : ℝ) - 1)))
      /
    (τ₁ * u₁ / (2 * ((m : ℝ) - 1))
      + τ₂ * u₂ / (2 * ((m : ℝ) + 1))) := by
  have hmR : (7 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hden :
      unequalFixedDifferenceFourCanonicalDenom m
          (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        ≠ 0 := by
    intro hzero
    have hid :=
      unequalFD4RawCoordinates_denom_ratio_sum hm hτ hu
    rw [hzero] at hid
    simp only [mul_zero, zero_div] at hid
    exact hA hid.symm
  unfold unequalFixedDifferenceFourCanonicalR
  apply (div_eq_div_iff hden hA).2
  rw [← unequalFD4RawCoordinates_denom_ratio_sum hm hτ hu]
  unfold unequalFixedDifferenceFourT
  field_simp [hτ, hu, hm0, hm1]
  ring

private theorem unequalFD4RawCoordinates_Q_ratio_sum
    {m : ℕ} (hm : 7 ≤ m)
    {τ₁ τ₂ u₁ u₂ d : ℝ}
    (hτ : τ₁ + τ₂ ≠ 0) (hu : u₁ + u₂ ≠ 0)
    (hA :
      τ₁ * u₁ / (2 * ((m : ℝ) - 1))
          + τ₂ * u₂ / (2 * ((m : ℝ) + 1))
        ≠ 0) :
    unequalFixedDifferenceFourCanonicalQ m
        (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        (u₁ + u₂) (d ^ 2 / (τ₁ + τ₂))
      =
    d ^ 2
      /
    (τ₁ * u₁ / (2 * ((m : ℝ) - 1))
      + τ₂ * u₂ / (2 * ((m : ℝ) + 1))) := by
  have hden :
      unequalFixedDifferenceFourCanonicalDenom m
          (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        ≠ 0 := by
    intro hzero
    have hid :=
      unequalFD4RawCoordinates_denom_ratio_sum hm hτ hu
    rw [hzero] at hid
    simp only [mul_zero, zero_div] at hid
    exact hA hid.symm
  have hUden :
      (u₁ + u₂)
          * unequalFixedDifferenceFourCanonicalDenom m
              (τ₁ / (τ₁ + τ₂)) (u₁ / (u₁ + u₂))
        ≠ 0 :=
    mul_ne_zero hu hden
  unfold unequalFixedDifferenceFourCanonicalQ
  apply (div_eq_div_iff hUden hA).2
  rw [← unequalFD4RawCoordinates_denom_ratio_sum hm hτ hu]
  field_simp [hτ, hu]

/-! ## Elementary raw-summary identities -/

/-- The family oracle weight is the ratio of the two true mean variances. -/
theorem unequalFixedDifferenceFourOracleVarianceWeight_eq
    (m : ℕ) (v₁ v₂ : NNReal) :
    oracleVarianceWeightU
        (unequalFixedDifferenceFourResidualDF1 m)
        (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂
      =
    ((v₁ : ℝ) / (unequalFixedDifferenceFourResidualDF1 m + 1))
      / unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂ := by
  rfl

/-- The first standardized residual coordinate is `ν₁ S₁²/v₁`. -/
theorem unequalFixedDifferenceFourNormalRawU1_eq_sampleVariance
    {m : ℕ} (hm : 7 ≤ m)
    (v₁ : NNReal)
    (X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ)
    (ω : Ω) :
    unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
      =
    (unequalFixedDifferenceFourResidualDF1 m : ℝ)
      * sampleVarianceN
          (unequalFixedDifferenceFourResidualDF1 m) X ω
      / (v₁ : ℝ) := by
  have hν :
      0 < unequalFixedDifferenceFourResidualDF1 m := by
    unfold unequalFixedDifferenceFourResidualDF1
    omega
  unfold unequalFixedDifferenceFourNormalRawU1
    scaledResidualSumSquaresN
  rw [← residualDF_mul_sampleVarianceN hν X ω]

/-- The second standardized residual coordinate is `ν₂ S₂²/v₂`. -/
theorem unequalFixedDifferenceFourNormalRawU2_eq_sampleVariance
    {m : ℕ} (hm : 7 ≤ m)
    (v₂ : NNReal)
    (Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ)
    (ω : Ω) :
    unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω
      =
    (unequalFixedDifferenceFourResidualDF2 m : ℝ)
      * sampleVarianceN
          (unequalFixedDifferenceFourResidualDF2 m) Y ω
      / (v₂ : ℝ) := by
  have hν :
      0 < unequalFixedDifferenceFourResidualDF2 m := by
    unfold unequalFixedDifferenceFourResidualDF2
    omega
  unfold unequalFixedDifferenceFourNormalRawU2
    scaledResidualSumSquaresN
  rw [← residualDF_mul_sampleVarianceN hν Y ω]

/-! ## Pointwise canonical/raw coordinate transport -/

/--
The family canonical denominator reconstructs the sum of the two estimated
sample-mean variances.
-/
theorem unequalFixedDifferenceFourRawMeanVarianceSum_eq_canonical
    {m : ℕ} (hm : 7 ≤ m)
    {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω ≠ 0) :
    unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω
      =
    unequalFixedDifferenceFourNormalMeanVarianceSum m v₁ v₂
      * unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω
      * unequalFixedDifferenceFourCanonicalDenom m
          (oracleVarianceWeightU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
          (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω)
      / (4 * (m : ℝ)) := by
  let τ₁ : ℝ :=
    (v₁ : ℝ) / (unequalFixedDifferenceFourResidualDF1 m + 1)
  let τ₂ : ℝ :=
    (v₂ : ℝ) / (unequalFixedDifferenceFourResidualDF2 m + 1)
  let u₁ : ℝ :=
    unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
  let u₂ : ℝ :=
    unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω
  have hτ : τ₁ + τ₂ ≠ 0 := by
    apply ne_of_gt
    dsimp only [τ₁, τ₂]
    positivity
  have hu : u₁ + u₂ ≠ 0 := by
    simpa [u₁, u₂, unequalFixedDifferenceFourNormalRawL] using hL
  have hid :=
    unequalFD4RawCoordinates_denom_ratio_sum hm hτ hu
  have hdf₁ :=
    unequalFD4RawCoordinates_cast_df_one hm
  have hdf₂ :=
    unequalFD4RawCoordinates_cast_df_two m
  have hdf₁ne :=
    unequalFD4RawCoordinates_cast_df_one_ne hm
  have hdf₂ne :=
    unequalFD4RawCoordinates_cast_df_two_ne m
  have hright :
      τ₁ * u₁ / (2 * ((m : ℝ) - 1))
          + τ₂ * u₂ / (2 * ((m : ℝ) + 1))
        =
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω := by
    dsimp only [τ₁, τ₂, u₁, u₂]
    rw [← hdf₁, ← hdf₂,
      unequalFixedDifferenceFourNormalRawU1_eq_sampleVariance
        hm v₁ X ω,
      unequalFixedDifferenceFourNormalRawU2_eq_sampleVariance
        hm v₂ Y ω]
    unfold unequalFixedDifferenceFourRawMeanVarianceSum
      unequalFixedDifferenceFourRawMeanVariance1
      unequalFixedDifferenceFourRawMeanVariance2
    field_simp [hv₁.ne', hv₂.ne', hdf₁ne, hdf₂ne]
  rw [hright] at hid
  symm
  simpa [τ₁, τ₂, u₁, u₂,
    unequalFixedDifferenceFourNormalMeanVarianceSum,
    unequalFixedDifferenceFourNormalRawP,
    unequalFixedDifferenceFourNormalRawL,
    unequalFixedDifferenceFourOracleVarianceWeight_eq] using hid

/-- The canonical base weight is the literal Graybill--Deal weight. -/
theorem
    unequalFixedDifferenceFourCanonicalR_eq_rawGraybillDealWeight
    {m : ℕ} (hm : 7 ≤ m)
    {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω ≠ 0) :
    unequalFixedDifferenceFourCanonicalR m
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω)
      =
    unequalFixedDifferenceFourRawGraybillDealWeight m X Y ω := by
  let τ₁ : ℝ :=
    (v₁ : ℝ) / (unequalFixedDifferenceFourResidualDF1 m + 1)
  let τ₂ : ℝ :=
    (v₂ : ℝ) / (unequalFixedDifferenceFourResidualDF2 m + 1)
  let u₁ : ℝ :=
    unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
  let u₂ : ℝ :=
    unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω
  have hτ : τ₁ + τ₂ ≠ 0 := by
    apply ne_of_gt
    dsimp only [τ₁, τ₂]
    positivity
  have hu : u₁ + u₂ ≠ 0 := by
    simpa [u₁, u₂, unequalFixedDifferenceFourNormalRawL] using hL
  have hdf₁ := unequalFD4RawCoordinates_cast_df_one hm
  have hdf₂ := unequalFD4RawCoordinates_cast_df_two m
  have hdf₁ne := unequalFD4RawCoordinates_cast_df_one_ne hm
  have hdf₂ne := unequalFD4RawCoordinates_cast_df_two_ne m
  have hcomponent :
      τ₁ * u₁ / (2 * ((m : ℝ) - 1))
          + τ₂ * u₂ / (2 * ((m : ℝ) + 1))
        =
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω := by
    dsimp only [τ₁, τ₂, u₁, u₂]
    rw [← hdf₁, ← hdf₂,
      unequalFixedDifferenceFourNormalRawU1_eq_sampleVariance
        hm v₁ X ω,
      unequalFixedDifferenceFourNormalRawU2_eq_sampleVariance
        hm v₂ Y ω]
    unfold unequalFixedDifferenceFourRawMeanVarianceSum
      unequalFixedDifferenceFourRawMeanVariance1
      unequalFixedDifferenceFourRawMeanVariance2
    field_simp [hv₁.ne', hv₂.ne', hdf₁ne, hdf₂ne]
  have hcomponent_ne :
      τ₁ * u₁ / (2 * ((m : ℝ) - 1))
          + τ₂ * u₂ / (2 * ((m : ℝ) + 1))
        ≠ 0 := by
    rwa [hcomponent]
  have hr :=
    unequalFD4RawCoordinates_R_ratio_sum
      hm hτ hu hcomponent_ne
  rw [hcomponent] at hr
  have hfirst :
      τ₁ * u₁ / (2 * ((m : ℝ) - 1))
        =
      unequalFixedDifferenceFourRawMeanVariance1 m X ω := by
    dsimp only [τ₁, u₁]
    rw [← hdf₁,
      unequalFixedDifferenceFourNormalRawU1_eq_sampleVariance
        hm v₁ X ω]
    unfold unequalFixedDifferenceFourRawMeanVariance1
    field_simp [hv₁.ne', hdf₁ne]
  rw [hfirst] at hr
  simpa [τ₁, τ₂, u₁, u₂,
    unequalFixedDifferenceFourNormalRawP,
    unequalFixedDifferenceFourOracleVarianceWeight_eq,
    unequalFixedDifferenceFourNormalMeanVarianceSum,
    unequalFixedDifferenceFourRawGraybillDealWeight] using hr

/-- The canonical quadratic coordinate is the literal raw statistic. -/
theorem
    unequalFixedDifferenceFourCanonicalQ_eq_rawQuadraticStatistic
    {m : ℕ} (hm : 7 ≤ m)
    {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω ≠ 0) :
    unequalFixedDifferenceFourCanonicalQ m
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y ω)
      =
    unequalFixedDifferenceFourRawQuadraticStatistic m X Y ω := by
  let τ₁ : ℝ :=
    (v₁ : ℝ) / (unequalFixedDifferenceFourResidualDF1 m + 1)
  let τ₂ : ℝ :=
    (v₂ : ℝ) / (unequalFixedDifferenceFourResidualDF2 m + 1)
  let u₁ : ℝ :=
    unequalFixedDifferenceFourNormalRawU1 m v₁ X ω
  let u₂ : ℝ :=
    unequalFixedDifferenceFourNormalRawU2 m v₂ Y ω
  let d : ℝ :=
    meanDifferenceU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m) X Y ω
  have hτ : τ₁ + τ₂ ≠ 0 := by
    apply ne_of_gt
    dsimp only [τ₁, τ₂]
    positivity
  have hu : u₁ + u₂ ≠ 0 := by
    simpa [u₁, u₂, unequalFixedDifferenceFourNormalRawL] using hL
  have hdf₁ := unequalFD4RawCoordinates_cast_df_one hm
  have hdf₂ := unequalFD4RawCoordinates_cast_df_two m
  have hdf₁ne := unequalFD4RawCoordinates_cast_df_one_ne hm
  have hdf₂ne := unequalFD4RawCoordinates_cast_df_two_ne m
  have hcomponent :
      τ₁ * u₁ / (2 * ((m : ℝ) - 1))
          + τ₂ * u₂ / (2 * ((m : ℝ) + 1))
        =
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω := by
    dsimp only [τ₁, τ₂, u₁, u₂]
    rw [← hdf₁, ← hdf₂,
      unequalFixedDifferenceFourNormalRawU1_eq_sampleVariance
        hm v₁ X ω,
      unequalFixedDifferenceFourNormalRawU2_eq_sampleVariance
        hm v₂ Y ω]
    unfold unequalFixedDifferenceFourRawMeanVarianceSum
      unequalFixedDifferenceFourRawMeanVariance1
      unequalFixedDifferenceFourRawMeanVariance2
    field_simp [hv₁.ne', hv₂.ne', hdf₁ne, hdf₂ne]
  have hcomponent_ne :
      τ₁ * u₁ / (2 * ((m : ℝ) - 1))
          + τ₂ * u₂ / (2 * ((m : ℝ) + 1))
        ≠ 0 := by
    rwa [hcomponent]
  have hq :=
    unequalFD4RawCoordinates_Q_ratio_sum
      (d := d) hm hτ hu hcomponent_ne
  rw [hcomponent] at hq
  simpa [τ₁, τ₂, u₁, u₂, d,
    unequalFixedDifferenceFourNormalRawP,
    unequalFixedDifferenceFourNormalRawL,
    unequalFixedDifferenceFourNormalRawV,
    generalStandardizedDifference,
    unequalFixedDifferenceFourNormalMeanVarianceSum,
    unequalFixedDifferenceFourOracleVarianceWeight_eq,
    unequalFixedDifferenceFourRawQuadraticStatistic] using hq

/-- The canonical perturbation direction is the literal raw direction. -/
theorem unequalFixedDifferenceFourCanonicalH_eq_rawDirection
    {m : ℕ} (hm : 7 ≤ m)
    {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω ≠ 0) :
    unequalFixedDifferenceFourCanonicalH m
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y ω)
      =
    unequalDampedPhi
        (unequalFixedDifferenceFourT m)
        (unequalFixedDifferenceFourKappa m)
        (unequalFixedDifferenceFourRawGraybillDealWeight m X Y ω)
      * (unequalFixedDifferenceFourC m
        - unequalFixedDifferenceFourRawQuadraticStatistic m X Y ω) := by
  unfold unequalFixedDifferenceFourCanonicalH
  rw [unequalFixedDifferenceFourCanonicalR_eq_rawGraybillDealWeight
      hm hv₁ hv₂ hL hA,
    unequalFixedDifferenceFourCanonicalQ_eq_rawQuadraticStatistic
      hm hv₁ hv₂ hL hA]

/-- The un-clipped canonical weight is the literal raw perturbation. -/
theorem unequalFixedDifferenceFourCanonicalWeight_eq_rawPerturbedWeight
    {m : ℕ} (hm : 7 ≤ m)
    {ε : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω ≠ 0) :
    unequalFixedDifferenceFourCanonicalWeight m ε
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y ω)
      =
    unequalFixedDifferenceFourRawPerturbedWeight ε m X Y ω := by
  unfold unequalFixedDifferenceFourCanonicalWeight perturbation
    unequalFixedDifferenceFourRawPerturbedWeight
  rw [unequalFixedDifferenceFourCanonicalR_eq_rawGraybillDealWeight
      hm hv₁ hv₂ hL hA,
    unequalFixedDifferenceFourCanonicalH_eq_rawDirection
      hm hv₁ hv₂ hL hA]
  ring

/-- The clipped canonical weight is the literal clipped perturbation. -/
theorem
    unequalFixedDifferenceFourCanonicalClippedWeight_eq_rawClippedPerturbedWeight
    {m : ℕ} (hm : 7 ≤ m)
    {ε : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω ≠ 0) :
    unequalFixedDifferenceFourCanonicalClippedWeight m ε
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y ω)
      =
    unequalFixedDifferenceFourRawClippedPerturbedWeight
      ε m X Y ω := by
  unfold unequalFixedDifferenceFourCanonicalClippedWeight
    unequalFixedDifferenceFourRawClippedPerturbedWeight
  rw [unequalFixedDifferenceFourCanonicalWeight_eq_rawPerturbedWeight
    hm hv₁ hv₂ hL hA]

/-- The canonical baseline is the literal Graybill--Deal estimator. -/
theorem
    unequalFixedDifferenceFourCanonicalBaseEstimator_eq_rawGraybillDealEstimator
    {m : ℕ} (hm : 7 ≤ m)
    {μ : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω ≠ 0) :
    μ
        + unequalFixedDifferenceFourOracleCenteredError
            m μ v₁ v₂ X Y ω
        + meanDifferenceU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) X Y ω
          * (unequalFixedDifferenceFourCanonicalR m
                (oracleVarianceWeightU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
                (unequalFixedDifferenceFourNormalRawP
                  m v₁ v₂ X Y ω)
              - oracleVarianceWeightU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
      =
    unequalFixedDifferenceFourRawGraybillDealEstimator m X Y ω := by
  rw [unequalFixedDifferenceFourCanonicalR_eq_rawGraybillDealWeight
      hm hv₁ hv₂ hL hA]
  unfold unequalFixedDifferenceFourOracleCenteredError
    oracleCenteredErrorU
    unequalFixedDifferenceFourRawGraybillDealEstimator
  ring

/-- The canonical competitor is the literal raw clipped competitor. -/
theorem
    unequalFixedDifferenceFourCanonicalClippedEstimator_eq_rawClippedPerturbedEstimator
    {m : ℕ} (hm : 7 ≤ m)
    {ε μ : ℝ} {v₁ v₂ : NNReal}
    {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
    {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
    {ω : Ω}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ))
    (hL : unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω ≠ 0)
    (hA :
      unequalFixedDifferenceFourRawMeanVarianceSum m X Y ω ≠ 0) :
    μ
        + unequalFixedDifferenceFourOracleCenteredError
            m μ v₁ v₂ X Y ω
        + meanDifferenceU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) X Y ω
          * (unequalFixedDifferenceFourCanonicalClippedWeight m ε
                (oracleVarianceWeightU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
                (unequalFixedDifferenceFourNormalRawP
                  m v₁ v₂ X Y ω)
                (unequalFixedDifferenceFourNormalRawL
                  m v₁ v₂ X Y ω)
                (unequalFixedDifferenceFourNormalRawV
                  m v₁ v₂ X Y ω)
              - oracleVarianceWeightU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
      =
    unequalFixedDifferenceFourRawClippedPerturbedEstimator
      ε m X Y ω := by
  rw [
    unequalFixedDifferenceFourCanonicalClippedWeight_eq_rawClippedPerturbedWeight
      hm hv₁ hv₂ hL hA]
  unfold unequalFixedDifferenceFourOracleCenteredError
    oracleCenteredErrorU
    unequalFixedDifferenceFourRawClippedPerturbedEstimator
  ring

/-! ## Almost-everywhere transport under the raw normal model -/

namespace TwoNormalSamplesU

variable
  {m : ℕ}
  {X : Fin (unequalFixedDifferenceFourResidualDF1 m + 1) → Ω → ℝ}
  {Y : Fin (unequalFixedDifferenceFourResidualDF2 m + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

theorem
    ae_eq_unequalFixedDifferenceFourCanonicalR_rawGraybillDealWeight
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      unequalFixedDifferenceFourCanonicalR m
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω))
      =ᵐ[P]
    unequalFixedDifferenceFourRawGraybillDealWeight m X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourNormalRawL hm hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourRawMeanVarianceSum
        hm hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourCanonicalR_eq_rawGraybillDealWeight
      hm hv₁ hv₂ hL hA

theorem
    ae_eq_unequalFixedDifferenceFourCanonicalQ_rawQuadraticStatistic
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      unequalFixedDifferenceFourCanonicalQ m
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y ω))
      =ᵐ[P]
    unequalFixedDifferenceFourRawQuadraticStatistic m X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourNormalRawL hm hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourRawMeanVarianceSum
        hm hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourCanonicalQ_eq_rawQuadraticStatistic
      hm hv₁ hv₂ hL hA

theorem
    ae_eq_unequalFixedDifferenceFourCanonicalClippedWeight_raw
    (ε : ℝ)
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      unequalFixedDifferenceFourCanonicalClippedWeight m ε
        (oracleVarianceWeightU
          (unequalFixedDifferenceFourResidualDF1 m)
          (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
        (unequalFixedDifferenceFourNormalRawP m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawL m v₁ v₂ X Y ω)
        (unequalFixedDifferenceFourNormalRawV m v₁ v₂ X Y ω))
      =ᵐ[P]
    unequalFixedDifferenceFourRawClippedPerturbedWeight
      ε m X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourNormalRawL hm hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourRawMeanVarianceSum
        hm hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourCanonicalClippedWeight_eq_rawClippedPerturbedWeight
      hm hv₁ hv₂ hL hA

theorem
    ae_eq_unequalFixedDifferenceFourCanonicalBaseEstimator_raw
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      μ
        + unequalFixedDifferenceFourOracleCenteredError
            m μ v₁ v₂ X Y ω
        + meanDifferenceU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) X Y ω
          * (unequalFixedDifferenceFourCanonicalR m
                (oracleVarianceWeightU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
                (unequalFixedDifferenceFourNormalRawP
                  m v₁ v₂ X Y ω)
              - oracleVarianceWeightU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂))
      =ᵐ[P]
    unequalFixedDifferenceFourRawGraybillDealEstimator m X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourNormalRawL hm hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourRawMeanVarianceSum
        hm hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourCanonicalBaseEstimator_eq_rawGraybillDealEstimator
      hm hv₁ hv₂ hL hA

theorem
    ae_eq_unequalFixedDifferenceFourCanonicalClippedEstimator_raw
    (ε : ℝ)
    (h : TwoNormalSamplesU
      (unequalFixedDifferenceFourResidualDF1 m)
      (unequalFixedDifferenceFourResidualDF2 m)
      X Y P μ v₁ v₂)
    (hm : 7 ≤ m)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    (fun ω =>
      μ
        + unequalFixedDifferenceFourOracleCenteredError
            m μ v₁ v₂ X Y ω
        + meanDifferenceU
            (unequalFixedDifferenceFourResidualDF1 m)
            (unequalFixedDifferenceFourResidualDF2 m) X Y ω
          * (unequalFixedDifferenceFourCanonicalClippedWeight m ε
                (oracleVarianceWeightU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂)
                (unequalFixedDifferenceFourNormalRawP
                  m v₁ v₂ X Y ω)
                (unequalFixedDifferenceFourNormalRawL
                  m v₁ v₂ X Y ω)
                (unequalFixedDifferenceFourNormalRawV
                  m v₁ v₂ X Y ω)
              - oracleVarianceWeightU
                  (unequalFixedDifferenceFourResidualDF1 m)
                  (unequalFixedDifferenceFourResidualDF2 m) v₁ v₂))
      =ᵐ[P]
    unequalFixedDifferenceFourRawClippedPerturbedEstimator
      ε m X Y := by
  filter_upwards
    [h.ae_ne_unequalFixedDifferenceFourNormalRawL hm hv₁ hv₂,
      h.ae_ne_unequalFixedDifferenceFourRawMeanVarianceSum
        hm hv₁ hv₂] with ω hL hA
  exact
    unequalFixedDifferenceFourCanonicalClippedEstimator_eq_rawClippedPerturbedEstimator
      hm hv₁ hv₂ hL hA

end TwoNormalSamplesU

end

end GraybillDeal
