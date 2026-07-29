import GraybillDeal.UnequalDampedSeriesPointwise
import GraybillDeal.SeriesIntegration

/-!
# Termwise integration for the damped unequal-size series

The four collected polynomial prefactors are uniformly bounded on the unit
interval.  Combining that compactness bound with the order-five
negative-binomial coefficients gives a summable geometric majorant.  This
file applies `hasSum_intervalIntegral_of_uniform_majorant` and records the
result for both one-sided `(13,17)` beta integrals.

Exact evaluation of the integrated coefficients is deliberately left to a
later layer.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/--
The continuous factor that remains after removing the common
negative-binomial coefficient and the power `s^n`.
-/
def unequalDampedSeriesEnvelope
    (density : ℝ → ℝ) (t q κ c k y : ℝ) : ℝ :=
  ‖density y‖
    * (‖unequalDampedG0 q κ c k y‖
      + ‖unequalDampedG1 t q κ c k y‖
      + ‖unequalDampedG2 t q κ c k y‖
      + ‖unequalDampedG3 t q c k y‖)

/-- The geometric majorant associated to an envelope bound `K`. -/
def unequalDampedSeriesMajorant (K s : ℝ) (n : ℕ) : ℝ :=
  K * ((n + 5).choose 5 : ℝ) * s ^ n

theorem continuous_unequalDampedSeriesEnvelope
    {density : ℝ → ℝ} (hdensity : Continuous density)
    (t q κ c k : ℝ) :
    Continuous (unequalDampedSeriesEnvelope density t q κ c k) := by
  unfold unequalDampedSeriesEnvelope unequalDampedG0 unequalDampedG1
    unequalDampedG2 unequalDampedG3 unequalDampedWBar
    unequalDampedF0 unequalDampedF1Hat unequalDampedPsi0
    unequalDampedPsi1
  fun_prop

/--
Continuity supplies one nonnegative envelope constant on `[0,1]`.
-/
theorem exists_unequalDampedSeriesEnvelope_bound
    {density : ℝ → ℝ} (hdensity : Continuous density)
    (t q κ c k : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ Icc (0 : ℝ) 1,
        unequalDampedSeriesEnvelope density t q κ c k y ≤ K := by
  have hcont :=
    continuous_unequalDampedSeriesEnvelope hdensity t q κ c k
  obtain ⟨K, hK⟩ :=
    bddAbove_def.mp
      (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max K 0, le_max_right K 0, ?_⟩
  intro y hy
  have himage :
      unequalDampedSeriesEnvelope density t q κ c k y
        ∈ unequalDampedSeriesEnvelope density t q κ c k ''
          Icc (0 : ℝ) 1 :=
    ⟨y, hy, rfl⟩
  exact (hK _ himage).trans (le_max_left K 0)

theorem unequalBinomialC_le_unshifted
    {s y : ℝ} (hs0 : 0 ≤ s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (n : ℕ) :
    0 ≤ unequalBinomialC0 (s * y) n ∧
    unequalBinomialC0 (s * y) n
      ≤ ((n + 5).choose 5 : ℝ) * s ^ n ∧
    0 ≤ unequalBinomialC1 (s * y) n ∧
    unequalBinomialC1 (s * y) n
      ≤ ((n + 5).choose 5 : ℝ) * s ^ n ∧
    0 ≤ unequalBinomialC2 (s * y) n ∧
    unequalBinomialC2 (s * y) n
      ≤ ((n + 5).choose 5 : ℝ) * s ^ n ∧
    0 ≤ unequalBinomialC3 (s * y) n ∧
    unequalBinomialC3 (s * y) n
      ≤ ((n + 5).choose 5 : ℝ) * s ^ n := by
  have hsy0 : 0 ≤ s * y := mul_nonneg hs0 hy0
  have hsy_le : s * y ≤ s := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hy1)]
  have hpow : (s * y) ^ n ≤ s ^ n :=
    pow_le_pow_left₀ hsy0 hsy_le n
  have hc1 :
      ((n + 4).choose 5 : ℝ) ≤ ((n + 5).choose 5 : ℝ) := by
    exact_mod_cast Nat.choose_le_choose 5 (by omega)
  have hc2 :
      ((n + 3).choose 5 : ℝ) ≤ ((n + 5).choose 5 : ℝ) := by
    exact_mod_cast Nat.choose_le_choose 5 (by omega)
  have hc3 :
      ((n + 2).choose 5 : ℝ) ≤ ((n + 5).choose 5 : ℝ) := by
    exact_mod_cast Nat.choose_le_choose 5 (by omega)
  constructor
  · unfold unequalBinomialC0
    positivity
  constructor
  · unfold unequalBinomialC0
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  constructor
  · unfold unequalBinomialC1
    positivity
  constructor
  · unfold unequalBinomialC1
    exact mul_le_mul hc1 hpow (pow_nonneg hsy0 n) (by positivity)
  constructor
  · unfold unequalBinomialC2
    positivity
  constructor
  · unfold unequalBinomialC2
    exact mul_le_mul hc2 hpow (pow_nonneg hsy0 n) (by positivity)
  constructor
  · unfold unequalBinomialC3
    positivity
  · unfold unequalBinomialC3
    exact mul_le_mul hc3 hpow (pow_nonneg hsy0 n) (by positivity)

/--
The target-indexed pointwise summand is bounded by the geometric majorant.
-/
theorem unequalDampedPointwiseSeriesTerm_norm_le
    {density : ℝ → ℝ} {t q κ c k s y K : ℝ}
    (hs0 : 0 ≤ s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hK :
      unequalDampedSeriesEnvelope density t q κ c k y ≤ K)
    (n : ℕ) :
    ‖unequalDampedPointwiseSeriesTerm
        density t q κ c k s y n‖
      ≤ unequalDampedSeriesMajorant K s n := by
  obtain ⟨hC0_nonneg, hC0_le, hC1_nonneg, hC1_le,
      hC2_nonneg, hC2_le, hC3_nonneg, hC3_le⟩ :=
    unequalBinomialC_le_unshifted hs0 hy0 hy1 n
  let B : ℝ := ((n + 5).choose 5 : ℝ) * s ^ n
  have hB0 : 0 ≤ B := by
    unfold B
    positivity
  let a :=
    unequalDampedG0 q κ c k y * unequalBinomialC0 (s * y) n
  let b :=
    unequalDampedG1 t q κ c k y * unequalBinomialC1 (s * y) n
  let d :=
    unequalDampedG2 t q κ c k y * unequalBinomialC2 (s * y) n
  let e :=
    unequalDampedG3 t q c k y * unequalBinomialC3 (s * y) n
  have ha :
      ‖a‖ ≤ ‖unequalDampedG0 q κ c k y‖ * B := by
    unfold a B
    rw [norm_mul, Real.norm_of_nonneg hC0_nonneg]
    exact mul_le_mul_of_nonneg_left hC0_le (norm_nonneg _)
  have hb :
      ‖b‖ ≤ ‖unequalDampedG1 t q κ c k y‖ * B := by
    unfold b B
    rw [norm_mul, Real.norm_of_nonneg hC1_nonneg]
    exact mul_le_mul_of_nonneg_left hC1_le (norm_nonneg _)
  have hd :
      ‖d‖ ≤ ‖unequalDampedG2 t q κ c k y‖ * B := by
    unfold d B
    rw [norm_mul, Real.norm_of_nonneg hC2_nonneg]
    exact mul_le_mul_of_nonneg_left hC2_le (norm_nonneg _)
  have he :
      ‖e‖ ≤ ‖unequalDampedG3 t q c k y‖ * B := by
    unfold e B
    rw [norm_mul, Real.norm_of_nonneg hC3_nonneg]
    exact mul_le_mul_of_nonneg_left hC3_le (norm_nonneg _)
  have habde :
      ‖a + b + d + e‖
        ≤
      (‖unequalDampedG0 q κ c k y‖
        + ‖unequalDampedG1 t q κ c k y‖
        + ‖unequalDampedG2 t q κ c k y‖
        + ‖unequalDampedG3 t q c k y‖) * B := by
    calc
      ‖a + b + d + e‖
          ≤ (‖a‖ + ‖b‖ + ‖d‖) + ‖e‖ := by
            calc
              ‖a + b + d + e‖ ≤ ‖a + b + d‖ + ‖e‖ :=
                norm_add_le _ _
              _ ≤ (‖a + b‖ + ‖d‖) + ‖e‖ := by
                gcongr
                exact norm_add_le _ _
              _ ≤ (‖a‖ + ‖b‖ + ‖d‖) + ‖e‖ := by
                gcongr
                exact norm_add_le _ _
      _ ≤
          (‖unequalDampedG0 q κ c k y‖ * B
            + ‖unequalDampedG1 t q κ c k y‖ * B
            + ‖unequalDampedG2 t q κ c k y‖ * B)
            + ‖unequalDampedG3 t q c k y‖ * B := by
          gcongr
      _ =
          (‖unequalDampedG0 q κ c k y‖
            + ‖unequalDampedG1 t q κ c k y‖
            + ‖unequalDampedG2 t q κ c k y‖
            + ‖unequalDampedG3 t q c k y‖) * B := by ring
  unfold unequalDampedPointwiseSeriesTerm
  change ‖density y * (a + b + d + e)‖
    ≤ unequalDampedSeriesMajorant K s n
  rw [norm_mul]
  calc
    ‖density y‖ * ‖a + b + d + e‖
        ≤
      ‖density y‖
        * ((‖unequalDampedG0 q κ c k y‖
            + ‖unequalDampedG1 t q κ c k y‖
            + ‖unequalDampedG2 t q κ c k y‖
            + ‖unequalDampedG3 t q c k y‖) * B) := by
          gcongr
    _ = unequalDampedSeriesEnvelope density t q κ c k y * B := by
      unfold unequalDampedSeriesEnvelope
      ring
    _ ≤ K * B := mul_le_mul_of_nonneg_right hK hB0
    _ = unequalDampedSeriesMajorant K s n := by
      unfold B unequalDampedSeriesMajorant
      ring

theorem summable_unequalDampedSeriesMajorant
    {K s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (unequalDampedSeriesMajorant K s) := by
  have hs : ‖s‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs0]
    exact hs1
  have h :=
    (summable_choose_five_mul_geometric hs).mul_left K
  change Summable
    (fun n => K * ((n + 5).choose 5 : ℝ) * s ^ n)
  simpa only [unequalBinomialC0, mul_assoc] using h

/--
Generic termwise integration for a continuous one-sided density.
-/
theorem hasSum_integral_unequalDampedPointwiseSeries
    {density : ℝ → ℝ} (hdensity : Continuous density)
    (t q κ c k : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum
      (fun n =>
        ∫ y in (0 : ℝ)..1,
          unequalDampedPointwiseSeriesTerm
            density t q κ c k s y n)
      (∫ y in (0 : ℝ)..1,
        unequalDampedHIntegrand density t q κ c k s y) := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_unequalDampedSeriesEnvelope_bound
      hdensity t q κ c k
  apply hasSum_intervalIntegral_of_uniform_majorant
    (c := unequalDampedSeriesMajorant K s)
  · intro n
    apply Continuous.continuousOn
    unfold unequalDampedPointwiseSeriesTerm
      unequalBinomialC0 unequalBinomialC1 unequalBinomialC2
      unequalBinomialC3 unequalDampedG0 unequalDampedG1
      unequalDampedG2 unequalDampedG3 unequalDampedWBar
      unequalDampedF0 unequalDampedF1Hat unequalDampedPsi0
      unequalDampedPsi1
    fun_prop
  · intro n y hy
    have hy' : y ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le] using hy
    exact unequalDampedPointwiseSeriesTerm_norm_le
      hs0 hy'.1 hy'.2 (hK y hy') n
  · exact summable_unequalDampedSeriesMajorant hs0 hs1
  · intro y hy
    have hy' : y ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le] using hy
    exact hasSum_unequalDampedPointwiseSeries
      density t q κ c k hs0 hs1 hy'.1 hy'.2

/-- The plus-side analytic integral. -/
def unequalDampedPlusH (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    unequalDampedHIntegrand
      unequalDampedPlusDensity
      (3 / 7) (4 / 7) unequalDampedKappa13_17
      unequalDampedC13_17 unequalDampedK13_17 s y

/-- The swapped-side analytic integral. -/
def unequalDampedMinusH (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1,
    unequalDampedHIntegrand
      unequalDampedMinusDensity
      (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
      unequalDampedC13_17 unequalDampedK13_17 s y

/--
The integrated plus-side pointwise terms sum to the plus-side analytic
integral.
-/
theorem hasSum_integral_unequalDampedPlusPointwiseSeries
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum
      (fun n =>
        ∫ y in (0 : ℝ)..1,
          unequalDampedPointwiseSeriesTerm
            unequalDampedPlusDensity
            (3 / 7) (4 / 7) unequalDampedKappa13_17
            unequalDampedC13_17 unequalDampedK13_17 s y n)
      (unequalDampedPlusH s) := by
  unfold unequalDampedPlusH
  apply hasSum_integral_unequalDampedPointwiseSeries
    (density := unequalDampedPlusDensity)
    (t := 3 / 7) (q := 4 / 7)
    (κ := unequalDampedKappa13_17)
    (c := unequalDampedC13_17) (k := unequalDampedK13_17)
    (s := s) ?_ hs0 hs1
  unfold unequalDampedPlusDensity
  fun_prop

/--
The integrated swapped-side pointwise terms sum to the swapped-side
analytic integral.
-/
theorem hasSum_integral_unequalDampedMinusPointwiseSeries
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum
      (fun n =>
        ∫ y in (0 : ℝ)..1,
          unequalDampedPointwiseSeriesTerm
            unequalDampedMinusDensity
            (4 / 7) (3 / 7) (-unequalDampedKappa13_17)
            unequalDampedC13_17 unequalDampedK13_17 s y n)
      (unequalDampedMinusH s) := by
  unfold unequalDampedMinusH
  apply hasSum_integral_unequalDampedPointwiseSeries
    (density := unequalDampedMinusDensity)
    (t := 4 / 7) (q := 3 / 7)
    (κ := -unequalDampedKappa13_17)
    (c := unequalDampedC13_17) (k := unequalDampedK13_17)
    (s := s) ?_ hs0 hs1
  unfold unequalDampedMinusDensity
  fun_prop

end

end GraybillDeal
