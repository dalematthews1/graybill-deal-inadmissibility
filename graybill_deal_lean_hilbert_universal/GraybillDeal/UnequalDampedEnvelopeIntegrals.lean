import GraybillDeal.UnequalDampedSeriesPointwise
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic.FunProp

/-!
# Exact quadratic-envelope integrals for the unequal damped certificate

The one-sided quadratic estimate in
`UnequalDampedCoordinates` leaves a beta expectation of

`(16/49) * y²/(1-y)² * (c² + (245/13)/(1-y)²)`.

On the original side `Y ~ Beta(8,6)` and on the sample-swapped side
`Y ~ Beta(6,8)`.  Their polynomial densities cancel all apparent endpoint
singularities.  This file evaluates the two resulting integrals exactly and
then combines those evaluations with the pointwise `C` envelopes.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The smaller sample-swapped quadratic-envelope constant. -/
def unequalDampedMMinus : ℝ := 20921716 / 405769

/-- The common envelope factor before multiplication by a beta density. -/
def unequalDampedEnvelopeFactor (y : ℝ) : ℝ :=
  (16 / 49) * (y ^ 2 / (1 - y) ^ 2)
    * (unequalDampedC13_17 ^ 2 + (245 / 13) / (1 - y) ^ 2)

/-- The `Beta(8,6)` density times the quadratic envelope. -/
def unequalDampedPlusEnvelopeIntegrand (y : ℝ) : ℝ :=
  unequalDampedPlusDensity y * unequalDampedEnvelopeFactor y

/-- The `Beta(6,8)` density times the quadratic envelope. -/
def unequalDampedMinusEnvelopeIntegrand (y : ℝ) : ℝ :=
  unequalDampedMinusDensity y * unequalDampedEnvelopeFactor y

/--
The polynomial extension of the plus-side envelope integrand.  It is useful
to record this expanded form because it is continuous at `y=1`.
-/
def unequalDampedPlusEnvelopePolynomial (y : ℝ) : ℝ :=
  (-1144284768 / 31213) * y ^ 12
    + (3432854304 / 31213) * y ^ 11
    - (5410509984 / 31213) * y ^ 10
    + (3121940448 / 31213) * y ^ 9

/-- The polynomial extension of the swapped-side envelope integrand. -/
def unequalDampedMinusEnvelopePolynomial (y : ℝ) : ℝ :=
  (-1144284768 / 31213) * y ^ 12
    + (5721423840 / 31213) * y ^ 11
    - (13420503360 / 31213) * y ^ 10
    + (17375814720 / 31213) * y ^ 9
    - (11654390880 / 31213) * y ^ 8
    + (3121940448 / 31213) * y ^ 7

theorem unequalDampedPlusEnvelopeIntegrand_eq_polynomial (y : ℝ) :
    unequalDampedPlusEnvelopeIntegrand y
      = unequalDampedPlusEnvelopePolynomial y := by
  by_cases hy : y = 1
  · subst y
    norm_num [unequalDampedPlusEnvelopeIntegrand,
      unequalDampedPlusEnvelopePolynomial, unequalDampedEnvelopeFactor,
      unequalDampedPlusDensity]
  · have hden : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    unfold unequalDampedPlusEnvelopeIntegrand
      unequalDampedPlusEnvelopePolynomial unequalDampedEnvelopeFactor
      unequalDampedPlusDensity unequalDampedC13_17
    field_simp [hden]
    ring

theorem unequalDampedMinusEnvelopeIntegrand_eq_polynomial (y : ℝ) :
    unequalDampedMinusEnvelopeIntegrand y
      = unequalDampedMinusEnvelopePolynomial y := by
  by_cases hy : y = 1
  · subst y
    norm_num [unequalDampedMinusEnvelopeIntegrand,
      unequalDampedMinusEnvelopePolynomial, unequalDampedEnvelopeFactor,
      unequalDampedMinusDensity]
  · have hden : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    unfold unequalDampedMinusEnvelopeIntegrand
      unequalDampedMinusEnvelopePolynomial unequalDampedEnvelopeFactor
      unequalDampedMinusDensity unequalDampedC13_17
    field_simp [hden]
    ring

private theorem unequalDampedPlusEnvelopePolynomial_integral :
    (∫ y in (0 : ℝ)..1, unequalDampedPlusEnvelopePolynomial y)
      = unequalDampedMPlus := by
  let F : ℝ → ℝ := fun y =>
    (-1144284768 / 405769) * y ^ 13
      + (286071192 / 31213) * y ^ 12
      - (491864544 / 31213) * y ^ 11
      + (1560970224 / 156065) * y ^ 10
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F)
    (by
      intro y hy
      dsimp [F]
      have h13 :=
        (hasDerivAt_pow 13 y).const_mul
          (-1144284768 / 405769 : ℝ)
      have h12 :=
        (hasDerivAt_pow 12 y).const_mul
          (286071192 / 31213 : ℝ)
      have h11 :=
        (hasDerivAt_pow 11 y).const_mul
          (491864544 / 31213 : ℝ)
      have h10 :=
        (hasDerivAt_pow 10 y).const_mul
          (1560970224 / 156065 : ℝ)
      have hderiv := ((h13.add h12).sub h11).add h10
      convert hderiv using 1
      · funext z
        simp only [Pi.add_apply, Pi.sub_apply]
      · unfold unequalDampedPlusEnvelopePolynomial
        norm_num
        ring)
    ((by
      unfold unequalDampedPlusEnvelopePolynomial
      fun_prop :
        Continuous unequalDampedPlusEnvelopePolynomial).intervalIntegrable
          0 1)]
  norm_num [F, unequalDampedMPlus]

private theorem unequalDampedMinusEnvelopePolynomial_integral :
    (∫ y in (0 : ℝ)..1, unequalDampedMinusEnvelopePolynomial y)
      = unequalDampedMMinus := by
  let F : ℝ → ℝ := fun y =>
    (-1144284768 / 405769) * y ^ 13
      + (476785320 / 31213) * y ^ 12
      - (1220045760 / 31213) * y ^ 11
      + (1737581472 / 31213) * y ^ 10
      - (1294932320 / 31213) * y ^ 9
      + (390242556 / 31213) * y ^ 8
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F)
    (by
      intro y hy
      dsimp [F]
      have h13 :=
        (hasDerivAt_pow 13 y).const_mul
          (-1144284768 / 405769 : ℝ)
      have h12 :=
        (hasDerivAt_pow 12 y).const_mul
          (476785320 / 31213 : ℝ)
      have h11 :=
        (hasDerivAt_pow 11 y).const_mul
          (1220045760 / 31213 : ℝ)
      have h10 :=
        (hasDerivAt_pow 10 y).const_mul
          (1737581472 / 31213 : ℝ)
      have h9 :=
        (hasDerivAt_pow 9 y).const_mul
          (1294932320 / 31213 : ℝ)
      have h8 :=
        (hasDerivAt_pow 8 y).const_mul
          (390242556 / 31213 : ℝ)
      have hderiv :=
        ((((h13.add h12).sub h11).add h10).sub h9).add h8
      convert hderiv using 1
      · funext z
        simp only [Pi.add_apply, Pi.sub_apply]
      · unfold unequalDampedMinusEnvelopePolynomial
        norm_num
        ring)
    ((by
      unfold unequalDampedMinusEnvelopePolynomial
      fun_prop :
        Continuous unequalDampedMinusEnvelopePolynomial).intervalIntegrable
          0 1)]
  norm_num [F, unequalDampedMMinus]

/-- Exact `Beta(8,6)` polynomial-density envelope integral. -/
theorem unequalDampedPlusEnvelopeIntegral :
    (∫ y in (0 : ℝ)..1, unequalDampedPlusEnvelopeIntegrand y)
      = unequalDampedMPlus := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedPlusEnvelopeIntegrand y)
        =
      ∫ y in (0 : ℝ)..1, unequalDampedPlusEnvelopePolynomial y := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact unequalDampedPlusEnvelopeIntegrand_eq_polynomial y
    _ = unequalDampedMPlus :=
      unequalDampedPlusEnvelopePolynomial_integral

/-- Exact `Beta(6,8)` polynomial-density envelope integral. -/
theorem unequalDampedMinusEnvelopeIntegral :
    (∫ y in (0 : ℝ)..1, unequalDampedMinusEnvelopeIntegrand y)
      = unequalDampedMMinus := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedMinusEnvelopeIntegrand y)
        =
      ∫ y in (0 : ℝ)..1, unequalDampedMinusEnvelopePolynomial y := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact unequalDampedMinusEnvelopeIntegrand_eq_polynomial y
    _ = unequalDampedMMinus :=
      unequalDampedMinusEnvelopePolynomial_integral

theorem unequalDampedMMinus_pos :
    0 < unequalDampedMMinus := by
  norm_num [unequalDampedMMinus]

/-- The swapped-side constant is bounded by the common plus-side constant. -/
theorem unequalDampedMMinus_le_MPlus :
    unequalDampedMMinus ≤ unequalDampedMPlus := by
  norm_num [unequalDampedMMinus, unequalDampedMPlus]

private theorem beta_eight_six :
    ProbabilityTheory.beta 8 6 = (1 / 10296 : ℝ) := by
  unfold ProbabilityTheory.beta
  norm_num [Real.Gamma_ofNat_eq_factorial]

private theorem beta_six_eight :
    ProbabilityTheory.beta 6 8 = (1 / 10296 : ℝ) := by
  unfold ProbabilityTheory.beta
  norm_num [Real.Gamma_ofNat_eq_factorial]

theorem betaPDF_eight_six_toReal (y : ℝ) :
    (betaPDF 8 6 y).toReal =
      if 0 < y ∧ y < 1 then unequalDampedPlusDensity y else 0 := by
  by_cases hy : 0 < y ∧ y < 1
  · rw [betaPDF, betaPDFReal, if_pos hy, ENNReal.toReal_ofReal, if_pos hy]
    · rw [beta_eight_six]
      have hseven : (8 : ℝ) - 1 = 7 := by norm_num
      have hfive : (6 : ℝ) - 1 = 5 := by norm_num
      rw [hseven, hfive]
      change
        (1 / (1 / 10296 : ℝ)) * y ^ (7 : ℝ) * (1 - y) ^ (5 : ℝ)
          = unequalDampedPlusDensity y
      norm_num [unequalDampedPlusDensity]
    · exact le_of_lt <| mul_pos
        (mul_pos (one_div_pos.mpr (beta_pos (by norm_num) (by norm_num)))
          (Real.rpow_pos_of_pos hy.1 _))
        (Real.rpow_pos_of_pos (sub_pos.mpr hy.2) _)
  · simp [betaPDF, betaPDFReal, hy]

theorem betaPDF_six_eight_toReal (y : ℝ) :
    (betaPDF 6 8 y).toReal =
      if 0 < y ∧ y < 1 then unequalDampedMinusDensity y else 0 := by
  by_cases hy : 0 < y ∧ y < 1
  · rw [betaPDF, betaPDFReal, if_pos hy, ENNReal.toReal_ofReal, if_pos hy]
    · rw [beta_six_eight]
      have hfive : (6 : ℝ) - 1 = 5 := by norm_num
      have hseven : (8 : ℝ) - 1 = 7 := by norm_num
      rw [hfive, hseven]
      change
        (1 / (1 / 10296 : ℝ)) * y ^ (5 : ℝ) * (1 - y) ^ (7 : ℝ)
          = unequalDampedMinusDensity y
      norm_num [unequalDampedMinusDensity]
    · exact le_of_lt <| mul_pos
        (mul_pos (one_div_pos.mpr (beta_pos (by norm_num) (by norm_num)))
          (Real.rpow_pos_of_pos hy.1 _))
        (Real.rpow_pos_of_pos (sub_pos.mpr hy.2) _)
  · simp [betaPDF, betaPDFReal, hy]

/-- Ordinary-density bridge for `Beta(8,6)`. -/
theorem integral_betaMeasure_eight_six_eq_interval
    (f : ℝ → ℝ) :
    (∫ y, f y ∂betaMeasure 8 6)
      =
    ∫ y in (0 : ℝ)..1, unequalDampedPlusDensity y * f y := by
  rw [betaMeasure]
  unfold betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_betaPDFReal 8 6).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  calc
    (∫ y, (betaPDF 8 6 y).toReal * f y)
        =
      ∫ y, (Ioo (0 : ℝ) 1).indicator
        (fun z => unequalDampedPlusDensity z * f z) y := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [betaPDF_eight_six_toReal]
          by_cases hy : y ∈ Ioo (0 : ℝ) 1
          · simp only [mem_Ioo] at hy
            simp [hy]
          · have hy' : ¬ (0 < y ∧ y < 1) := by
              simpa only [mem_Ioo] using hy
            simp [hy, hy']
    _ =
      ∫ y in Ioo (0 : ℝ) 1,
        unequalDampedPlusDensity y * f y :=
      integral_indicator measurableSet_Ioo
    _ =
      ∫ y in Ioc (0 : ℝ) 1,
        unequalDampedPlusDensity y * f y := by
          apply setIntegral_congr_set
          exact Ioo_ae_eq_Ioc
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalDampedPlusDensity y * f y := by
          rw [intervalIntegral.integral_of_le (by norm_num)]

/-- Ordinary-density bridge for `Beta(6,8)`. -/
theorem integral_betaMeasure_six_eight_eq_interval
    (f : ℝ → ℝ) :
    (∫ y, f y ∂betaMeasure 6 8)
      =
    ∫ y in (0 : ℝ)..1, unequalDampedMinusDensity y * f y := by
  rw [betaMeasure]
  unfold betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_betaPDFReal 6 8).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  calc
    (∫ y, (betaPDF 6 8 y).toReal * f y)
        =
      ∫ y, (Ioo (0 : ℝ) 1).indicator
        (fun z => unequalDampedMinusDensity z * f z) y := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [betaPDF_six_eight_toReal]
          by_cases hy : y ∈ Ioo (0 : ℝ) 1
          · simp only [mem_Ioo] at hy
            simp [hy]
          · have hy' : ¬ (0 < y ∧ y < 1) := by
              simpa only [mem_Ioo] using hy
            simp [hy, hy']
    _ =
      ∫ y in Ioo (0 : ℝ) 1,
        unequalDampedMinusDensity y * f y :=
      integral_indicator measurableSet_Ioo
    _ =
      ∫ y in Ioc (0 : ℝ) 1,
        unequalDampedMinusDensity y * f y := by
          apply setIntegral_congr_set
          exact Ioo_ae_eq_Ioc
    _ =
      ∫ y in (0 : ℝ)..1,
        unequalDampedMinusDensity y * f y := by
          rw [intervalIntegral.integral_of_le (by norm_num)]

/-- The exact envelope expectation under `Beta(8,6)`. -/
theorem integral_unequalDampedEnvelope_beta_eight_six :
    (∫ y, unequalDampedEnvelopeFactor y ∂betaMeasure 8 6)
      = unequalDampedMPlus := by
  rw [integral_betaMeasure_eight_six_eq_interval]
  exact unequalDampedPlusEnvelopeIntegral

/-- The exact envelope expectation under `Beta(6,8)`. -/
theorem integral_unequalDampedEnvelope_beta_six_eight :
    (∫ y, unequalDampedEnvelopeFactor y ∂betaMeasure 6 8)
      = unequalDampedMMinus := by
  rw [integral_betaMeasure_six_eight_eq_interval]
  exact unequalDampedMinusEnvelopeIntegral

/-- A beta-density-weighted original-side `C` integrand. -/
def unequalDampedPlusCIntegrand (s y : ℝ) : ℝ :=
  unequalDampedPlusDensity y
    * (unequalDampedPhi (3 / 7) unequalDampedKappa13_17
          (unequalDampedR s y) ^ 2
        * unequalDampedCKernel13_17 (unequalDampedU (4 / 7) s y))

/-- A beta-density-weighted swapped-side `C` integrand. -/
def unequalDampedMinusCIntegrand (s y : ℝ) : ℝ :=
  unequalDampedMinusDensity y
    * (unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
          (unequalDampedR s y) ^ 2
        * unequalDampedCKernel13_17 (unequalDampedU (3 / 7) s y))

private theorem unequalDampedR_continuousOn
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ContinuousOn (unequalDampedR s) (Icc (0 : ℝ) 1) := by
  have hden :
      ∀ y ∈ Icc (0 : ℝ) 1, unequalDampedDenom s y ≠ 0 := by
    intro y hy
    exact ne_of_gt
      (unequalDampedDenom_pos hs0 hs1 hy.1 hy.2)
  unfold unequalDampedR unequalDampedDenom
  exact
    (continuous_const.sub continuous_id).continuousOn.div
      (continuous_const.sub
        (continuous_const.mul continuous_id)).continuousOn hden

private theorem unequalDampedU_continuousOn
    (q : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ContinuousOn (fun y => unequalDampedU q s y) (Icc (0 : ℝ) 1) := by
  have hden :
      ∀ y ∈ Icc (0 : ℝ) 1, unequalDampedDenom s y ≠ 0 := by
    intro y hy
    exact ne_of_gt
      (unequalDampedDenom_pos hs0 hs1 hy.1 hy.2)
  unfold unequalDampedU unequalDampedDenom
  exact
    continuous_const.continuousOn.div
      (continuous_const.sub
        (continuous_const.mul continuous_id)).continuousOn hden

private theorem unequalDampedPhi_comp_continuousOn
    (t κ : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ContinuousOn
      (fun y => unequalDampedPhi t κ (unequalDampedR s y))
      (Icc (0 : ℝ) 1) := by
  have hr := unequalDampedR_continuousOn hs0 hs1
  unfold unequalDampedPhi unequalDampedInner
  exact
    (hr.mul (continuous_const.continuousOn.sub hr)).mul
      ((continuous_const.continuousOn.sub hr).add
        ((continuous_const.continuousOn.mul hr).mul
          (continuous_const.continuousOn.sub hr)))

private theorem unequalDampedCKernel_comp_continuousOn
    (q : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ContinuousOn
      (fun y => unequalDampedCKernel13_17 (unequalDampedU q s y))
      (Icc (0 : ℝ) 1) := by
  have hu := unequalDampedU_continuousOn q hs0 hs1
  unfold unequalDampedCKernel13_17
  exact
    (continuous_const.continuousOn.sub
      (continuous_const.continuousOn.mul hu)).add
      (continuous_const.continuousOn.mul (hu.pow 2))

private theorem unequalDampedPlusCIntegrand_intervalIntegrable
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    IntervalIntegrable (unequalDampedPlusCIntegrand s) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  unfold unequalDampedPlusCIntegrand
  have hdensity :
      Continuous unequalDampedPlusDensity := by
    unfold unequalDampedPlusDensity
    fun_prop
  have hphi :=
    (unequalDampedPhi_comp_continuousOn
      (3 / 7) unequalDampedKappa13_17 hs0 hs1).pow 2
  have hkernel :=
    unequalDampedCKernel_comp_continuousOn (4 / 7) hs0 hs1
  exact hdensity.continuousOn.mul (hphi.mul hkernel)

private theorem unequalDampedMinusCIntegrand_intervalIntegrable
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    IntervalIntegrable (unequalDampedMinusCIntegrand s) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  unfold unequalDampedMinusCIntegrand
  have hdensity :
      Continuous unequalDampedMinusDensity := by
    unfold unequalDampedMinusDensity
    fun_prop
  have hphi :=
    (unequalDampedPhi_comp_continuousOn
      (4 / 7) (-unequalDampedKappa13_17) hs0 hs1).pow 2
  have hkernel :=
    unequalDampedCKernel_comp_continuousOn (3 / 7) hs0 hs1
  exact hdensity.continuousOn.mul (hphi.mul hkernel)

private theorem unequalDampedPlusEnvelopeIntegrand_intervalIntegrable :
    IntervalIntegrable unequalDampedPlusEnvelopeIntegrand volume 0 1 := by
  rw [show unequalDampedPlusEnvelopeIntegrand
      = unequalDampedPlusEnvelopePolynomial by
    funext y
    exact unequalDampedPlusEnvelopeIntegrand_eq_polynomial y]
  exact
    (by
      unfold unequalDampedPlusEnvelopePolynomial
      fun_prop :
        Continuous unequalDampedPlusEnvelopePolynomial).intervalIntegrable
      0 1

private theorem unequalDampedMinusEnvelopeIntegrand_intervalIntegrable :
    IntervalIntegrable unequalDampedMinusEnvelopeIntegrand volume 0 1 := by
  rw [show unequalDampedMinusEnvelopeIntegrand
      = unequalDampedMinusEnvelopePolynomial by
    funext y
    exact unequalDampedMinusEnvelopeIntegrand_eq_polynomial y]
  exact
    (by
      unfold unequalDampedMinusEnvelopePolynomial
      fun_prop :
        Continuous unequalDampedMinusEnvelopePolynomial).intervalIntegrable
      0 1

/--
Integrating the original-side pointwise envelope yields the exact common
quadratic bound.
-/
theorem integral_unequalDampedPlusC_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y in (0 : ℝ)..1, unequalDampedPlusCIntegrand s y)
      ≤ unequalDampedMPlus * (1 - s) ^ 2 := by
  have hraw :=
    unequalDampedPlusCIntegrand_intervalIntegrable hs0 hs1
  have henv :=
    unequalDampedPlusEnvelopeIntegrand_intervalIntegrable
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedPlusCIntegrand s y)
        ≤
      ∫ y in (0 : ℝ)..1,
        (1 - s) ^ 2 * unequalDampedPlusEnvelopeIntegrand y := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo
            (by norm_num) hraw (henv.const_mul ((1 - s) ^ 2))
          intro y hy
          have hpoint :=
            unequalDampedC_pointwise_le_envelope13_17
              hs0 hs1 hy.1.le hy.2
          have hdensity : 0 ≤ unequalDampedPlusDensity y := by
            unfold unequalDampedPlusDensity
            exact mul_nonneg
              (mul_nonneg (by norm_num) (pow_nonneg hy.1.le 7))
              (pow_nonneg (sub_nonneg.mpr hy.2.le) 5)
          have hmul :=
            mul_le_mul_of_nonneg_left hpoint hdensity
          calc
            unequalDampedPlusCIntegrand s y
                ≤
              unequalDampedPlusDensity y
                * ((1 - s) ^ 2 * (16 / 49)
                  * (y ^ 2 / (1 - y) ^ 2)
                  * (unequalDampedC13_17 ^ 2
                    + (245 / 13) / (1 - y) ^ 2)) := by
                      exact hmul
            _ =
              (1 - s) ^ 2
                * unequalDampedPlusEnvelopeIntegrand y := by
                  unfold unequalDampedPlusEnvelopeIntegrand
                    unequalDampedEnvelopeFactor
                  ring
    _ = (1 - s) ^ 2 * unequalDampedMPlus := by
      rw [intervalIntegral.integral_const_mul,
        unequalDampedPlusEnvelopeIntegral]
    _ = unequalDampedMPlus * (1 - s) ^ 2 := by ring

/--
The swapped-side pointwise envelope first yields its smaller exact constant.
-/
theorem integral_unequalDampedMinusC_le_MMinus
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y in (0 : ℝ)..1, unequalDampedMinusCIntegrand s y)
      ≤ unequalDampedMMinus * (1 - s) ^ 2 := by
  have hraw :=
    unequalDampedMinusCIntegrand_intervalIntegrable hs0 hs1
  have henv :=
    unequalDampedMinusEnvelopeIntegrand_intervalIntegrable
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedMinusCIntegrand s y)
        ≤
      ∫ y in (0 : ℝ)..1,
        (1 - s) ^ 2 * unequalDampedMinusEnvelopeIntegrand y := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo
            (by norm_num) hraw (henv.const_mul ((1 - s) ^ 2))
          intro y hy
          have hpoint :=
            unequalDampedC_pointwise_le_envelope17_13
              hs0 hs1 hy.1.le hy.2
          have hdensity : 0 ≤ unequalDampedMinusDensity y := by
            unfold unequalDampedMinusDensity
            exact mul_nonneg
              (mul_nonneg (by norm_num) (pow_nonneg hy.1.le 5))
              (pow_nonneg (sub_nonneg.mpr hy.2.le) 7)
          have hmul :=
            mul_le_mul_of_nonneg_left hpoint hdensity
          calc
            unequalDampedMinusCIntegrand s y
                ≤
              unequalDampedMinusDensity y
                * ((1 - s) ^ 2 * (16 / 49)
                  * (y ^ 2 / (1 - y) ^ 2)
                  * (unequalDampedC13_17 ^ 2
                    + (245 / 13) / (1 - y) ^ 2)) := by
                      exact hmul
            _ =
              (1 - s) ^ 2
                * unequalDampedMinusEnvelopeIntegrand y := by
                  unfold unequalDampedMinusEnvelopeIntegrand
                    unequalDampedEnvelopeFactor
                  ring
    _ = (1 - s) ^ 2 * unequalDampedMMinus := by
      rw [intervalIntegral.integral_const_mul,
        unequalDampedMinusEnvelopeIntegral]
    _ = unequalDampedMMinus * (1 - s) ^ 2 := by ring

/-- The common `M₊` also bounds the swapped-side quadratic integral. -/
theorem integral_unequalDampedMinusC_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y in (0 : ℝ)..1, unequalDampedMinusCIntegrand s y)
      ≤ unequalDampedMPlus * (1 - s) ^ 2 := by
  calc
    (∫ y in (0 : ℝ)..1, unequalDampedMinusCIntegrand s y)
        ≤ unequalDampedMMinus * (1 - s) ^ 2 :=
      integral_unequalDampedMinusC_le_MMinus hs0 hs1
    _ ≤ unequalDampedMPlus * (1 - s) ^ 2 :=
      mul_le_mul_of_nonneg_right unequalDampedMMinus_le_MPlus
        (sq_nonneg (1 - s))

/--
Probability-law form of the original-side quadratic estimate.
-/
theorem integral_unequalDampedPlusC_beta_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y,
      unequalDampedPhi (3 / 7) unequalDampedKappa13_17
          (unequalDampedR s y) ^ 2
        * unequalDampedCKernel13_17 (unequalDampedU (4 / 7) s y)
      ∂betaMeasure 8 6)
      ≤ unequalDampedMPlus * (1 - s) ^ 2 := by
  rw [integral_betaMeasure_eight_six_eq_interval]
  exact integral_unequalDampedPlusC_le hs0 hs1

/--
Probability-law form of the swapped-side quadratic estimate.
-/
theorem integral_unequalDampedMinusC_beta_le
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ y,
      unequalDampedPhi (4 / 7) (-unequalDampedKappa13_17)
          (unequalDampedR s y) ^ 2
        * unequalDampedCKernel13_17 (unequalDampedU (3 / 7) s y)
      ∂betaMeasure 6 8)
      ≤ unequalDampedMPlus * (1 - s) ^ 2 := by
  rw [integral_betaMeasure_six_eight_eq_interval]
  exact integral_unequalDampedMinusC_le hs0 hs1

end

end GraybillDeal
