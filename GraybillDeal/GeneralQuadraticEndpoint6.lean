import GraybillDeal.GeneralQuadratic
import GraybillDeal.IntegralPairing
import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The generalized sixth-power endpoint integral

For residual degrees of freedom `ν`, the sixth-power quadratic kernel has
weight `(1-x²)^(ν/2+1)`.  At the endpoint `s = 1` its integrand becomes

`(1-x)^(ν/2+1) * (1+x)^(ν/2-5)`.

This file evaluates the resulting integral and proves that it uniformly
bounds the interior kernels when `ν ≥ 9` and `|s| < 1`.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory Real

noncomputable section

/-- The `s = 1` endpoint version of the generalized sixth-power kernel. -/
def generalEndpointKernel6 (ν x : ℝ) : ℝ :=
  (1 - x) ^ (ν / 2 + 1) * (1 + x) ^ (ν / 2 - 5)

/-- The generalized sixth-power endpoint integral. -/
def generalJ6 (ν : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, generalEndpointKernel6 ν x

private theorem integral_rpow_mul_two_sub_rpow
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (∫ x in (0 : ℝ)..2, x ^ (s - 1) * (2 - x) ^ (t - 1))
      =
    2 ^ (s + t - 1) * beta s t := by
  have hc := Complex.betaIntegral_scaled (s : ℂ) (t : ℂ)
    (show (0 : ℝ) < 2 by norm_num)
  rw [Complex.betaIntegral_eq_Gamma_mul_div (s : ℂ) (t : ℂ)
    (by simpa) (by simpa)] at hc
  rw [← Complex.ofReal_inj, ← intervalIntegral.integral_ofReal]
  calc
    (∫ x in (0 : ℝ)..2,
        ((x ^ (s - 1) * (2 - x) ^ (t - 1) : ℝ) : ℂ))
        =
      ∫ x in (0 : ℝ)..2,
        (x : ℂ) ^ ((s : ℂ) - 1)
          * ((2 : ℂ) - x) ^ ((t : ℂ) - 1) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with x hx
            rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
            rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
              Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
            push_cast
            rfl
    _ =
      (2 : ℂ) ^ ((s : ℂ) + t - 1)
        * (Complex.Gamma (s : ℂ) * Complex.Gamma (t : ℂ)
          / Complex.Gamma ((s : ℂ) + t)) := hc
    _ =
      ((2 ^ (s + t - 1) * beta s t : ℝ) : ℂ) := by
        rw [show (s : ℂ) + t - 1 = ((s + t - 1 : ℝ) : ℂ) by
          push_cast
          rfl]
        change
          ((2 : ℝ) : ℂ) ^ ((s + t - 1 : ℝ) : ℂ)
              * (Complex.Gamma (s : ℂ) * Complex.Gamma (t : ℂ)
                / Complex.Gamma ((s : ℂ) + t))
            =
          ((2 ^ (s + t - 1) * beta s t : ℝ) : ℂ)
        rw [← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [Complex.Gamma_ofReal]
        rw [show (s : ℂ) + t = ((s + t : ℝ) : ℂ) by
          push_cast
          rfl,
          Complex.Gamma_ofReal]
        unfold beta
        push_cast
        rfl

/-- The shifted beta integrand used to evaluate `generalJ6`. -/
private def generalJ6ScaledIntegrand (ν u : ℝ) : ℝ :=
  u ^ (ν / 2 + 1) * (2 - u) ^ (ν / 2 - 5)

private theorem generalJ6_eq_scaledIntegral (ν : ℝ) :
    generalJ6 ν
      =
    ∫ u in (0 : ℝ)..2, generalJ6ScaledIntegrand ν u := by
  have h :=
    intervalIntegral.integral_comp_sub_mul
      (f := generalJ6ScaledIntegrand ν)
      (a := (-1 : ℝ)) (b := 1) (c := (1 : ℝ)) (d := (1 : ℝ))
      (by norm_num : (1 : ℝ) ≠ 0)
  unfold generalJ6
  convert h using 1
  · apply intervalIntegral.integral_congr
    intro x hx
    unfold generalEndpointKernel6 generalJ6ScaledIntegrand
    congr 2 <;> ring
  · norm_num

/--
Exact beta-function evaluation of the generalized sixth-power endpoint
integral.
-/
theorem generalJ6_eq_beta {ν : ℝ} (hν : 9 ≤ ν) :
    generalJ6 ν
      =
    2 ^ (ν - 3) * beta (ν / 2 + 2) (ν / 2 - 4) := by
  rw [generalJ6_eq_scaledIntegral]
  have hs : 0 < ν / 2 + 2 := by linarith
  have ht : 0 < ν / 2 - 4 := by linarith
  have hbeta :=
    integral_rpow_mul_two_sub_rpow
      (s := ν / 2 + 2) (t := ν / 2 - 4) hs ht
  unfold generalJ6ScaledIntegrand
  simpa only [
    show ν / 2 + 2 - 1 = ν / 2 + 1 by ring,
    show ν / 2 - 4 - 1 = ν / 2 - 5 by ring,
    show ν / 2 + 2 + (ν / 2 - 4) - 1 = ν - 3 by ring] using hbeta

private theorem generalJ6ScaledIntegrand_intervalIntegrable
    {ν : ℝ} (hν : 9 ≤ ν) :
    IntervalIntegrable (generalJ6ScaledIntegrand ν) volume 0 2 := by
  have hq0 : 0 ≤ ν / 2 + 1 := by linarith
  have hp : -1 < ν / 2 - 5 := by linarith
  have h01 :
      IntervalIntegrable (generalJ6ScaledIntegrand ν) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    unfold generalJ6ScaledIntegrand
    apply
      (Real.continuous_rpow_const hq0).continuousOn.mul
    exact
      (continuous_const.sub continuous_id).continuousOn.rpow_const
        (by
          intro x hx
          left
          norm_num [uIcc_of_le] at hx
          change 2 - x ≠ 0
          linarith)
  have hpow :
      IntervalIntegrable (fun u : ℝ => u ^ (ν / 2 - 5))
        volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hsub :
      IntervalIntegrable (fun u : ℝ => (2 - u) ^ (ν / 2 - 5))
        volume 1 2 := by
    have h := hpow.comp_sub_left (2 : ℝ)
    convert h.symm using 1 <;> norm_num
  have h12 :
      IntervalIntegrable (generalJ6ScaledIntegrand ν) volume 1 2 := by
    unfold generalJ6ScaledIntegrand
    exact hsub.continuousOn_mul
      (Real.continuous_rpow_const hq0).continuousOn
  exact h01.trans h12

/-- The endpoint kernel is integrable throughout the range `ν ≥ 9`. -/
theorem generalEndpointKernel6_intervalIntegrable
    {ν : ℝ} (hν : 9 ≤ ν) :
    IntervalIntegrable (generalEndpointKernel6 ν) volume (-1) 1 := by
  have hscaled := generalJ6ScaledIntegrand_intervalIntegrable hν
  have h := hscaled.comp_sub_left (1 : ℝ)
  convert h.symm using 1
  · funext x
    unfold generalEndpointKernel6 generalJ6ScaledIntegrand
    congr 2
    all_goals ring
  · norm_num
  · norm_num

private theorem generalQuadraticKernel6_continuousOn
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    ContinuousOn (generalQuadraticKernel6 ν s) (Icc (-1) 1) := by
  have hden : ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 6 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    exact ne_of_gt <| one_add_sx_pos hs <| by
      rw [abs_le]
      exact ⟨by linarith [hx.1], hx.2⟩
  have hweight :
      Continuous (fun x : ℝ => generalQuadraticWeight ν x) := by
    unfold generalQuadraticWeight
    exact
      (Real.continuous_rpow_const
        (by linarith : 0 ≤ ν / 2 + 1)).comp
          (continuous_const.sub (continuous_id.pow 2))
  unfold generalQuadraticKernel6
  exact hweight.continuousOn.div
    ((continuous_const.add
      (continuous_const.mul continuous_id)).pow 6).continuousOn hden

private theorem generalQuadraticKernel6_intervalIntegrable_neg
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    IntervalIntegrable (generalQuadraticKernel6 ν s) volume (-1) 0 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (generalQuadraticKernel6_continuousOn hν hs).mono (by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩)

private theorem generalQuadraticKernel6_intervalIntegrable_pos
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    IntervalIntegrable (generalQuadraticKernel6 ν s) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (generalQuadraticKernel6_continuousOn hν hs).mono (by
    intro x hx
    exact ⟨(by linarith [hx.1]), hx.2⟩)

private theorem generalEndpointKernel6_intervalIntegrable_neg
    {ν : ℝ} (hν : 9 ≤ ν) :
    IntervalIntegrable (generalEndpointKernel6 ν) volume (-1) 0 := by
  exact (generalEndpointKernel6_intervalIntegrable hν).mono_set (by
    intro x hx
    simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2])

private theorem generalEndpointKernel6_intervalIntegrable_pos
    {ν : ℝ} (hν : 9 ≤ ν) :
    IntervalIntegrable (generalEndpointKernel6 ν) volume 0 1 := by
  exact (generalEndpointKernel6_intervalIntegrable hν).mono_set (by
    intro x hx
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2])

private theorem generalQuadraticKernel6_add_neg_eq
    {ν s x : ℝ} (hs : |s| < 1) (hx : |x| ≤ 1) :
    generalQuadraticKernel6 ν s x
        + generalQuadraticKernel6 ν s (-x)
      =
    2 * generalQuadraticWeight ν x
      * (1 + 15 * s ^ 2 * x ^ 2 + 15 * s ^ 4 * x ^ 4
          + s ^ 6 * x ^ 6)
      / (1 - s ^ 2 * x ^ 2) ^ 6 := by
  have hplus : 1 + s * x ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hx)
  have hxneg : |-x| ≤ 1 := by simpa only [abs_neg] using hx
  have hminus : 1 - s * x ≠ 0 := by
    have h := ne_of_gt (one_add_sx_pos hs hxneg)
    simpa only [mul_neg, sub_eq_add_neg] using h
  have hplus6 : (1 + s * x) ^ 6 ≠ 0 := pow_ne_zero 6 hplus
  have hminus6 : (1 - s * x) ^ 6 ≠ 0 := pow_ne_zero 6 hminus
  have hden :
      (1 + s * x) ^ 6 * (1 - s * x) ^ 6
        = (1 - s ^ 2 * x ^ 2) ^ 6 := by ring
  have hweight :
      generalQuadraticWeight ν (-x) = generalQuadraticWeight ν x := by
    unfold generalQuadraticWeight
    congr 2
    ring
  unfold generalQuadraticKernel6
  rw [hweight]
  rw [show 1 + s * -x = 1 - s * x by ring]
  rw [div_add_div _ _ hplus6 hminus6, hden]
  congr 1
  ring

private theorem generalEndpointKernel6_add_neg_eq
    {ν x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    generalEndpointKernel6 ν x + generalEndpointKernel6 ν (-x)
      =
    2 * generalQuadraticWeight ν x
      * (1 + 15 * x ^ 2 + 15 * x ^ 4 + x ^ 6)
      / (1 - x ^ 2) ^ 6 := by
  let a : ℝ := ν / 2 + 1
  have hminus : 0 < 1 - x := sub_pos.mpr hx1
  have hplus : 0 < 1 + x := by linarith
  have hw :
      generalQuadraticWeight ν x
        = (1 - x) ^ a * (1 + x) ^ a := by
    unfold generalQuadraticWeight
    dsimp only [a]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact Real.mul_rpow hminus.le hplus.le
  have hepos :
      generalEndpointKernel6 ν x
        = generalQuadraticWeight ν x / (1 + x) ^ 6 := by
    unfold generalEndpointKernel6
    rw [show ν / 2 - 5 = a - (6 : ℕ) by
      dsimp only [a]
      norm_num
      ring]
    rw [Real.rpow_sub_natCast hplus.ne' a 6]
    rw [hw]
    ring
  have heneg :
      generalEndpointKernel6 ν (-x)
        = generalQuadraticWeight ν x / (1 - x) ^ 6 := by
    unfold generalEndpointKernel6
    rw [show 1 - -x = 1 + x by ring,
      show 1 + -x = 1 - x by ring]
    rw [show ν / 2 - 5 = a - (6 : ℕ) by
      dsimp only [a]
      norm_num
      ring]
    rw [Real.rpow_sub_natCast hminus.ne' a 6]
    calc
      (1 + x) ^ (ν / 2 + 1) * ((1 - x) ^ a / (1 - x) ^ 6)
          =
        ((1 - x) ^ a * (1 + x) ^ a) / (1 - x) ^ 6 := by
          dsimp only [a]
          ring
      _ = generalQuadraticWeight ν x / (1 - x) ^ 6 := by
          rw [← hw]
  rw [hepos, heneg]
  have hp6 : (1 + x) ^ 6 ≠ 0 := pow_ne_zero 6 hplus.ne'
  have hm6 : (1 - x) ^ 6 ≠ 0 := pow_ne_zero 6 hminus.ne'
  rw [div_add_div _ _ hp6 hm6]
  have hden :
      (1 + x) ^ 6 * (1 - x) ^ 6 = (1 - x ^ 2) ^ 6 := by ring
  rw [hden]
  congr 1
  ring

/--
After pairing `x` and `-x`, every interior sixth-power kernel is bounded by
the corresponding endpoint pair.
-/
theorem generalPairedQuadraticKernel6_le_endpoint
    {ν s x : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    generalQuadraticKernel6 ν s x
        + generalQuadraticKernel6 ν s (-x)
      ≤
    generalEndpointKernel6 ν x + generalEndpointKernel6 ν (-x) := by
  by_cases hx1 : x = 1
  · subst x
    have ha : ν / 2 + 1 ≠ 0 := by linarith
    have hleft :
        generalQuadraticKernel6 ν s 1
            + generalQuadraticKernel6 ν s (-1) = 0 := by
      unfold generalQuadraticKernel6 generalQuadraticWeight
      rw [show 1 - (1 : ℝ) ^ 2 = 0 by norm_num,
        show 1 - (-1 : ℝ) ^ 2 = 0 by norm_num,
        Real.zero_rpow ha]
      simp
    rw [hleft]
    unfold generalEndpointKernel6
    positivity
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hxabs : |x| ≤ 1 := by
      rw [abs_of_nonneg hx.1]
      exact hx.2
    rw [generalQuadraticKernel6_add_neg_eq hs hxabs,
      generalEndpointKernel6_add_neg_eq hx.1 hxlt]
    let z : ℝ := s ^ 2
    let y : ℝ := x ^ 2
    have hz0 : 0 ≤ z := by dsimp [z]; positivity
    have hz1 : z ≤ 1 := by
      dsimp [z]
      nlinarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2]
    have hy0 : 0 ≤ y := by dsimp [y]; positivity
    have hy1 : y < 1 := by
      dsimp [y]
      nlinarith [hx.1, hxlt]
    have hA : 0 < 1 - y := sub_pos.mpr hy1
    have hD : 0 < 1 - z * y := by
      dsimp [z, y]
      exact one_sub_sq_mul_sq_pos hs hxabs
    have hAD : 1 - y ≤ 1 - z * y := by
      have : z * y ≤ y := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - z) hy0]
      linarith
    have hzsq : z ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ hz0 hz1 2
    have hzcube : z ^ 3 ≤ 1 := by
      simpa using pow_le_pow_left₀ hz0 hz1 3
    have hNz0 :
        0 ≤ 1 + 15 * z * y + 15 * z ^ 2 * y ^ 2 + z ^ 3 * y ^ 3 := by
      positivity
    have hNz :
        1 + 15 * z * y + 15 * z ^ 2 * y ^ 2 + z ^ 3 * y ^ 3
          ≤ 1 + 15 * y + 15 * y ^ 2 + y ^ 3 := by
      have hzy : z * y ≤ y := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - z) hy0]
      have hzsqysq : z ^ 2 * y ^ 2 ≤ y ^ 2 :=
        by simpa using mul_le_mul_of_nonneg_right hzsq (sq_nonneg y)
      have hzcubeycube : z ^ 3 * y ^ 3 ≤ y ^ 3 :=
        by
          simpa using
            mul_le_mul_of_nonneg_right hzcube (pow_nonneg hy0 3)
      nlinarith
    have hpow : (1 - y) ^ 6 ≤ (1 - z * y) ^ 6 :=
      pow_le_pow_left₀ hA.le hAD 6
    have hprod :
        (1 - y) ^ 6
            * (1 + 15 * z * y + 15 * z ^ 2 * y ^ 2 + z ^ 3 * y ^ 3)
          ≤
        (1 - z * y) ^ 6
            * (1 + 15 * y + 15 * y ^ 2 + y ^ 3) := by
      calc
        (1 - y) ^ 6
              * (1 + 15 * z * y + 15 * z ^ 2 * y ^ 2 + z ^ 3 * y ^ 3)
            ≤
          (1 - z * y) ^ 6
              * (1 + 15 * z * y + 15 * z ^ 2 * y ^ 2
                + z ^ 3 * y ^ 3) :=
            mul_le_mul_of_nonneg_right hpow hNz0
        _ ≤
          (1 - z * y) ^ 6
              * (1 + 15 * y + 15 * y ^ 2 + y ^ 3) :=
            mul_le_mul_of_nonneg_left hNz
              (pow_nonneg hD.le 6)
    rw [div_le_div_iff₀ (pow_pos hD 6) (pow_pos hA 6)]
    have hweight :
        0 ≤ 2 * generalQuadraticWeight ν x := by
      unfold generalQuadraticWeight
      positivity
    dsimp [z, y] at hprod ⊢
    calc
      (2 * generalQuadraticWeight ν x
          * (1 + 15 * s ^ 2 * x ^ 2 + 15 * s ^ 4 * x ^ 4
              + s ^ 6 * x ^ 6))
          * (1 - x ^ 2) ^ 6
          =
        (2 * generalQuadraticWeight ν x)
          * ((1 - x ^ 2) ^ 6
            * (1 + 15 * s ^ 2 * x ^ 2
                + 15 * (s ^ 2) ^ 2 * (x ^ 2) ^ 2
                + (s ^ 2) ^ 3 * (x ^ 2) ^ 3)) := by ring
      _ ≤
        (2 * generalQuadraticWeight ν x)
          * ((1 - s ^ 2 * x ^ 2) ^ 6
            * (1 + 15 * x ^ 2 + 15 * (x ^ 2) ^ 2 + (x ^ 2) ^ 3)) :=
          mul_le_mul_of_nonneg_left hprod hweight
      _ =
        (2 * generalQuadraticWeight ν x
          * (1 + 15 * x ^ 2 + 15 * x ^ 4 + x ^ 6))
          * (1 - s ^ 2 * x ^ 2) ^ 6 := by ring

/--
Uniform sixth-power endpoint bound for every `ν ≥ 9` and interior centered
variance ratio.
-/
theorem integral_generalQuadraticKernel6_le_generalJ6
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    (∫ x in (-1 : ℝ)..1, generalQuadraticKernel6 ν s x)
      ≤ generalJ6 ν := by
  rw [integral_neg_one_one_eq_pair
    (generalQuadraticKernel6 ν s)
    (generalQuadraticKernel6_intervalIntegrable_neg hν hs)
    (generalQuadraticKernel6_intervalIntegrable_pos hν hs)]
  unfold generalJ6
  rw [integral_neg_one_one_eq_pair
    (generalEndpointKernel6 ν)
    (generalEndpointKernel6_intervalIntegrable_neg hν)
    (generalEndpointKernel6_intervalIntegrable_pos hν)]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact
      (generalQuadraticKernel6_intervalIntegrable_pos hν hs).add
        (by
          have hcomp :
              IntervalIntegrable
                (fun x : ℝ => generalQuadraticKernel6 ν s (-x))
                volume 1 0 := by
            simpa using
              (IntervalIntegrable.iff_comp_neg
                (a := (-1 : ℝ)) (b := 0)
                (f := generalQuadraticKernel6 ν s) (by simp)).mp
                  (generalQuadraticKernel6_intervalIntegrable_neg hν hs)
          exact hcomp.symm)
  · exact
      (generalEndpointKernel6_intervalIntegrable_pos hν).add
        (by
          have hcomp :
              IntervalIntegrable
                (fun x : ℝ => generalEndpointKernel6 ν (-x))
                volume 1 0 := by
            simpa using
              (IntervalIntegrable.iff_comp_neg
                (a := (-1 : ℝ)) (b := 0)
                (f := generalEndpointKernel6 ν) (by simp)).mp
                  (generalEndpointKernel6_intervalIntegrable_neg hν)
          exact hcomp.symm)
  · intro x hx
    exact generalPairedQuadraticKernel6_le_endpoint hν hs hx

/-- The uniform sixth-power bound with its beta value substituted. -/
theorem integral_generalQuadraticKernel6_le_beta
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    (∫ x in (-1 : ℝ)..1, generalQuadraticKernel6 ν s x)
      ≤
    2 ^ (ν - 3) * beta (ν / 2 + 2) (ν / 2 - 4) := by
  rw [← generalJ6_eq_beta hν]
  exact integral_generalQuadraticKernel6_le_generalJ6 hν hs

end

end GraybillDeal
