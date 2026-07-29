import GraybillDeal.IntegralPairing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Uniform bounds for the quadratic Graybill--Deal kernels

For an interior centered variance ratio `|s| < 1`, this file proves the two
uniform integral bounds used in the quadratic part of the `n = 13`
counterexample:

* the fourth-power kernel is at most `256 / 165`;
* the sixth-power kernel is at most `64 / 9`.

The proof pairs the values at `x` and `-x`, bounds the resulting even rational
function by its endpoint value `|s| = 1`, and integrates the endpoint
polynomial exactly.
-/

namespace GraybillDeal

open Set
open MeasureTheory

noncomputable section

/-- The fourth-power denominator kernel appearing in the quadratic bound. -/
def quadraticKernel4 (s x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ 7 / (1 + s * x) ^ 4

/-- The sixth-power denominator kernel appearing in the quadratic bound. -/
def quadraticKernel6 (s x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ 7 / (1 + s * x) ^ 6

/-- The endpoint polynomial obtained by pairing the fourth-power kernel. -/
def endpointKernel4 (x : ℝ) : ℝ :=
  (1 - x) ^ 7 * (1 + x) ^ 3
    + (1 + x) ^ 7 * (1 - x) ^ 3

/-- The endpoint polynomial obtained by pairing the sixth-power kernel. -/
def endpointKernel6 (x : ℝ) : ℝ :=
  (1 - x) ^ 7 * (1 + x)
    + (1 + x) ^ 7 * (1 - x)

private theorem quadraticKernel4_continuousOn {s : ℝ} (hs : |s| < 1) :
    ContinuousOn (quadraticKernel4 s) (Icc (-1) 1) := by
  have hden : ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 4 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  unfold quadraticKernel4
  exact
    ((continuous_const.sub (continuous_id.pow 2)).pow 7).continuousOn.div
      ((continuous_const.add (continuous_const.mul continuous_id)).pow 4).continuousOn
      hden

private theorem quadraticKernel6_continuousOn {s : ℝ} (hs : |s| < 1) :
    ContinuousOn (quadraticKernel6 s) (Icc (-1) 1) := by
  have hden : ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 6 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  unfold quadraticKernel6
  exact
    ((continuous_const.sub (continuous_id.pow 2)).pow 7).continuousOn.div
      ((continuous_const.add (continuous_const.mul continuous_id)).pow 6).continuousOn
      hden

private theorem quadraticKernel4_intervalIntegrable_neg {s : ℝ}
    (hs : |s| < 1) :
    IntervalIntegrable (quadraticKernel4 s) volume (-1) 0 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (quadraticKernel4_continuousOn hs).mono (by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩)

private theorem quadraticKernel4_intervalIntegrable_pos {s : ℝ}
    (hs : |s| < 1) :
    IntervalIntegrable (quadraticKernel4 s) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (quadraticKernel4_continuousOn hs).mono (by
    intro x hx
    exact ⟨(by linarith [hx.1]), hx.2⟩)

private theorem quadraticKernel6_intervalIntegrable_neg {s : ℝ}
    (hs : |s| < 1) :
    IntervalIntegrable (quadraticKernel6 s) volume (-1) 0 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (quadraticKernel6_continuousOn hs).mono (by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩)

private theorem quadraticKernel6_intervalIntegrable_pos {s : ℝ}
    (hs : |s| < 1) :
    IntervalIntegrable (quadraticKernel6 s) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (quadraticKernel6_continuousOn hs).mono (by
    intro x hx
    exact ⟨(by linarith [hx.1]), hx.2⟩)

private theorem pairedKernel4_eq {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    quadraticKernel4 s x + quadraticKernel4 s (-x)
      =
    2 * (1 - x ^ 2) ^ 7
      * (1 + 6 * s ^ 2 * x ^ 2 + s ^ 4 * x ^ 4)
      / (1 - s ^ 2 * x ^ 2) ^ 4 := by
  have hplus : 1 + s * x ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hx)
  have hxneg : |-x| ≤ 1 := by simpa only [abs_neg] using hx
  have hminus : 1 - s * x ≠ 0 := by
    have := ne_of_gt (one_add_sx_pos hs hxneg)
    simpa only [mul_neg, sub_eq_add_neg] using this
  have hpair : 1 - s ^ 2 * x ^ 2 ≠ 0 :=
    ne_of_gt (one_sub_sq_mul_sq_pos hs hx)
  have hplus4 : (1 + s * x) ^ 4 ≠ 0 := pow_ne_zero 4 hplus
  have hminus4 : (1 - s * x) ^ 4 ≠ 0 := pow_ne_zero 4 hminus
  have hden :
      (1 + s * x) ^ 4 * (1 - s * x) ^ 4
        = (1 - s ^ 2 * x ^ 2) ^ 4 := by
    ring
  unfold quadraticKernel4
  rw [show 1 - (-x) ^ 2 = 1 - x ^ 2 by ring]
  rw [show 1 + s * -x = 1 - s * x by ring]
  change
    (1 - x ^ 2) ^ 7 / (1 + s * x) ^ 4
        + (1 - x ^ 2) ^ 7 / (1 - s * x) ^ 4
      =
    2 * (1 - x ^ 2) ^ 7
      * (1 + 6 * s ^ 2 * x ^ 2 + s ^ 4 * x ^ 4)
      / (1 - s ^ 2 * x ^ 2) ^ 4
  rw [div_add_div _ _ hplus4 hminus4, hden]
  congr 1
  ring

private theorem pairedKernel6_eq {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    quadraticKernel6 s x + quadraticKernel6 s (-x)
      =
    2 * (1 - x ^ 2) ^ 7
      * (1 + 15 * s ^ 2 * x ^ 2 + 15 * s ^ 4 * x ^ 4
          + s ^ 6 * x ^ 6)
      / (1 - s ^ 2 * x ^ 2) ^ 6 := by
  have hplus : 1 + s * x ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hx)
  have hxneg : |-x| ≤ 1 := by simpa only [abs_neg] using hx
  have hminus : 1 - s * x ≠ 0 := by
    have := ne_of_gt (one_add_sx_pos hs hxneg)
    simpa only [mul_neg, sub_eq_add_neg] using this
  have hpair : 1 - s ^ 2 * x ^ 2 ≠ 0 :=
    ne_of_gt (one_sub_sq_mul_sq_pos hs hx)
  have hplus6 : (1 + s * x) ^ 6 ≠ 0 := pow_ne_zero 6 hplus
  have hminus6 : (1 - s * x) ^ 6 ≠ 0 := pow_ne_zero 6 hminus
  have hden :
      (1 + s * x) ^ 6 * (1 - s * x) ^ 6
        = (1 - s ^ 2 * x ^ 2) ^ 6 := by
    ring
  unfold quadraticKernel6
  rw [show 1 - (-x) ^ 2 = 1 - x ^ 2 by ring]
  rw [show 1 + s * -x = 1 - s * x by ring]
  change
    (1 - x ^ 2) ^ 7 / (1 + s * x) ^ 6
        + (1 - x ^ 2) ^ 7 / (1 - s * x) ^ 6
      =
    2 * (1 - x ^ 2) ^ 7
      * (1 + 15 * s ^ 2 * x ^ 2 + 15 * s ^ 4 * x ^ 4
          + s ^ 6 * x ^ 6)
      / (1 - s ^ 2 * x ^ 2) ^ 6
  rw [div_add_div _ _ hplus6 hminus6, hden]
  congr 1
  ring

private theorem endpointKernel4_algebra (x : ℝ) :
    endpointKernel4 x =
      2 * (1 - x ^ 2) ^ 3 * (1 + 6 * x ^ 2 + x ^ 4) := by
  unfold endpointKernel4
  ring

private theorem endpointKernel6_algebra (x : ℝ) :
    endpointKernel6 x =
      2 * (1 - x ^ 2) * (1 + 15 * x ^ 2 + 15 * x ^ 4 + x ^ 6) := by
  unfold endpointKernel6
  ring

/--
After pairing, the fourth-power kernel is bounded pointwise by its endpoint
polynomial.
-/
theorem pairedKernel4_le_endpoint {s x : ℝ}
    (hs : |s| < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    quadraticKernel4 s x + quadraticKernel4 s (-x) ≤ endpointKernel4 x := by
  have hxabs : |x| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [pairedKernel4_eq hs hxabs, endpointKernel4_algebra]
  let z : ℝ := s ^ 2
  let y : ℝ := x ^ 2
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    nlinarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2]
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy1 : y ≤ 1 := by
    dsimp [y]
    nlinarith [hx.1, hx.2]
  have hA0 : 0 ≤ 1 - y := by linarith
  have hD : 0 < 1 - z * y := by
    dsimp [z, y]
    exact one_sub_sq_mul_sq_pos hs hxabs
  have hAD : 1 - y ≤ 1 - z * y := by
    have : z * y ≤ y := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - z) hy0]
    linarith
  have hzsq : z ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hz0 hz1 2
  have hzy : z * y ≤ y := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - z) hy0]
  have hzsqysq : z ^ 2 * y ^ 2 ≤ y ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_right hzsq (sq_nonneg y)
  have hNz0 : 0 ≤ 1 + 6 * z * y + z ^ 2 * y ^ 2 := by
    positivity
  have hNz :
      1 + 6 * z * y + z ^ 2 * y ^ 2 ≤ 1 + 6 * y + y ^ 2 := by
    nlinarith
  have hpow : (1 - y) ^ 4 ≤ (1 - z * y) ^ 4 :=
    pow_le_pow_left₀ hA0 hAD 4
  have hprod :
      (1 - y) ^ 4 * (1 + 6 * z * y + z ^ 2 * y ^ 2)
        ≤
      (1 - z * y) ^ 4 * (1 + 6 * y + y ^ 2) := by
    calc
      (1 - y) ^ 4 * (1 + 6 * z * y + z ^ 2 * y ^ 2)
          ≤ (1 - z * y) ^ 4 * (1 + 6 * z * y + z ^ 2 * y ^ 2) :=
        mul_le_mul_of_nonneg_right hpow hNz0
      _ ≤ (1 - z * y) ^ 4 * (1 + 6 * y + y ^ 2) :=
        mul_le_mul_of_nonneg_left hNz
          (pow_nonneg (le_of_lt hD) 4)
  apply (div_le_iff₀ (pow_pos hD 4)).2
  dsimp [z, y] at hprod ⊢
  calc
    2 * (1 - x ^ 2) ^ 7
          * (1 + 6 * s ^ 2 * x ^ 2 + s ^ 4 * x ^ 4)
        =
      (2 * (1 - x ^ 2) ^ 3)
        * ((1 - x ^ 2) ^ 4
          * (1 + 6 * s ^ 2 * x ^ 2 + (s ^ 2) ^ 2 * (x ^ 2) ^ 2)) := by
            ring
    _ ≤
      (2 * (1 - x ^ 2) ^ 3)
        * ((1 - s ^ 2 * x ^ 2) ^ 4
          * (1 + 6 * x ^ 2 + (x ^ 2) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ =
      (2 * (1 - x ^ 2) ^ 3 * (1 + 6 * x ^ 2 + x ^ 4))
        * (1 - s ^ 2 * x ^ 2) ^ 4 := by
            ring

/--
After pairing, the sixth-power kernel is bounded pointwise by its endpoint
polynomial.
-/
theorem pairedKernel6_le_endpoint {s x : ℝ}
    (hs : |s| < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    quadraticKernel6 s x + quadraticKernel6 s (-x) ≤ endpointKernel6 x := by
  have hxabs : |x| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [pairedKernel6_eq hs hxabs, endpointKernel6_algebra]
  let z : ℝ := s ^ 2
  let y : ℝ := x ^ 2
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    nlinarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2]
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy1 : y ≤ 1 := by
    dsimp [y]
    nlinarith [hx.1, hx.2]
  have hA0 : 0 ≤ 1 - y := by linarith
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
  have hzy : z * y ≤ y := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - z) hy0]
  have hzsqysq : z ^ 2 * y ^ 2 ≤ y ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_right hzsq (sq_nonneg y)
  have hzcubeycube : z ^ 3 * y ^ 3 ≤ y ^ 3 :=
    by
      simpa using
        mul_le_mul_of_nonneg_right hzcube (pow_nonneg hy0 3)
  have hNz0 :
      0 ≤ 1 + 15 * z * y + 15 * z ^ 2 * y ^ 2 + z ^ 3 * y ^ 3 := by
    positivity
  have hNz :
      1 + 15 * z * y + 15 * z ^ 2 * y ^ 2 + z ^ 3 * y ^ 3
        ≤ 1 + 15 * y + 15 * y ^ 2 + y ^ 3 := by
    nlinarith
  have hpow : (1 - y) ^ 6 ≤ (1 - z * y) ^ 6 :=
    pow_le_pow_left₀ hA0 hAD 6
  have hprod :
      (1 - y) ^ 6
          * (1 + 15 * z * y + 15 * z ^ 2 * y ^ 2 + z ^ 3 * y ^ 3)
        ≤
      (1 - z * y) ^ 6
          * (1 + 15 * y + 15 * y ^ 2 + y ^ 3) := by
    calc
      (1 - y) ^ 6
            * (1 + 15 * z * y + 15 * z ^ 2 * y ^ 2 + z ^ 3 * y ^ 3)
          ≤ (1 - z * y) ^ 6
            * (1 + 15 * z * y + 15 * z ^ 2 * y ^ 2 + z ^ 3 * y ^ 3) :=
        mul_le_mul_of_nonneg_right hpow hNz0
      _ ≤ (1 - z * y) ^ 6
            * (1 + 15 * y + 15 * y ^ 2 + y ^ 3) :=
        mul_le_mul_of_nonneg_left hNz
          (pow_nonneg (le_of_lt hD) 6)
  apply (div_le_iff₀ (pow_pos hD 6)).2
  dsimp [z, y] at hprod ⊢
  calc
    2 * (1 - x ^ 2) ^ 7
          * (1 + 15 * s ^ 2 * x ^ 2 + 15 * s ^ 4 * x ^ 4
              + s ^ 6 * x ^ 6)
        =
      (2 * (1 - x ^ 2))
        * ((1 - x ^ 2) ^ 6
          * (1 + 15 * s ^ 2 * x ^ 2
              + 15 * (s ^ 2) ^ 2 * (x ^ 2) ^ 2
              + (s ^ 2) ^ 3 * (x ^ 2) ^ 3)) := by
            ring
    _ ≤
      (2 * (1 - x ^ 2))
        * ((1 - s ^ 2 * x ^ 2) ^ 6
          * (1 + 15 * x ^ 2 + 15 * (x ^ 2) ^ 2 + (x ^ 2) ^ 3)) := by
            exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ =
      (2 * (1 - x ^ 2)
          * (1 + 15 * x ^ 2 + 15 * x ^ 4 + x ^ 6))
        * (1 - s ^ 2 * x ^ 2) ^ 6 := by
            ring

/-- Exact integral of the fourth-power endpoint polynomial. -/
theorem integral_endpointKernel4 :
    (∫ x in (0 : ℝ)..1, endpointKernel4 x) = 256 / 165 := by
  let F : ℝ → ℝ := fun x =>
    2 * x + 2 * x ^ 3 - (28 / 5) * x ^ 5 + 4 * x ^ 7
      - (2 / 3) * x ^ 9 - (2 / 11) * x ^ 11
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F)
    (by
      intro x hx
      dsimp [F]
      have h1 := (hasDerivAt_id x).const_mul 2
      have h3 := (hasDerivAt_pow 3 x).const_mul 2
      have h5 := (hasDerivAt_pow 5 x).const_mul (28 / 5)
      have h7 := (hasDerivAt_pow 7 x).const_mul 4
      have h9 := (hasDerivAt_pow 9 x).const_mul (2 / 3)
      have h11 := (hasDerivAt_pow 11 x).const_mul (2 / 11)
      have hderiv := ((((h1.add h3).sub h5).add h7).sub h9).sub h11
      convert hderiv using 1
      · funext y
        simp only [Pi.add_apply, Pi.sub_apply, id_eq]
      · unfold endpointKernel4
        norm_num
        ring)
    ((by
      unfold endpointKernel4
      fun_prop : Continuous endpointKernel4).intervalIntegrable 0 1)]
  norm_num [F]

/-- Exact integral of the sixth-power endpoint polynomial. -/
theorem integral_endpointKernel6 :
    (∫ x in (0 : ℝ)..1, endpointKernel6 x) = 64 / 9 := by
  let F : ℝ → ℝ := fun x =>
    2 * x + (28 / 3) * x ^ 3 - 4 * x ^ 7 - (2 / 9) * x ^ 9
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F)
    (by
      intro x hx
      dsimp [F]
      have h1 := (hasDerivAt_id x).const_mul 2
      have h3 := (hasDerivAt_pow 3 x).const_mul (28 / 3)
      have h7 := (hasDerivAt_pow 7 x).const_mul 4
      have h9 := (hasDerivAt_pow 9 x).const_mul (2 / 9)
      have hderiv := ((h1.add h3).sub h7).sub h9
      convert hderiv using 1
      · funext y
        simp only [Pi.add_apply, Pi.sub_apply, id_eq]
      · unfold endpointKernel6
        norm_num
        ring)
    ((by
      unfold endpointKernel6
      fun_prop : Continuous endpointKernel6).intervalIntegrable 0 1)]
  norm_num [F]

/--
Uniform fourth-power quadratic-kernel bound for every interior variance
ratio.
-/
theorem integral_quadraticKernel4_le {s : ℝ} (hs : |s| < 1) :
    (∫ x in (-1 : ℝ)..1, quadraticKernel4 s x) ≤ 256 / 165 := by
  rw [integral_neg_one_one_eq_pair
    (quadraticKernel4 s)
    (quadraticKernel4_intervalIntegrable_neg hs)
    (quadraticKernel4_intervalIntegrable_pos hs)]
  rw [← integral_endpointKernel4]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact
      (quadraticKernel4_intervalIntegrable_pos hs).add
        (by
          have hcomp10 :
              IntervalIntegrable (fun x : ℝ => quadraticKernel4 s (-x))
                volume 1 0 :=
            by
              simpa using
                (IntervalIntegrable.iff_comp_neg
                  (a := (-1 : ℝ)) (b := 0) (f := quadraticKernel4 s)
                    (by simp)).mp
                      (quadraticKernel4_intervalIntegrable_neg hs)
          exact hcomp10.symm)
  · exact
      ((by
        unfold endpointKernel4
        fun_prop : Continuous endpointKernel4).intervalIntegrable 0 1)
  · intro x hx
    exact pairedKernel4_le_endpoint hs hx

/--
Uniform sixth-power quadratic-kernel bound for every interior variance
ratio.
-/
theorem integral_quadraticKernel6_le {s : ℝ} (hs : |s| < 1) :
    (∫ x in (-1 : ℝ)..1, quadraticKernel6 s x) ≤ 64 / 9 := by
  rw [integral_neg_one_one_eq_pair
    (quadraticKernel6 s)
    (quadraticKernel6_intervalIntegrable_neg hs)
    (quadraticKernel6_intervalIntegrable_pos hs)]
  rw [← integral_endpointKernel6]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact
      (quadraticKernel6_intervalIntegrable_pos hs).add
        (by
          have hcomp10 :
              IntervalIntegrable (fun x : ℝ => quadraticKernel6 s (-x))
                volume 1 0 :=
            by
              simpa using
                (IntervalIntegrable.iff_comp_neg
                  (a := (-1 : ℝ)) (b := 0) (f := quadraticKernel6 s)
                    (by simp)).mp
                      (quadraticKernel6_intervalIntegrable_neg hs)
          exact hcomp10.symm)
  · exact
      ((by
        unfold endpointKernel6
        fun_prop : Continuous endpointKernel6).intervalIntegrable 0 1)
  · intro x hx
    exact pairedKernel6_le_endpoint hs hx

/--
The two uniform bounds combine with `K₂ = 18 / 55` to give the constant
`H = 1696 / 165` used in the fixed-`n = 13` risk certificate.
-/
theorem n13_quadratic_integrals_le {s : ℝ} (hs : |s| < 1) :
    (∫ x in (-1 : ℝ)..1, quadraticKernel4 s x)
        + (15 / 4 : ℝ) * (18 / 55)
          * (∫ x in (-1 : ℝ)..1, quadraticKernel6 s x)
      ≤ 1696 / 165 := by
  calc
    (∫ x in (-1 : ℝ)..1, quadraticKernel4 s x)
          + (15 / 4 : ℝ) * (18 / 55)
            * (∫ x in (-1 : ℝ)..1, quadraticKernel6 s x)
        ≤ (256 / 165 : ℝ)
          + (15 / 4) * (18 / 55) * (64 / 9) := by
            gcongr
            · exact integral_quadraticKernel4_le hs
            · exact integral_quadraticKernel6_le hs
    _ = 1696 / 165 := by norm_num

end

end GraybillDeal
