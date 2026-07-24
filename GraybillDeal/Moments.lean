import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fixed beta moments for the Graybill--Deal certificate

For the `n = 13` argument, the beta-density reduction produces

`M j = ∫ x in 0..1, x ^ (2*j) * (1 - x^2)^6`.

This file evaluates the three moments needed by the finite algebraic
certificate.
-/

namespace GraybillDeal

noncomputable def M (j : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ (2 * j) * (1 - x ^ 2) ^ 6

theorem M_nonneg (j : ℕ) : 0 ≤ M j := by
  unfold M
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  apply mul_nonneg
  · rw [two_mul, pow_add]
    exact mul_self_nonneg (x ^ j)
  · rw [show 6 = 3 + 3 by norm_num, pow_add]
    exact mul_self_nonneg ((1 - x ^ 2) ^ 3)

private lemma M_integrand_one (x : ℝ) :
    x ^ (2 * 1) * (1 - x ^ 2) ^ 6 =
      x ^ 2 - 6 * x ^ 4 + 15 * x ^ 6 - 20 * x ^ 8
        + 15 * x ^ 10 - 6 * x ^ 12 + x ^ 14 := by
  ring

theorem M_one : M 1 = 1024 / 45045 := by
  unfold M
  let F : ℝ → ℝ := fun x =>
    x ^ 3 / 3 - 6 * x ^ 5 / 5 + 15 * x ^ 7 / 7 - 20 * x ^ 9 / 9
      + 15 * x ^ 11 / 11 - 6 * x ^ 13 / 13 + x ^ 15 / 15
  calc
    (∫ x in (0 : ℝ)..1, x ^ (2 * 1) * (1 - x ^ 2) ^ 6) =
        ∫ x in (0 : ℝ)..1,
          (x ^ 2 - 6 * x ^ 4 + 15 * x ^ 6 - 20 * x ^ 8
            + 15 * x ^ 10 - 6 * x ^ 12 + x ^ 14) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact M_integrand_one x
    _ = 1024 / 45045 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := F)
        (by
          intro x hx
          dsimp [F]
          have h3 := (hasDerivAt_pow 3 x).div_const 3
          have h5 := ((hasDerivAt_pow 5 x).const_mul 6).div_const 5
          have h7 := ((hasDerivAt_pow 7 x).const_mul 15).div_const 7
          have h9 := ((hasDerivAt_pow 9 x).const_mul 20).div_const 9
          have h11 := ((hasDerivAt_pow 11 x).const_mul 15).div_const 11
          have h13 := ((hasDerivAt_pow 13 x).const_mul 6).div_const 13
          have h15 := (hasDerivAt_pow 15 x).div_const 15
          have hderiv :=
            (((((h3.sub h5).add h7).sub h9).add h11).sub h13).add h15
          convert hderiv using 1
          · funext y
            simp only [Pi.add_apply, Pi.sub_apply]
          · norm_num
            ring)
        ((by fun_prop : Continuous fun x : ℝ =>
          x ^ 2 - 6 * x ^ 4 + 15 * x ^ 6 - 20 * x ^ 8
            + 15 * x ^ 10 - 6 * x ^ 12 + x ^ 14).intervalIntegrable 0 1)]
      norm_num [F]

private lemma M_integrand_two (x : ℝ) :
    x ^ (2 * 2) * (1 - x ^ 2) ^ 6 =
      x ^ 4 - 6 * x ^ 6 + 15 * x ^ 8 - 20 * x ^ 10
        + 15 * x ^ 12 - 6 * x ^ 14 + x ^ 16 := by
  ring

theorem M_two : M 2 = (3 / 17) * M 1 := by
  rw [M_one]
  unfold M
  let F : ℝ → ℝ := fun x =>
    x ^ 5 / 5 - 6 * x ^ 7 / 7 + 15 * x ^ 9 / 9 - 20 * x ^ 11 / 11
      + 15 * x ^ 13 / 13 - 6 * x ^ 15 / 15 + x ^ 17 / 17
  calc
    (∫ x in (0 : ℝ)..1, x ^ (2 * 2) * (1 - x ^ 2) ^ 6) =
        ∫ x in (0 : ℝ)..1,
          (x ^ 4 - 6 * x ^ 6 + 15 * x ^ 8 - 20 * x ^ 10
            + 15 * x ^ 12 - 6 * x ^ 14 + x ^ 16) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact M_integrand_two x
    _ = (3 / 17) * (1024 / 45045) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := F)
        (by
          intro x hx
          dsimp [F]
          have h5 := (hasDerivAt_pow 5 x).div_const 5
          have h7 := ((hasDerivAt_pow 7 x).const_mul 6).div_const 7
          have h9 := ((hasDerivAt_pow 9 x).const_mul 15).div_const 9
          have h11 := ((hasDerivAt_pow 11 x).const_mul 20).div_const 11
          have h13 := ((hasDerivAt_pow 13 x).const_mul 15).div_const 13
          have h15 := ((hasDerivAt_pow 15 x).const_mul 6).div_const 15
          have h17 := (hasDerivAt_pow 17 x).div_const 17
          have hderiv :=
            (((((h5.sub h7).add h9).sub h11).add h13).sub h15).add h17
          convert hderiv using 1
          · funext y
            simp only [Pi.add_apply, Pi.sub_apply]
          · norm_num
            ring)
        ((by fun_prop : Continuous fun x : ℝ =>
          x ^ 4 - 6 * x ^ 6 + 15 * x ^ 8 - 20 * x ^ 10
            + 15 * x ^ 12 - 6 * x ^ 14 + x ^ 16).intervalIntegrable 0 1)]
      norm_num [F]

private lemma M_integrand_three (x : ℝ) :
    x ^ (2 * 3) * (1 - x ^ 2) ^ 6 =
      x ^ 6 - 6 * x ^ 8 + 15 * x ^ 10 - 20 * x ^ 12
        + 15 * x ^ 14 - 6 * x ^ 16 + x ^ 18 := by
  ring

theorem M_three : M 3 = (15 / 323) * M 1 := by
  rw [M_one]
  unfold M
  let F : ℝ → ℝ := fun x =>
    x ^ 7 / 7 - 6 * x ^ 9 / 9 + 15 * x ^ 11 / 11 - 20 * x ^ 13 / 13
      + 15 * x ^ 15 / 15 - 6 * x ^ 17 / 17 + x ^ 19 / 19
  calc
    (∫ x in (0 : ℝ)..1, x ^ (2 * 3) * (1 - x ^ 2) ^ 6) =
        ∫ x in (0 : ℝ)..1,
          (x ^ 6 - 6 * x ^ 8 + 15 * x ^ 10 - 20 * x ^ 12
            + 15 * x ^ 14 - 6 * x ^ 16 + x ^ 18) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact M_integrand_three x
    _ = (15 / 323) * (1024 / 45045) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := F)
        (by
          intro x hx
          dsimp [F]
          have h7 := (hasDerivAt_pow 7 x).div_const 7
          have h9 := ((hasDerivAt_pow 9 x).const_mul 6).div_const 9
          have h11 := ((hasDerivAt_pow 11 x).const_mul 15).div_const 11
          have h13 := ((hasDerivAt_pow 13 x).const_mul 20).div_const 13
          have h15 := ((hasDerivAt_pow 15 x).const_mul 15).div_const 15
          have h17 := ((hasDerivAt_pow 17 x).const_mul 6).div_const 17
          have h19 := (hasDerivAt_pow 19 x).div_const 19
          have hderiv :=
            (((((h7.sub h9).add h11).sub h13).add h15).sub h17).add h19
          convert hderiv using 1
          · funext y
            simp only [Pi.add_apply, Pi.sub_apply]
          · norm_num
            ring)
        ((by fun_prop : Continuous fun x : ℝ =>
          x ^ 6 - 6 * x ^ 8 + 15 * x ^ 10 - 20 * x ^ 12
            + 15 * x ^ 14 - 6 * x ^ 16 + x ^ 18).intervalIntegrable 0 1)]
      norm_num [F]

theorem M_one_pos : 0 < M 1 := by
  rw [M_one]
  norm_num

theorem M_two_pos : 0 < M 2 := by
  rw [M_two]
  exact mul_pos (by norm_num) M_one_pos

theorem M_three_pos : 0 < M 3 := by
  rw [M_three]
  exact mul_pos (by norm_num) M_one_pos

end GraybillDeal
