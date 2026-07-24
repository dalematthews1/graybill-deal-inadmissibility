import GraybillDeal.Moments

/-!
# Recurrence and positivity for the Graybill--Deal beta moments

The moments

`M j = ∫ x in 0..1, x^(2*j) * (1 - x^2)^6`

satisfy the beta-integral recurrence

`(2*j+1) M j = (2*j+15) M (j+1)`.
-/

namespace GraybillDeal

private def momentPrimitive (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * j + 1) * (1 - x ^ 2) ^ 7

private def momentDerivative (j : ℕ) (x : ℝ) : ℝ :=
  (2 * j + 1 : ℝ) * (x ^ (2 * j) * (1 - x ^ 2) ^ 6)
    - (2 * j + 15 : ℝ) * (x ^ (2 * (j + 1)) * (1 - x ^ 2) ^ 6)

private theorem momentPrimitive_hasDerivAt (j : ℕ) (x : ℝ) :
    HasDerivAt (momentPrimitive j) (momentDerivative j x) x := by
  have hbase : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    have hbase0 := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)
    rw [show ((fun _ : ℝ => (1 : ℝ)) - fun y : ℝ => y ^ 2) =
        (fun y : ℝ => 1 - y ^ 2) by
      funext y
      rfl] at hbase0
    have hbase1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub] using hbase0
    apply hbase1.congr_deriv
    ring
  have hprod :=
    (hasDerivAt_pow (2 * j + 1) x).mul (hbase.pow 7)
  rw [show ((fun y : ℝ => y ^ (2 * j + 1)) *
        (fun y : ℝ => 1 - y ^ 2) ^ 7) = momentPrimitive j by
      funext y
      rfl] at hprod
  apply hprod.congr_deriv
  unfold momentDerivative
  simp [pow_succ]
  ring

/-- The integral of the derivative used in the moment recurrence vanishes. -/
private theorem integral_momentDerivative_eq_zero (j : ℕ) :
    (∫ x in (0 : ℝ)..1, momentDerivative j x) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => momentPrimitive_hasDerivAt j x)
    ((by
      unfold momentDerivative
      fun_prop : Continuous (momentDerivative j)).intervalIntegrable 0 1)]
  simp [momentPrimitive]

/--
The beta moments satisfy

`(2*j+1) M j = (2*j+15) M (j+1)`.
-/
theorem M_recurrence (j : ℕ) :
    (2 * j + 1 : ℝ) * M j = (2 * j + 15 : ℝ) * M (j + 1) := by
  have hzero := integral_momentDerivative_eq_zero j
  have hsplit :
      (∫ x in (0 : ℝ)..1, momentDerivative j x) =
        (2 * j + 1 : ℝ) * M j - (2 * j + 15 : ℝ) * M (j + 1) := by
    unfold momentDerivative M
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun x : ℝ =>
        (2 * j + 1 : ℝ) * (x ^ (2 * j) * (1 - x ^ 2) ^ 6)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun x : ℝ =>
        (2 * j + 15 : ℝ) *
          (x ^ (2 * (j + 1)) * (1 - x ^ 2) ^ 6)).intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const_mul]
  rw [hsplit] at hzero
  exact sub_eq_zero.mp hzero

/-- Every moment `M j` is strictly positive. -/
theorem M_pos : ∀ j : ℕ, 0 < M j := by
  intro j
  induction j with
  | zero =>
      have h : M 0 = 15 * M 1 := by
        simpa using M_recurrence 0
      rw [h]
      exact mul_pos (by norm_num) M_one_pos
  | succ j ih =>
      have hprod : 0 < (2 * j + 15 : ℝ) * M (j + 1) := by
        rw [← M_recurrence j]
        exact mul_pos (by positivity) ih
      exact pos_of_mul_pos_right hprod (by positivity)

end GraybillDeal
