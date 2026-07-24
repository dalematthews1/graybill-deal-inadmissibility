import GraybillDeal.GeneralQuadraticEndpoint4
import GraybillDeal.GeneralQuadraticEndpoint6
import GraybillDeal.GeneralReduced

/-!
# Complete generalized quadratic allowance

This module packages the two exact endpoint evaluations as the allowance
`Hν` and discharges the last hypotheses of the generic reduced-risk theorem.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The exact fourth-order endpoint value. -/
def generalJ4 (ν : ℝ) : ℝ :=
  (2 : ℝ) ^ (ν - 1) * beta (ν / 2 + 2) (ν / 2 - 2)

/-- The complete quadratic allowance at residual degrees of freedom `ν`. -/
def generalH (ν : ℝ) : ℝ :=
  generalQuadraticAllowance ν (generalJ4 ν) (generalJ6 ν)

theorem generalJ4_eq_endpointIntegral
    {ν : ℝ} (hν : 9 ≤ ν) :
    generalJ4 ν = generalQuadraticEndpointIntegral4 ν := by
  rw [integral_generalQuadraticEndpointKernel4 hν]
  rfl

theorem generalJ4_pos {ν : ℝ} (hν : 9 ≤ ν) :
    0 < generalJ4 ν := by
  unfold generalJ4
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (beta_pos (by linarith) (by linarith))

theorem generalJ6_pos {ν : ℝ} (hν : 9 ≤ ν) :
    0 < generalJ6 ν := by
  rw [generalJ6_eq_beta hν]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (beta_pos (by linarith) (by linarith))

theorem generalH_pos {ν : ℝ} (hν : 9 ≤ ν) :
    0 < generalH ν := by
  unfold generalH generalQuadraticAllowance
  have htop :
      0 < generalQuadraticTopCoefficient ν :=
    generalQuadraticTopCoefficient_pos hν
  nlinarith [mul_pos htop (generalJ6_pos hν), generalJ4_pos hν]

theorem integral_generalQuadraticKernel4_le_generalJ4
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    (∫ x in (-1 : ℝ)..1, generalQuadraticKernel4 ν s x)
      ≤ generalJ4 ν := by
  simpa only [generalJ4] using
    integral_generalQuadraticKernel4_le hν hs

theorem integral_generalQuadraticKernel6_le_generalJ6'
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    (∫ x in (-1 : ℝ)..1, generalQuadraticKernel6 ν s x)
      ≤ generalJ6 ν :=
  integral_generalQuadraticKernel6_le_generalJ6 hν hs

/-- The generalized exact quadratic integrand is uniformly bounded by `Hν`. -/
theorem integral_generalCgIntegrand_le_generalH
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    (∫ x in (-1 : ℝ)..1, generalCgIntegrand ν s x)
      ≤ generalH ν := by
  exact integral_generalCgIntegrand_le_of_kernel_bounds
    hν hs
    (integral_generalQuadraticKernel4_le_generalJ4 hν hs)
    (integral_generalQuadraticKernel6_le_generalJ6' hν hs)

/-- The unconditional generalized upper bound for the quadratic risk term. -/
theorem generalCtheta_le
    (Ka : ℝ) {ν s : ℝ}
    (hKa : 0 ≤ Ka) (hν : 9 ≤ ν) (hs : |s| < 1) :
    generalCtheta Ka ν s
      ≤ Ka * (1 - s ^ 2) ^ 2 * generalH ν := by
  exact generalCtheta_le_of_kernel_bounds
    Ka hKa hν hs
    (integral_generalQuadraticKernel4_le_generalJ4 hν hs)
    (integral_generalQuadraticKernel6_le_generalJ6' hν hs)

/--
For every equal sample size represented by `ν ≥ 9`, there is a single
positive perturbation coefficient which makes the reduced risk difference
strictly negative for every interior variance ratio.
-/
theorem exists_generalReducedRisk_epsilon_unconditional
    (Ka : ℝ) (ν : ℕ) (hν : 9 ≤ ν) (hKa : 0 < Ka) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, |s| < 1 →
        2 * ε * generalBtheta Ka (ν : ℝ) s
          + ε ^ 2 * generalCtheta Ka (ν : ℝ) s < 0 := by
  have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
  exact exists_generalReducedRisk_epsilon_of_kernel_bounds
    Ka (generalJ4 (ν : ℝ)) (generalJ6 (ν : ℝ))
      ν hν hKa
      (generalJ4_pos hνR) (le_of_lt (generalJ6_pos hνR))
      (fun hs =>
        integral_generalQuadraticKernel4_le_generalJ4 hνR hs)
      (fun hs =>
        integral_generalQuadraticKernel6_le_generalJ6' hνR hs)

/-- The same existence theorem stated directly for common sample size `n`. -/
theorem exists_generalReducedRisk_epsilon_sampleSize
    (Ka : ℝ) (n : ℕ) (hn : 10 ≤ n) (hKa : 0 < Ka) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, |s| < 1 →
        2 * ε * generalBtheta Ka ((n - 1 : ℕ) : ℝ) s
          + ε ^ 2 * generalCtheta Ka ((n - 1 : ℕ) : ℝ) s < 0 := by
  have hν : 9 ≤ n - 1 := by
    have h := Nat.sub_le_sub_right hn 1
    norm_num at h ⊢
    exact h
  exact exists_generalReducedRisk_epsilon_unconditional
    Ka (n - 1) hν hKa

end

end GraybillDeal
