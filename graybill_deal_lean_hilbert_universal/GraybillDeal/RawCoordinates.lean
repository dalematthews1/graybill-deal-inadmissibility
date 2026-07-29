import GraybillDeal.Canonical

/-!
# Raw variance coordinates

This file is the deterministic identification layer between two raw sample
variances and the canonical beta--gamma coordinates.

For positive population variances `σ₁², σ₂²` and observed unbiased sample
variances `S₁², S₂²`, put

* `Uᵢ = 12 Sᵢ² / σᵢ²`,
* `P = U₁ / (U₁ + U₂)`,
* `L = U₁ + U₂`,
* `V = 13 D² / (σ₁² + σ₂²)`.

The theorems below verify algebraically that the canonical weight and
quadratic statistic are exactly

* `S₁² / (S₁² + S₂²)`, and
* `13 D² / (S₁² + S₂²)`.

The nonzero assumptions are deliberately explicit.  In the raw normal model
they will be discharged almost surely from the chi-square laws.
-/

namespace GraybillDeal

noncomputable section

/-- Sum of the two population variances. -/
def rawVarianceSum (σ₁sq σ₂sq : ℝ) : ℝ :=
  σ₁sq + σ₂sq

/-- The centered population-variance contrast `s = 2θ-1`. -/
def rawVarianceContrast (σ₁sq σ₂sq : ℝ) : ℝ :=
  (σ₁sq - σ₂sq) / rawVarianceSum σ₁sq σ₂sq

/-- Standardized residual sum of squares at sample size `13`. -/
def rawResidualScale13 (σsq Ssq : ℝ) : ℝ :=
  12 * Ssq / σsq

/-- Sum coordinate of the two standardized residual sums of squares. -/
def rawResidualL13 (σ₁sq σ₂sq S₁sq S₂sq : ℝ) : ℝ :=
  rawResidualScale13 σ₁sq S₁sq + rawResidualScale13 σ₂sq S₂sq

/-- Ratio coordinate of the two standardized residual sums of squares. -/
def rawResidualP13 (σ₁sq σ₂sq S₁sq S₂sq : ℝ) : ℝ :=
  rawResidualScale13 σ₁sq S₁sq
    / rawResidualL13 σ₁sq σ₂sq S₁sq S₂sq

/--
Nonvanishing of the standardized residual sum forces nonvanishing of its
common-denominator numerator.
-/
theorem rawResidual_cross_ne
    {σ₁sq σ₂sq S₁sq S₂sq : ℝ}
    (hσ₁ : σ₁sq ≠ 0) (hσ₂ : σ₂sq ≠ 0)
    (hL : rawResidualL13 σ₁sq σ₂sq S₁sq S₂sq ≠ 0) :
    S₁sq * σ₂sq + σ₁sq * S₂sq ≠ 0 := by
  intro hcross
  apply hL
  unfold rawResidualL13 rawResidualScale13
  field_simp [hσ₁, hσ₂]
  nlinarith [hcross]

theorem canonicalTheta_rawVarianceContrast
    {σ₁sq σ₂sq : ℝ}
    (hsum : rawVarianceSum σ₁sq σ₂sq ≠ 0) :
    canonicalTheta (rawVarianceContrast σ₁sq σ₂sq)
      = σ₁sq / rawVarianceSum σ₁sq σ₂sq := by
  unfold canonicalTheta rawVarianceContrast
  unfold rawVarianceSum at hsum ⊢
  field_simp [hsum]
  ring

theorem one_sub_canonicalTheta_rawVarianceContrast
    {σ₁sq σ₂sq : ℝ}
    (hsum : rawVarianceSum σ₁sq σ₂sq ≠ 0) :
    1 - canonicalTheta (rawVarianceContrast σ₁sq σ₂sq)
      = σ₂sq / rawVarianceSum σ₁sq σ₂sq := by
  rw [canonicalTheta_rawVarianceContrast hsum]
  unfold rawVarianceSum at hsum ⊢
  field_simp [hsum]
  ring

theorem abs_rawVarianceContrast_lt_one
    {σ₁sq σ₂sq : ℝ} (hσ₁ : 0 < σ₁sq) (hσ₂ : 0 < σ₂sq) :
    |rawVarianceContrast σ₁sq σ₂sq| < 1 := by
  rw [abs_lt]
  unfold rawVarianceContrast rawVarianceSum
  constructor
  · rw [lt_div_iff₀ (add_pos hσ₁ hσ₂)]
    linarith
  · rw [div_lt_iff₀ (add_pos hσ₁ hσ₂)]
    linarith

/--
The product `L d` is the raw total sample variance in canonical units.
-/
theorem rawResidualL13_mul_canonicalDenom
    {σ₁sq σ₂sq S₁sq S₂sq : ℝ}
    (hσ₁ : σ₁sq ≠ 0) (hσ₂ : σ₂sq ≠ 0)
    (hsum : rawVarianceSum σ₁sq σ₂sq ≠ 0)
    (hL : rawResidualL13 σ₁sq σ₂sq S₁sq S₂sq ≠ 0) :
    rawResidualL13 σ₁sq σ₂sq S₁sq S₂sq
        * canonicalDenom (rawVarianceContrast σ₁sq σ₂sq)
          (rawResidualP13 σ₁sq σ₂sq S₁sq S₂sq)
      =
    12 * (S₁sq + S₂sq) / rawVarianceSum σ₁sq σ₂sq := by
  have hcross :=
    rawResidual_cross_ne hσ₁ hσ₂ hL
  rw [show canonicalDenom (rawVarianceContrast σ₁sq σ₂sq)
        (rawResidualP13 σ₁sq σ₂sq S₁sq S₂sq)
      =
      canonicalTheta (rawVarianceContrast σ₁sq σ₂sq)
          * rawResidualP13 σ₁sq σ₂sq S₁sq S₂sq
        + (1 - canonicalTheta (rawVarianceContrast σ₁sq σ₂sq))
          * (1 - rawResidualP13 σ₁sq σ₂sq S₁sq S₂sq) by rfl]
  rw [one_sub_canonicalTheta_rawVarianceContrast hsum,
    canonicalTheta_rawVarianceContrast hsum]
  unfold rawResidualP13 rawResidualL13 rawResidualScale13 rawVarianceSum
  unfold rawResidualL13 rawResidualScale13 at hL
  unfold rawVarianceSum at hsum
  field_simp [hσ₁, hσ₂, hsum, hL, hcross]
  ring

/-- The canonical base weight is exactly the Graybill--Deal sample weight. -/
theorem canonicalR_rawResidualP13
    {σ₁sq σ₂sq S₁sq S₂sq : ℝ}
    (hσ₁ : σ₁sq ≠ 0) (hσ₂ : σ₂sq ≠ 0)
    (hsum : rawVarianceSum σ₁sq σ₂sq ≠ 0)
    (hL : rawResidualL13 σ₁sq σ₂sq S₁sq S₂sq ≠ 0)
    (hSsum : S₁sq + S₂sq ≠ 0) :
    canonicalR (rawVarianceContrast σ₁sq σ₂sq)
        (rawResidualP13 σ₁sq σ₂sq S₁sq S₂sq)
      =
    S₁sq / (S₁sq + S₂sq) := by
  have hcross :=
    rawResidual_cross_ne hσ₁ hσ₂ hL
  unfold canonicalR
  rw [canonicalTheta_rawVarianceContrast hsum]
  have hden :
      canonicalDenom (rawVarianceContrast σ₁sq σ₂sq)
          (rawResidualP13 σ₁sq σ₂sq S₁sq S₂sq)
        =
      (12 * (S₁sq + S₂sq) / rawVarianceSum σ₁sq σ₂sq)
        / rawResidualL13 σ₁sq σ₂sq S₁sq S₂sq := by
    apply (eq_div_iff hL).2
    rw [mul_comm]
    exact rawResidualL13_mul_canonicalDenom hσ₁ hσ₂ hsum hL
  rw [hden]
  unfold rawResidualP13 rawResidualL13 rawResidualScale13 rawVarianceSum
  unfold rawResidualL13 rawResidualScale13 at hL
  unfold rawVarianceSum at hsum
  field_simp [hσ₁, hσ₂, hsum, hL, hSsum, hcross]
  field_simp [hcross]

/--
The canonical statistic `q=12V/(Ld)` is exactly
`13D²/(S₁²+S₂²)`.
-/
theorem canonicalQ13_rawResidual_coordinates
    {σ₁sq σ₂sq S₁sq S₂sq D : ℝ}
    (hσ₁ : σ₁sq ≠ 0) (hσ₂ : σ₂sq ≠ 0)
    (hsum : rawVarianceSum σ₁sq σ₂sq ≠ 0)
    (hL : rawResidualL13 σ₁sq σ₂sq S₁sq S₂sq ≠ 0)
    (hSsum : S₁sq + S₂sq ≠ 0) :
    canonicalQ13 (rawVarianceContrast σ₁sq σ₂sq)
        (rawResidualP13 σ₁sq σ₂sq S₁sq S₂sq)
        (rawResidualL13 σ₁sq σ₂sq S₁sq S₂sq)
        (standardizedDifference13 (rawVarianceSum σ₁sq σ₂sq) D)
      =
    13 * D ^ 2 / (S₁sq + S₂sq) := by
  unfold canonicalQ13
  rw [rawResidualL13_mul_canonicalDenom hσ₁ hσ₂ hsum hL]
  unfold standardizedDifference13
  field_simp

end

end GraybillDeal
