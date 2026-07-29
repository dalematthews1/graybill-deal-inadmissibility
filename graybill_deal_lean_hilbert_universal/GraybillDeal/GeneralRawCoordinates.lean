import GraybillDeal.GeneralCanonical
import GraybillDeal.RawCoordinates

/-!
# Raw variance coordinates at arbitrary equal sample size

This is the sample-size-generic deterministic identification layer.  The
natural number `ν` is the residual degrees of freedom, so the two samples
have size `ν + 1`.

For population variances `σ₀², σ₁²` and observed unbiased sample variances
`S₀², S₁²`, put

* `Uᵢ = ν Sᵢ² / σᵢ²`,
* `P = U₀ / (U₀ + U₁)`,
* `L = U₀ + U₁`,
* `V = (ν+1)D² / (σ₀²+σ₁²)`.

The results below identify the canonical weight and quadratic statistic with
the literal Graybill--Deal quantities

* `S₀² / (S₀² + S₁²)`, and
* `(ν+1)D² / (S₀² + S₁²)`.
-/

namespace GraybillDeal

noncomputable section

/-- Standardized residual sum of squares with residual degrees of freedom `ν`. -/
def rawResidualScaleN (ν : ℕ) (σsq Ssq : ℝ) : ℝ :=
  (ν : ℝ) * Ssq / σsq

/-- Sum coordinate of the two standardized residual sums of squares. -/
def rawResidualLN
    (ν : ℕ) (σ₀sq σ₁sq S₀sq S₁sq : ℝ) : ℝ :=
  rawResidualScaleN ν σ₀sq S₀sq
    + rawResidualScaleN ν σ₁sq S₁sq

/-- Ratio coordinate of the two standardized residual sums of squares. -/
def rawResidualPN
    (ν : ℕ) (σ₀sq σ₁sq S₀sq S₁sq : ℝ) : ℝ :=
  rawResidualScaleN ν σ₀sq S₀sq
    / rawResidualLN ν σ₀sq σ₁sq S₀sq S₁sq

/--
Nonvanishing of the standardized residual sum forces nonvanishing of its
common-denominator numerator.
-/
theorem rawResidualN_cross_ne
    {ν : ℕ} {σ₀sq σ₁sq S₀sq S₁sq : ℝ}
    (hν : 0 < ν)
    (hσ₀ : σ₀sq ≠ 0) (hσ₁ : σ₁sq ≠ 0)
    (hL : rawResidualLN ν σ₀sq σ₁sq S₀sq S₁sq ≠ 0) :
    S₀sq * σ₁sq + σ₀sq * S₁sq ≠ 0 := by
  intro hcross
  apply hL
  unfold rawResidualLN rawResidualScaleN
  have hνR : (ν : ℝ) ≠ 0 := by exact_mod_cast hν.ne'
  field_simp [hσ₀, hσ₁, hνR]
  nlinarith [hcross]

/--
The product `L d` is the total raw sample variance in canonical units.
-/
theorem rawResidualLN_mul_canonicalDenom
    {ν : ℕ} {σ₀sq σ₁sq S₀sq S₁sq : ℝ}
    (hν : 0 < ν)
    (hσ₀ : σ₀sq ≠ 0) (hσ₁ : σ₁sq ≠ 0)
    (hsum : rawVarianceSum σ₀sq σ₁sq ≠ 0)
    (hL : rawResidualLN ν σ₀sq σ₁sq S₀sq S₁sq ≠ 0) :
    rawResidualLN ν σ₀sq σ₁sq S₀sq S₁sq
        * canonicalDenom (rawVarianceContrast σ₀sq σ₁sq)
          (rawResidualPN ν σ₀sq σ₁sq S₀sq S₁sq)
      =
    (ν : ℝ) * (S₀sq + S₁sq) / rawVarianceSum σ₀sq σ₁sq := by
  have hcross :=
    rawResidualN_cross_ne hν hσ₀ hσ₁ hL
  rw [show canonicalDenom (rawVarianceContrast σ₀sq σ₁sq)
        (rawResidualPN ν σ₀sq σ₁sq S₀sq S₁sq)
      =
      canonicalTheta (rawVarianceContrast σ₀sq σ₁sq)
          * rawResidualPN ν σ₀sq σ₁sq S₀sq S₁sq
        + (1 - canonicalTheta (rawVarianceContrast σ₀sq σ₁sq))
          * (1 - rawResidualPN ν σ₀sq σ₁sq S₀sq S₁sq) by rfl]
  rw [one_sub_canonicalTheta_rawVarianceContrast hsum,
    canonicalTheta_rawVarianceContrast hsum]
  unfold rawResidualPN rawResidualLN rawResidualScaleN rawVarianceSum
  unfold rawResidualLN rawResidualScaleN at hL
  unfold rawVarianceSum at hsum
  have hνR : (ν : ℝ) ≠ 0 := by exact_mod_cast hν.ne'
  field_simp [hσ₀, hσ₁, hsum, hL, hcross, hνR]
  ring

/-- The canonical base weight is exactly the Graybill--Deal sample weight. -/
theorem canonicalR_rawResidualPN
    {ν : ℕ} {σ₀sq σ₁sq S₀sq S₁sq : ℝ}
    (hν : 0 < ν)
    (hσ₀ : σ₀sq ≠ 0) (hσ₁ : σ₁sq ≠ 0)
    (hsum : rawVarianceSum σ₀sq σ₁sq ≠ 0)
    (hL : rawResidualLN ν σ₀sq σ₁sq S₀sq S₁sq ≠ 0)
    (hSsum : S₀sq + S₁sq ≠ 0) :
    canonicalR (rawVarianceContrast σ₀sq σ₁sq)
        (rawResidualPN ν σ₀sq σ₁sq S₀sq S₁sq)
      =
    S₀sq / (S₀sq + S₁sq) := by
  have hcross :=
    rawResidualN_cross_ne hν hσ₀ hσ₁ hL
  unfold canonicalR
  rw [canonicalTheta_rawVarianceContrast hsum]
  have hden :
      canonicalDenom (rawVarianceContrast σ₀sq σ₁sq)
          (rawResidualPN ν σ₀sq σ₁sq S₀sq S₁sq)
        =
      ((ν : ℝ) * (S₀sq + S₁sq) / rawVarianceSum σ₀sq σ₁sq)
        / rawResidualLN ν σ₀sq σ₁sq S₀sq S₁sq := by
    apply (eq_div_iff hL).2
    rw [mul_comm]
    exact rawResidualLN_mul_canonicalDenom
      hν hσ₀ hσ₁ hsum hL
  rw [hden]
  unfold rawResidualPN rawResidualLN rawResidualScaleN rawVarianceSum
  unfold rawResidualLN rawResidualScaleN at hL
  unfold rawVarianceSum at hsum
  have hνR : (ν : ℝ) ≠ 0 := by exact_mod_cast hν.ne'
  field_simp [hσ₀, hσ₁, hsum, hL, hSsum, hcross, hνR]
  field_simp [hcross]

/--
The canonical statistic is exactly
`(ν+1)D² / (S₀²+S₁²)`.
-/
theorem canonicalQ_rawResidual_coordinates
    {ν : ℕ} {σ₀sq σ₁sq S₀sq S₁sq D : ℝ}
    (hν : 0 < ν)
    (hσ₀ : σ₀sq ≠ 0) (hσ₁ : σ₁sq ≠ 0)
    (hsum : rawVarianceSum σ₀sq σ₁sq ≠ 0)
    (hL : rawResidualLN ν σ₀sq σ₁sq S₀sq S₁sq ≠ 0)
    (hSsum : S₀sq + S₁sq ≠ 0) :
    canonicalQ (ν : ℝ)
        (canonicalTheta (rawVarianceContrast σ₀sq σ₁sq))
        (rawResidualPN ν σ₀sq σ₁sq S₀sq S₁sq)
        (rawResidualLN ν σ₀sq σ₁sq S₀sq S₁sq)
        (generalStandardizedDifference
          (ν : ℝ) (rawVarianceSum σ₀sq σ₁sq) D)
      =
    ((ν : ℝ) + 1) * D ^ 2 / (S₀sq + S₁sq) := by
  unfold canonicalQ
  rw [canonicalDenomTheta_canonicalTheta]
  rw [rawResidualLN_mul_canonicalDenom
    hν hσ₀ hσ₁ hsum hL]
  unfold generalStandardizedDifference
  have hνR : (ν : ℝ) ≠ 0 := by exact_mod_cast hν.ne'
  field_simp [hνR, hsum, hSsum]

end

end GraybillDeal
