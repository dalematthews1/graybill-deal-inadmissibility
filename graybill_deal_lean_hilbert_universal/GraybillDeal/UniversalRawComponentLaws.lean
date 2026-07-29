import GraybillDeal.GeneralGaussianMeanBridge
import GraybillDeal.UnequalBlocks
import GraybillDeal.UniversalRawRiskTransport

/-!
# Universal component laws from two raw normal samples

This module packages the probability laws which precede the final
three-dimensional change of variables in the universal Graybill--Deal
argument.  The natural-number parameters `ν₁,ν₂` are residual degrees of
freedom, so the sample sizes are `ν₁+1,ν₂+1`.

For positive population variances put

```
τ = v₁/(ν₁+1) + v₂/(ν₂+1),
V = (Ȳ-X̄)²/τ,
U₁ = RSS₁/v₁,
U₂ = RSS₂/v₂.
```

Then

```
V  ~ Gamma(1/2, 1/2),
U₁ ~ Gamma(ν₁/2, 1/2),
U₂ ~ Gamma(ν₂/2, 1/2),
```

and the triple is jointly independent, hence has the corresponding product
law.  These statements hold for every positive pair of residual degrees of
freedom; there is no lower-shape restriction such as `1 < νᵢ/2`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Canonical independent components -/

/-- The population variance of `D = Ȳ-X̄`. -/
def universalRawDifferenceVariance
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal) : ℝ :=
  (v₁ : ℝ) / (ν₁ + 1) + (v₂ : ℝ) / (ν₂ + 1)

/-- The risk-bearing squared-normal component `V = D²/τ`. -/
def universalRawStandardizedDifferenceSquare
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  meanDifferenceU ν₁ ν₂ X Y ω ^ 2
    / universalRawDifferenceVariance ν₁ ν₂ v₁ v₂

/-- The first chi-square component `U₁ = RSS₁/v₁`. -/
def universalRawScaledResidual1
    (ν₁ : ℕ) (v₁ : NNReal)
    (X : Fin (ν₁ + 1) → Ω → ℝ) : Ω → ℝ :=
  scaledResidualSumSquaresN ν₁ (v₁ : ℝ) X

/-- The second chi-square component `U₂ = RSS₂/v₂`. -/
def universalRawScaledResidual2
    (ν₂ : ℕ) (v₂ : NNReal)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) : Ω → ℝ :=
  scaledResidualSumSquaresN ν₂ (v₂ : ℝ) Y

/-- The right-associated triple `(V,U₁,U₂)`. -/
def universalRawIndependentComponents
    (ν₁ ν₂ : ℕ) (v₁ v₂ : NNReal)
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ) (ω : Ω) :
    ℝ × ℝ × ℝ :=
  (universalRawStandardizedDifferenceSquare
      ν₁ ν₂ v₁ v₂ X Y ω,
    universalRawScaledResidual1 ν₁ v₁ X ω,
    universalRawScaledResidual2 ν₂ v₂ Y ω)

/-- The exact product measure of `(V,U₁,U₂)`. -/
def universalRawIndependentComponentMeasure
    (ν₁ ν₂ : ℕ) : Measure (ℝ × ℝ × ℝ) :=
  (gammaMeasure (1 / 2) (1 / 2)).prod
    ((gammaMeasure ((ν₁ : ℝ) / 2) (1 / 2)).prod
      (gammaMeasure ((ν₂ : ℝ) / 2) (1 / 2)))

/-! ## The exact squared-normal risk tilt -/

/-- Multiplying the `Gamma(1/2,1/2)` density by its coordinate raises the
shape to `3/2`; the normalizing constant is exactly one. -/
theorem gammaPDFReal_half_half_mul_id (x : ℝ) :
    gammaPDFReal (1 / 2) (1 / 2) x * x
      =
    gammaPDFReal (3 / 2) (1 / 2) x := by
  by_cases hx : 0 < x
  · rw [gammaPDFReal, if_pos hx.le, gammaPDFReal, if_pos hx.le]
    have hΓ :
        Real.Gamma (3 / 2 : ℝ)
          = (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
        Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    have hr :
        (1 / 2 : ℝ) ^ (3 / 2 : ℝ)
          = (1 / 2 : ℝ) ^ (1 / 2 : ℝ) * (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
        Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ)),
        Real.rpow_one]
    have hxpow :
        x ^ ((1 / 2 : ℝ) - 1) * x
          = x ^ ((3 / 2 : ℝ) - 1) := by
      calc
        x ^ ((1 / 2 : ℝ) - 1) * x
            =
          x ^ ((1 / 2 : ℝ) - 1) * x ^ (1 : ℝ) := by
            congr 1
            exact (Real.rpow_one x).symm
        _ = x ^ (((1 / 2 : ℝ) - 1) + 1) := by
          rw [Real.rpow_add hx]
        _ = x ^ ((3 / 2 : ℝ) - 1) := by
          congr 1
          ring
    rw [hΓ, hr, ← hxpow]
    field_simp [Real.Gamma_pos_of_pos (by norm_num :
      0 < (1 / 2 : ℝ))]
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    rcases hx0.eq_or_lt with rfl | hxneg
    · norm_num [gammaPDFReal]
    · rw [gammaPDFReal, if_neg hxneg.not_ge,
        gammaPDFReal, if_neg hxneg.not_ge]
      simp

theorem gammaPDF_half_half_mul_ofReal (x : ℝ) :
    gammaPDF (1 / 2) (1 / 2) x * ENNReal.ofReal x
      =
    gammaPDF (3 / 2) (1 / 2) x := by
  unfold gammaPDF
  rw [← ENNReal.ofReal_mul
    (gammaPDFReal_nonneg (by norm_num) (by norm_num) x)]
  rw [gammaPDFReal_half_half_mul_id]

/-- Size-biasing a squared standard Gaussian by its value produces
`Gamma(3/2,1/2)` with no additional scalar. -/
theorem gammaMeasure_half_half_withDensity_id :
    (gammaMeasure (1 / 2) (1 / 2)).withDensity
        (fun x : ℝ => ENNReal.ofReal x)
      =
    gammaMeasure (3 / 2) (1 / 2) := by
  unfold gammaMeasure
  change
    (volume.withDensity
      (fun x : ℝ =>
        ENNReal.ofReal (gammaPDFReal (1 / 2) (1 / 2) x))).withDensity
          (fun x : ℝ => ENNReal.ofReal x)
      =
    volume.withDensity
      (fun x : ℝ =>
        ENNReal.ofReal (gammaPDFReal (3 / 2) (1 / 2) x))
  have hid : Measurable (fun x : ℝ => ENNReal.ofReal x) := by
    fun_prop
  rw [← withDensity_mul volume
    (measurable_gammaPDFReal (1 / 2) (1 / 2)).ennreal_ofReal
    hid]
  apply withDensity_congr_ae
  exact ae_of_all _ gammaPDF_half_half_mul_ofReal

/-- Push a density depending only on a random variable through its law.
This is the abstract measure-theoretic step behind risk tilting. -/
theorem HasLaw.map_withDensity_comp
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {Z : S → T} {P : Measure S} {M : Measure T}
    (hZ : HasLaw Z M P) (w : T → ℝ≥0∞) (hw : Measurable w) :
    Measure.map Z (P.withDensity (fun ω => w (Z ω)))
      =
    M.withDensity w := by
  have hwZ : AEMeasurable (fun ω => w (Z ω)) P :=
    hw.comp_aemeasurable hZ.aemeasurable
  have hZtilted :
      AEMeasurable Z (P.withDensity (fun ω => w (Z ω))) :=
    hZ.aemeasurable.mono_ac
      (withDensity_absolutelyContinuous P (fun ω => w (Z ω)))
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  calc
    (∫⁻ z, f z
        ∂Measure.map Z (P.withDensity (fun ω => w (Z ω))))
        =
      ∫⁻ ω, f (Z ω)
        ∂P.withDensity (fun ω => w (Z ω)) := by
          rw [lintegral_map' hf.aemeasurable hZtilted]
    _ = ∫⁻ ω, w (Z ω) * f (Z ω) ∂P := by
      simpa only [Function.comp_apply, Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul₀
          hwZ (hf.comp_aemeasurable hZ.aemeasurable))
    _ = ∫⁻ z, w z * f z ∂M := by
      simpa only [Function.comp_apply, Pi.mul_apply] using
        hZ.lintegral_comp (hw.mul hf).aemeasurable
    _ = ∫⁻ z, f z ∂M.withDensity w := by
      simpa only [Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul M hw hf).symm

/-- The product component measure after size-biasing its first coordinate. -/
def universalRawRiskTiltedIndependentComponentMeasure
    (ν₁ ν₂ : ℕ) : Measure (ℝ × ℝ × ℝ) :=
  (gammaMeasure (3 / 2) (1 / 2)).prod
    ((gammaMeasure ((ν₁ : ℝ) / 2) (1 / 2)).prod
      (gammaMeasure ((ν₂ : ℝ) / 2) (1 / 2)))

/-- Size-biasing the product law by `V` changes only the first gamma shape,
from `1/2` to `3/2`. -/
theorem universalRawIndependentComponentMeasure_withDensity_fst
    (ν₁ ν₂ : ℕ) :
    (universalRawIndependentComponentMeasure ν₁ ν₂).withDensity
        (fun z => ENNReal.ofReal z.1)
      =
    universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂ := by
  letI : SigmaFinite
      (gammaMeasure ((ν₁ : ℝ) / 2) (1 / 2)) := by
    unfold gammaMeasure gammaPDF
    infer_instance
  letI : SigmaFinite
      (gammaMeasure ((ν₂ : ℝ) / 2) (1 / 2)) := by
    unfold gammaMeasure gammaPDF
    infer_instance
  unfold universalRawIndependentComponentMeasure
    universalRawRiskTiltedIndependentComponentMeasure
  have hid : Measurable (fun x : ℝ => ENNReal.ofReal x) := by
    fun_prop
  rw [← prod_withDensity_left hid,
    gammaMeasure_half_half_withDensity_id]

@[measurability, fun_prop]
theorem measurable_universalRawStandardizedDifferenceSquare
    {ν₁ ν₂ : ℕ} {v₁ v₂ : NNReal}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j)) :
    Measurable
      (universalRawStandardizedDifferenceSquare
        ν₁ ν₂ v₁ v₂ X Y) := by
  unfold universalRawStandardizedDifferenceSquare
  fun_prop

@[measurability, fun_prop]
theorem measurable_universalRawScaledResidual1
    {ν₁ : ℕ} {v₁ : NNReal}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    Measurable (universalRawScaledResidual1 ν₁ v₁ X) :=
  measurable_scaledResidualSumSquaresN hX _

@[measurability, fun_prop]
theorem measurable_universalRawScaledResidual2
    {ν₂ : ℕ} {v₂ : NNReal}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    (hY : ∀ j, Measurable (Y j)) :
    Measurable (universalRawScaledResidual2 ν₂ v₂ Y) :=
  measurable_scaledResidualSumSquaresN hY _

@[measurability, fun_prop]
theorem measurable_universalRawIndependentComponents
    {ν₁ ν₂ : ℕ} {v₁ v₂ : NNReal}
    {X : Fin (ν₁ + 1) → Ω → ℝ}
    {Y : Fin (ν₂ + 1) → Ω → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hY : ∀ j, Measurable (Y j)) :
    Measurable
      (universalRawIndependentComponents ν₁ ν₂ v₁ v₂ X Y) := by
  unfold universalRawIndependentComponents
  fun_prop

theorem universalRawDifferenceVariance_pos
    (ν₁ ν₂ : ℕ) {v₁ v₂ : NNReal}
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    0 < universalRawDifferenceVariance ν₁ ν₂ v₁ v₂ := by
  unfold universalRawDifferenceVariance
  positivity

/-- The defining normalization, in the direction used by the risk tilt:
`D² = τ V`. -/
theorem meanDifference_sq_eq_variance_mul_standardized
    {ν₁ ν₂ : ℕ} {v₁ v₂ : NNReal}
    (X : Fin (ν₁ + 1) → Ω → ℝ)
    (Y : Fin (ν₂ + 1) → Ω → ℝ)
    (hτ : 0 < universalRawDifferenceVariance ν₁ ν₂ v₁ v₂)
    (ω : Ω) :
    meanDifferenceU ν₁ ν₂ X Y ω ^ 2
      =
    universalRawDifferenceVariance ν₁ ν₂ v₁ v₂
      * universalRawStandardizedDifferenceSquare
          ν₁ ν₂ v₁ v₂ X Y ω := by
  unfold universalRawStandardizedDifferenceSquare
  field_simp

namespace TwoNormalSamplesU

variable {ν₁ ν₂ : ℕ}
  {X : Fin (ν₁ + 1) → Ω → ℝ}
  {Y : Fin (ν₂ + 1) → Ω → ℝ}
  {P : Measure Ω} {μ : ℝ} {v₁ v₂ : NNReal}

/-- Exact centered-normal law of `D`, restated using the real variance
constant used throughout this module. -/
theorem hasLaw_universalRawMeanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    HasLaw (meanDifferenceU ν₁ ν₂ X Y)
      (gaussianReal 0
        (universalRawDifferenceVariance ν₁ ν₂ v₁ v₂).toNNReal) P := by
  convert h.hasLaw_meanDifference using 1
  congr 1
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by
    unfold universalRawDifferenceVariance
    positivity)]
  push_cast
  rfl

/-- `V = D²/τ` is exactly a squared standard Gaussian. -/
theorem hasLaw_universalRawStandardizedDifferenceSquare
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    HasLaw
      (universalRawStandardizedDifferenceSquare
        ν₁ ν₂ v₁ v₂ X Y)
      (gammaMeasure (1 / 2) (1 / 2)) P := by
  let τ := universalRawDifferenceVariance ν₁ ν₂ v₁ v₂
  have hτ : 0 < τ :=
    universalRawDifferenceVariance_pos ν₁ ν₂ hv₁ hv₂
  have hD :
      HasLaw (meanDifferenceU ν₁ ν₂ X Y)
        (gaussianReal 0 (τ / (((0 : ℕ) : ℝ) + 1)).toNNReal) P := by
    simpa [τ] using h.hasLaw_universalRawMeanDifference
  have hout :=
    hasLaw_generalStandardizedDifference_of_gaussian
      0 τ (meanDifferenceU ν₁ ν₂ X Y) P hτ hD
  apply hout.congr
  filter_upwards [] with ω
  simp [universalRawStandardizedDifferenceSquare,
    generalStandardizedDifference, τ]

/-- Exact first residual law, valid for every positive `ν₁`. -/
theorem hasLaw_universalRawScaledResidual1
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hv₁ : 0 < (v₁ : ℝ)) :
    HasLaw (universalRawScaledResidual1 ν₁ v₁ X)
      (gammaMeasure ((ν₁ : ℝ) / 2) (1 / 2)) P :=
  h.hasLaw_scaledResidualSumSquaresX hν₁ hv₁

/-- Exact second residual law, valid for every positive `ν₂`. -/
theorem hasLaw_universalRawScaledResidual2
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₂ : 0 < ν₂) (hv₂ : 0 < (v₂ : ℝ)) :
    HasLaw (universalRawScaledResidual2 ν₂ v₂ Y)
      (gammaMeasure ((ν₂ : ℝ) / 2) (1 / 2)) P :=
  h.hasLaw_scaledResidualSumSquaresY hν₂ hv₂

/-- The two standardized residual sums remain independent. -/
theorem indepFun_universalRawScaledResiduals
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    IndepFun
      (universalRawScaledResidual1 ν₁ v₁ X)
      (universalRawScaledResidual2 ν₂ v₂ Y) P :=
  h.indepFun_scaledResidualSumSquares

/-- `V` is independent of the pair `(U₁,U₂)`. -/
theorem indepFun_universalRawStandardizedDifferenceSquare_scaledResiduals
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    IndepFun
      (universalRawStandardizedDifferenceSquare
        ν₁ ν₂ v₁ v₂ X Y)
      (fun ω =>
        (universalRawScaledResidual1 ν₁ v₁ X ω,
          universalRawScaledResidual2 ν₂ v₂ Y ω)) P := by
  have hout :=
    h.indepFun_meanDifference_residualSumSquares.comp
      (show Measurable
          (fun d : ℝ =>
            d ^ 2 / universalRawDifferenceVariance ν₁ ν₂ v₁ v₂) by
        fun_prop)
      (show Measurable
          (fun z : ℝ × ℝ =>
            (z.1 / (v₁ : ℝ), z.2 / (v₂ : ℝ))) by
        fun_prop)
  apply hout.congr
  · filter_upwards [] with ω
    rfl
  · filter_upwards [] with ω
    rfl

/-- Exact product law of the independent residual pair. -/
theorem hasLaw_universalRawScaledResidualPair
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    HasLaw
      (fun ω =>
        (universalRawScaledResidual1 ν₁ v₁ X ω,
          universalRawScaledResidual2 ν₂ v₂ Y ω))
      ((gammaMeasure ((ν₁ : ℝ) / 2) (1 / 2)).prod
        (gammaMeasure ((ν₂ : ℝ) / 2) (1 / 2))) P := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  exact IndepFun.hasLaw_prod
    (h.hasLaw_universalRawScaledResidual1 hν₁ hv₁)
    (h.hasLaw_universalRawScaledResidual2 hν₂ hv₂)
    h.indepFun_universalRawScaledResiduals

/--
The complete component law.  This is the exact product measure used before
the final deterministic coordinate change.
-/
theorem hasLaw_universalRawIndependentComponents
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    HasLaw
      (universalRawIndependentComponents ν₁ ν₂ v₁ v₂ X Y)
      (universalRawIndependentComponentMeasure ν₁ ν₂) P := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  exact IndepFun.hasLaw_prod
    (h.hasLaw_universalRawStandardizedDifferenceSquare hv₁ hv₂)
    (h.hasLaw_universalRawScaledResidualPair
      hν₁ hν₂ hv₁ hv₂)
    h.indepFun_universalRawStandardizedDifferenceSquare_scaledResiduals

set_option maxHeartbeats 800000 in
/--
The exact **risk-tilted component law**.  Weighting the raw probability
measure by `D²`:

* contributes the scalar `τ = Var(D)`;
* raises the squared-normal shape from `1/2` to `3/2`;
* leaves both residual gamma laws unchanged.

This equality is deliberately unnormalised: both sides have total mass
`τ`, exactly as required by squared-risk comparison.
-/
theorem map_universalRawIndependentComponents_withDensity_sq_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂)
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hv₁ : 0 < (v₁ : ℝ)) (hv₂ : 0 < (v₂ : ℝ)) :
    Measure.map
        (universalRawIndependentComponents ν₁ ν₂ v₁ v₂ X Y)
        (P.withDensity
          (fun ω =>
            ENNReal.ofReal
              (meanDifferenceU ν₁ ν₂ X Y ω ^ 2)))
      =
    ENNReal.ofReal
        (universalRawDifferenceVariance ν₁ ν₂ v₁ v₂)
      • universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂ := by
  let C :=
    universalRawIndependentComponents ν₁ ν₂ v₁ v₂ X Y
  let τ := universalRawDifferenceVariance ν₁ ν₂ v₁ v₂
  have hτ : 0 < τ :=
    universalRawDifferenceVariance_pos ν₁ ν₂ hv₁ hv₂
  have hC :
      HasLaw C (universalRawIndependentComponentMeasure ν₁ ν₂) P := by
    exact h.hasLaw_universalRawIndependentComponents
      hν₁ hν₂ hv₁ hv₂
  have hweight :
      (fun ω =>
        ENNReal.ofReal (meanDifferenceU ν₁ ν₂ X Y ω ^ 2))
        =
      (fun ω => ENNReal.ofReal (τ * (C ω).1)) := by
    funext ω
    congr 1
    exact meanDifference_sq_eq_variance_mul_standardized
      X Y hτ ω
  have hw :
      Measurable
        (fun z : ℝ × ℝ × ℝ => ENNReal.ofReal (τ * z.1)) := by
    fun_prop
  have hfirst :
      Measurable
        (fun z : ℝ × ℝ × ℝ => ENNReal.ofReal z.1) := by
    fun_prop
  calc
    Measure.map C
        (P.withDensity
          (fun ω =>
            ENNReal.ofReal
              (meanDifferenceU ν₁ ν₂ X Y ω ^ 2)))
        =
      Measure.map C
        (P.withDensity (fun ω => ENNReal.ofReal (τ * (C ω).1))) := by
          rw [hweight]
    _ =
      (universalRawIndependentComponentMeasure ν₁ ν₂).withDensity
        (fun z => ENNReal.ofReal (τ * z.1)) :=
      GraybillDeal.HasLaw.map_withDensity_comp hC _ hw
    _ =
      (universalRawIndependentComponentMeasure ν₁ ν₂).withDensity
        (ENNReal.ofReal τ •
          (fun z => ENNReal.ofReal z.1)) := by
            congr 1
            funext z
            simp only [Pi.smul_apply, smul_eq_mul]
            rw [ENNReal.ofReal_mul hτ.le]
    _ =
      ENNReal.ofReal τ
        • (universalRawIndependentComponentMeasure ν₁ ν₂).withDensity
          (fun z => ENNReal.ofReal z.1) := by
            rw [withDensity_smul (ENNReal.ofReal τ) hfirst]
    _ =
      ENNReal.ofReal τ
        • universalRawRiskTiltedIndependentComponentMeasure ν₁ ν₂ := by
          rw [universalRawIndependentComponentMeasure_withDensity_fst]

/-! ## Exact risk-bearing moments -/

/-- The squared mean difference is integrable. -/
theorem integrable_sq_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    Integrable (fun ω => meanDifferenceU ν₁ ν₂ X Y ω ^ 2) P := by
  exact
    (memLp_two_iff_integrable_sq
      h.hasGaussianLaw_meanDifference.aemeasurable.aestronglyMeasurable).1
      h.hasGaussianLaw_meanDifference.memLp_two

/-- Exact first risk-bearing moment: `E[D²] = τ`. -/
theorem integral_sq_meanDifference
    (h : TwoNormalSamplesU ν₁ ν₂ X Y P μ v₁ v₂) :
    (∫ ω, meanDifferenceU ν₁ ν₂ X Y ω ^ 2 ∂P)
      =
    universalRawDifferenceVariance ν₁ ν₂ v₁ v₂ := by
  letI : IsProbabilityMeasure P := h.indep.isProbabilityMeasure
  have hvar :=
    variance_eq_integral
      h.hasGaussianLaw_meanDifference.aemeasurable
  rw [h.integral_meanDifference] at hvar
  simp only [sub_zero] at hvar
  calc
    (∫ ω, meanDifferenceU ν₁ ν₂ X Y ω ^ 2 ∂P)
        =
      ProbabilityTheory.variance
        (meanDifferenceU ν₁ ν₂ X Y) P := hvar.symm
    _ = universalRawDifferenceVariance ν₁ ν₂ v₁ v₂ := by
      exact h.variance_meanDifference

end TwoNormalSamplesU

end

end GraybillDeal
