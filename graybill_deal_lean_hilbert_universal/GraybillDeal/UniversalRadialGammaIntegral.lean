import GraybillDeal.UniversalReducedDensity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The radial Gamma integral in the universal reduced experiment

After the positive-coordinate substitution

```
(r,q,t) ↦ (r*t, (1-r)*t, q*t),
```

the powers of the three canonical coordinates together with the Jacobian
`t²` give the radial power

```
t ^ (a + b + 1/2).
```

Equivalently, this is the Gamma integrand with shape
`a + b + 3/2`.  This file proves the required measurability,
integrability, and exact integral for every `a,b > 0`.  It then checks
algebraically that integrating the natural pre-radial density gives
`universalFullReducedDensity`.

No probability law is assumed here: the results are purely analytic.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

/-- Shape of the one-dimensional radial Gamma integral. -/
def universalRadialShape (a b : ℝ) : ℝ :=
  a + b + 3 / 2

/-- The radial Gamma integrand obtained after the three-coordinate
change of variables. -/
def universalRadialGammaIntegrand
    (a b r q θ t : ℝ) : ℝ :=
  t ^ (universalRadialShape a b - 1)
    * Real.exp (-(universalRadialRate a b r q θ * t))

theorem universalRadialShape_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < universalRadialShape a b := by
  unfold universalRadialShape
  linarith

theorem universalRadialShape_sub_one
    (a b : ℝ) :
    universalRadialShape a b - 1 = a + b + 1 / 2 := by
  unfold universalRadialShape
  ring

theorem measurable_universalRadialGammaIntegrand
    (a b r q θ : ℝ) :
    Measurable (universalRadialGammaIntegrand a b r q θ) := by
  unfold universalRadialGammaIntegrand
  fun_prop

theorem stronglyMeasurable_universalRadialGammaIntegrand
    (a b r q θ : ℝ) :
    StronglyMeasurable (universalRadialGammaIntegrand a b r q θ) :=
  (measurable_universalRadialGammaIntegrand a b r q θ).stronglyMeasurable

theorem universalRadialGammaIntegrand_nonneg
    (a b r q θ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ universalRadialGammaIntegrand a b r q θ t := by
  unfold universalRadialGammaIntegrand
  positivity

theorem universalRadialGammaIntegrand_pos
    (a b r q θ : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < universalRadialGammaIntegrand a b r q θ t := by
  unfold universalRadialGammaIntegrand
  exact mul_pos (Real.rpow_pos_of_pos ht _)
    (Real.exp_pos _)

/-- The radial integrand is integrable on the positive half-line whenever
the Gamma shape and exponential rate are positive. -/
theorem integrableOn_universalRadialGammaIntegrand
    {a b r q θ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hq : 0 < q) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    IntegrableOn
      (universalRadialGammaIntegrand a b r q θ) (Ioi 0) := by
  have hshape : 0 < universalRadialShape a b :=
    universalRadialShape_pos ha hb
  have hrate : 0 < universalRadialRate a b r q θ :=
    universalRadialRate_pos ha hb hr0 hr1 hq hθ0 hθ1
  have hbase :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ))
      (s := universalRadialShape a b - 1)
      (b := universalRadialRate a b r q θ)
      (by linarith) (by norm_num) hrate
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro t ht
  unfold universalRadialGammaIntegrand
  simp only [Real.rpow_one]
  congr 2
  ring

/-- Exact evaluation of the radial integral in its direct Gamma form. -/
theorem integral_universalRadialGammaIntegrand
    {a b r q θ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hq : 0 < q) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∫ t : ℝ in Ioi 0,
        universalRadialGammaIntegrand a b r q θ t
      =
    (1 / universalRadialRate a b r q θ) ^
        universalRadialShape a b
      * Real.Gamma (universalRadialShape a b) := by
  have hshape : 0 < universalRadialShape a b :=
    universalRadialShape_pos ha hb
  have hrate : 0 < universalRadialRate a b r q θ :=
    universalRadialRate_pos ha hb hr0 hr1 hq hθ0 hθ1
  exact Real.integral_rpow_mul_exp_neg_mul_Ioi hshape hrate

/-- The same exact evaluation with the reciprocal power written as a
negative power of the rate. -/
theorem integral_universalRadialGammaIntegrand_eq_rpow_neg
    {a b r q θ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hq : 0 < q) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∫ t : ℝ in Ioi 0,
        universalRadialGammaIntegrand a b r q θ t
      =
    universalRadialRate a b r q θ ^
        (-universalRadialShape a b)
      * Real.Gamma (universalRadialShape a b) := by
  rw [integral_universalRadialGammaIntegrand
    ha hb hr0 hr1 hq hθ0 hθ1]
  have hrate : 0 < universalRadialRate a b r q θ :=
    universalRadialRate_pos ha hb hr0 hr1 hq hθ0 hθ1
  rw [one_div, ← Real.rpow_neg_one]
  rw [← Real.rpow_mul hrate.le]
  congr 2
  ring

/-- The non-radial factor of the transformed canonical density before
integrating out `t`. -/
def universalPreRadialFactor
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) : ℝ :=
  a ^ a * b ^ b
      / (Real.sqrt (2 * Real.pi) * Real.Gamma a * Real.Gamma b)
    * (θ : ℝ) ^ (-a)
    * (1 - (θ : ℝ)) ^ (-b)
    * x.r ^ (a - 1)
    * (1 - x.r) ^ (b - 1)
    * x.q ^ (1 / 2 : ℝ)

/-- The full transformed density in `(r,q,t)` coordinates, prior to
radial integration. -/
def universalPreRadialDensity
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) (t : ℝ) : ℝ :=
  universalPreRadialFactor a b θ x
    * universalRadialGammaIntegrand
        a b x.r x.q (θ : ℝ) t

theorem measurable_universalPreRadialDensity
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    Measurable (universalPreRadialDensity a b θ x) := by
  unfold universalPreRadialDensity
  exact measurable_const.mul
    (measurable_universalRadialGammaIntegrand
      a b x.r x.q (θ : ℝ))

theorem integrableOn_universalPreRadialDensity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    IntegrableOn
      (universalPreRadialDensity a b θ x) (Ioi 0) := by
  unfold universalPreRadialDensity
  exact
    (integrableOn_universalRadialGammaIntegrand
      ha hb x.r_pos x.r_lt_one x.q_pos
        θ.property.1 θ.property.2).const_mul _

/-- Integrating the pre-radial density first gives the expected Gamma
factor. -/
theorem integral_universalPreRadialDensity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    ∫ t : ℝ in Ioi 0, universalPreRadialDensity a b θ x t
      =
    universalPreRadialFactor a b θ x
      * (universalRadialRate a b x.r x.q (θ : ℝ) ^
          (-universalRadialShape a b)
        * Real.Gamma (universalRadialShape a b)) := by
  unfold universalPreRadialDensity
  rw [MeasureTheory.integral_const_mul]
  rw [integral_universalRadialGammaIntegrand_eq_rpow_neg
    ha hb x.r_pos x.r_lt_one x.q_pos
      θ.property.1 θ.property.2]

/-- The integrated pre-radial density is exactly the full reduced density
used by the universal decision-theoretic argument. -/
theorem universalPreRadialFactor_mul_gamma_eq_fullReducedDensity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    universalPreRadialFactor a b θ x
        * (universalRadialRate a b x.r x.q (θ : ℝ) ^
            (-universalRadialShape a b)
          * Real.Gamma (universalRadialShape a b))
      =
    universalFullReducedDensity a b θ x := by
  rw [universalFullReducedDensity_eq_explicit]
  have hB :
      universalB a b x.r x.q
          (universalInteriorThetaInclusion θ)
        =
      2 * (θ : ℝ) * (1 - (θ : ℝ))
        * universalRadialRate a b x.r x.q (θ : ℝ) := by
    exact universalB_eq_two_mul_radialRate
      θ.property.1 θ.property.2
  rw [hB]
  unfold universalPreRadialFactor universalRadialShape
    universalReducedDensityConstant
  have hθ0 : 0 < (θ : ℝ) := θ.property.1
  have hθ1 : (θ : ℝ) < 1 := θ.property.2
  have h1θ : 0 < 1 - (θ : ℝ) := sub_pos.mpr hθ1
  have hrate : 0 < universalRadialRate a b x.r x.q (θ : ℝ) :=
    universalRadialRate_pos ha hb x.r_pos x.r_lt_one x.q_pos
      hθ0 hθ1
  rw [Real.mul_rpow
    (mul_nonneg (mul_nonneg (by norm_num) hθ0.le) h1θ.le)
    hrate.le]
  rw [Real.mul_rpow
    (mul_nonneg (by norm_num) hθ0.le) h1θ.le]
  rw [Real.mul_rpow (by norm_num) hθ0.le]
  have htwoPow :
      (2 : ℝ) ^ (a + b + 3 / 2)
          * 2 ^ (-(a + b + 3 / 2)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hθPow :
      (θ : ℝ) ^ (b + 3 / 2)
          * (θ : ℝ) ^ (-(a + b + 3 / 2))
        =
      (θ : ℝ) ^ (-a) := by
    rw [← Real.rpow_add hθ0]
    congr 1
    ring
  have h1θPow :
      (1 - (θ : ℝ)) ^ (a + 3 / 2)
          * (1 - (θ : ℝ)) ^ (-(a + b + 3 / 2))
        =
      (1 - (θ : ℝ)) ^ (-b) := by
    rw [← Real.rpow_add h1θ]
    congr 1
    ring
  have hendpoint :
      (2 : ℝ) ^ (a + b + 3 / 2)
          * ((θ : ℝ) ^ (b + 3 / 2)
            * (1 - (θ : ℝ)) ^ (a + 3 / 2))
          * (2 ^ (-(a + b + 3 / 2))
            * (θ : ℝ) ^ (-(a + b + 3 / 2))
            * (1 - (θ : ℝ)) ^ (-(a + b + 3 / 2)))
        =
      (θ : ℝ) ^ (-a) * (1 - (θ : ℝ)) ^ (-b) := by
    calc
      _ =
          ((2 : ℝ) ^ (a + b + 3 / 2)
              * 2 ^ (-(a + b + 3 / 2)))
            * ((θ : ℝ) ^ (b + 3 / 2)
              * (θ : ℝ) ^ (-(a + b + 3 / 2)))
            * ((1 - (θ : ℝ)) ^ (a + 3 / 2)
              * (1 - (θ : ℝ)) ^
                  (-(a + b + 3 / 2))) := by ring
      _ = (θ : ℝ) ^ (-a) * (1 - (θ : ℝ)) ^ (-b) := by
        rw [htwoPow, hθPow, h1θPow]
        ring
  symm
  calc
    _ =
        (a ^ a * b ^ b
            / (Real.sqrt (2 * Real.pi)
              * Real.Gamma a * Real.Gamma b))
          * x.r ^ (a - 1)
          * (1 - x.r) ^ (b - 1)
          * x.q ^ (1 / 2 : ℝ)
          * ((2 : ℝ) ^ (a + b + 3 / 2)
            * ((θ : ℝ) ^ (b + 3 / 2)
              * (1 - (θ : ℝ)) ^ (a + 3 / 2))
            * (2 ^ (-(a + b + 3 / 2))
              * (θ : ℝ) ^ (-(a + b + 3 / 2))
              * (1 - (θ : ℝ)) ^ (-(a + b + 3 / 2))))
          * universalRadialRate a b x.r x.q (θ : ℝ) ^
              (-(a + b + 3 / 2))
          * Real.Gamma (a + b + 3 / 2) := by
        ring_nf
    _ =
        (a ^ a * b ^ b
            / (Real.sqrt (2 * Real.pi)
              * Real.Gamma a * Real.Gamma b))
          * x.r ^ (a - 1)
          * (1 - x.r) ^ (b - 1)
          * x.q ^ (1 / 2 : ℝ)
          * ((θ : ℝ) ^ (-a) * (1 - (θ : ℝ)) ^ (-b))
          * universalRadialRate a b x.r x.q (θ : ℝ) ^
              (-(a + b + 3 / 2))
          * Real.Gamma (a + b + 3 / 2) := by
        rw [hendpoint]
    _ = _ := by ring_nf

/-- The exact radial integration statement in the form needed by the
reduced-density pushforward. -/
theorem integral_universalPreRadialDensity_eq_fullReducedDensity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    ∫ t : ℝ in Ioi 0, universalPreRadialDensity a b θ x t
      =
    universalFullReducedDensity a b θ x := by
  rw [integral_universalPreRadialDensity ha hb θ x]
  exact universalPreRadialFactor_mul_gamma_eq_fullReducedDensity
    ha hb θ x

theorem universalPreRadialFactor_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    0 < universalPreRadialFactor a b θ x := by
  unfold universalPreRadialFactor
  have hden :
      0 < Real.sqrt (2 * Real.pi)
          * Real.Gamma a * Real.Gamma b := by
    have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
    have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
    positivity
  have haa : 0 < a ^ a := Real.rpow_pos_of_pos ha _
  have hbb : 0 < b ^ b := Real.rpow_pos_of_pos hb _
  have hθa : 0 < (θ : ℝ) ^ (-a) :=
    Real.rpow_pos_of_pos θ.property.1 _
  have hθb : 0 < (1 - (θ : ℝ)) ^ (-b) :=
    Real.rpow_pos_of_pos (sub_pos.mpr θ.property.2) _
  have hra : 0 < x.r ^ (a - 1) :=
    Real.rpow_pos_of_pos x.r_pos _
  have hrb : 0 < (1 - x.r) ^ (b - 1) :=
    Real.rpow_pos_of_pos (sub_pos.mpr x.r_lt_one) _
  have hq : 0 < x.q ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos x.q_pos _
  positivity

theorem universalPreRadialDensity_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation)
    {t : ℝ} (ht : 0 < t) :
    0 < universalPreRadialDensity a b θ x t := by
  unfold universalPreRadialDensity
  exact mul_pos
    (universalPreRadialFactor_pos ha hb θ x)
    (universalRadialGammaIntegrand_pos
      a b x.r x.q (θ : ℝ) ht)

/-- `lintegral` form of the exact radial identity.  This is the version
that can be inserted directly into `withDensity` and pushforward
calculations. -/
theorem lintegral_universalPreRadialDensity_eq_fullReducedDensity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (universalPreRadialDensity a b θ x t)
      =
    ENNReal.ofReal (universalFullReducedDensity a b θ x) := by
  have hint :
      Integrable
        (universalPreRadialDensity a b θ x)
        ((volume : Measure ℝ).restrict (Ioi 0)) :=
    integrableOn_universalPreRadialDensity ha hb θ x
  have hnonneg :
      0 ≤ᵐ[((volume : Measure ℝ).restrict (Ioi 0))]
        universalPreRadialDensity a b θ x := by
    filter_upwards
      [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact (universalPreRadialDensity_pos
      ha hb θ x ht).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [integral_universalPreRadialDensity_eq_fullReducedDensity
    ha hb θ x]

/-! ## Direct bridge from the canonical positive triple -/

/-- The analytic weighted density of the positive canonical triple
`(g₁,g₂,w)`.  This is intentionally only a function: identifying a raw
probability law with this density is a separate probabilistic theorem. -/
def universalCanonicalWeightedTripleDensity
    (a b : ℝ) (θ : UniversalInteriorTheta)
    (z : ℝ × ℝ × ℝ) : ℝ :=
  a ^ a * b ^ b
      / (Real.sqrt (2 * Real.pi) * Real.Gamma a * Real.Gamma b)
    * (θ : ℝ) ^ (-a)
    * (1 - (θ : ℝ)) ^ (-b)
    * z.1 ^ (a - 1)
    * z.2.1 ^ (b - 1)
    * z.2.2 ^ (1 / 2 : ℝ)
    * Real.exp
        (-(a * z.1 / (θ : ℝ)
          + b * z.2.1 / (1 - (θ : ℝ))
          + z.2.2 / 2))

theorem measurable_universalCanonicalWeightedTripleDensity
    (a b : ℝ) (θ : UniversalInteriorTheta) :
    Measurable (universalCanonicalWeightedTripleDensity a b θ) := by
  unfold universalCanonicalWeightedTripleDensity
  fun_prop

theorem universalCanonicalWeightedTripleDensity_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    {z : ℝ × ℝ × ℝ}
    (hg₁ : 0 < z.1) (hg₂ : 0 < z.2.1) (hw : 0 < z.2.2) :
    0 < universalCanonicalWeightedTripleDensity a b θ z := by
  unfold universalCanonicalWeightedTripleDensity
  have hden :
      0 < Real.sqrt (2 * Real.pi)
          * Real.Gamma a * Real.Gamma b := by
    have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
    have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
    positivity
  have haa : 0 < a ^ a := Real.rpow_pos_of_pos ha _
  have hbb : 0 < b ^ b := Real.rpow_pos_of_pos hb _
  have hθa : 0 < (θ : ℝ) ^ (-a) :=
    Real.rpow_pos_of_pos θ.property.1 _
  have hθb : 0 < (1 - (θ : ℝ)) ^ (-b) :=
    Real.rpow_pos_of_pos (sub_pos.mpr θ.property.2) _
  have hg₁pow : 0 < z.1 ^ (a - 1) :=
    Real.rpow_pos_of_pos hg₁ _
  have hg₂pow : 0 < z.2.1 ^ (b - 1) :=
    Real.rpow_pos_of_pos hg₂ _
  have hwpow : 0 < z.2.2 ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hw _
  positivity

/-- Pointwise Jacobian bridge from the canonical triple to the
pre-radial density.  The factor `t²` is the absolute inverse Jacobian. -/
theorem canonicalWeightedTripleDensity_comp_inverse_mul_jacobian
    (a b : ℝ)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation)
    {t : ℝ} (ht : 0 < t) :
    universalCanonicalWeightedTripleDensity a b θ
        (universalReducedInverseCoordinates x.r x.q t)
      * universalReducedInverseJacobian t
      =
    universalPreRadialDensity a b θ x t := by
  unfold universalCanonicalWeightedTripleDensity
    universalReducedInverseCoordinates
    universalReducedInverseJacobian
    universalPreRadialDensity
    universalPreRadialFactor
    universalRadialGammaIntegrand
  have hr0 : 0 < x.r := x.r_pos
  have hr1 : 0 < 1 - x.r := sub_pos.mpr x.r_lt_one
  have hq : 0 < x.q := x.q_pos
  rw [Real.mul_rpow hr0.le ht.le]
  rw [Real.mul_rpow hr1.le ht.le]
  rw [Real.mul_rpow hq.le ht.le]
  have hpow :
      t ^ (a - 1) * t ^ (b - 1)
          * t ^ (1 / 2 : ℝ) * t ^ 2
        =
      t ^ (universalRadialShape a b - 1) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add ht, ← Real.rpow_add ht,
      ← Real.rpow_add ht]
    unfold universalRadialShape
    congr 1
    norm_num
    ring
  have hexp :
      -(a * (x.r * t) / (θ : ℝ)
          + b * ((1 - x.r) * t) / (1 - (θ : ℝ))
          + x.q * t / 2)
        =
      -(universalRadialRate a b x.r x.q (θ : ℝ) * t) := by
    unfold universalRadialRate
    ring
  rw [hexp]
  ring_nf at hpow ⊢
  rw [← hpow]

/-- The canonical nested-triple integrand, its inverse Jacobian, and the
radial integral collapse directly to `universalFullReducedDensity`. -/
theorem lintegral_canonicalWeightedTripleDensity_comp_inverse
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal
          (universalCanonicalWeightedTripleDensity a b θ
              (universalReducedInverseCoordinates x.r x.q t)
            * universalReducedInverseJacobian t)
      =
    ENNReal.ofReal (universalFullReducedDensity a b θ x) := by
  calc
    _ =
        ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal
            (universalPreRadialDensity a b θ x t) := by
      exact setLIntegral_congr_fun measurableSet_Ioi
        (fun t ht => congrArg ENNReal.ofReal
          (canonicalWeightedTripleDensity_comp_inverse_mul_jacobian
            a b θ x ht))
    _ = _ :=
      lintegral_universalPreRadialDensity_eq_fullReducedDensity
        ha hb θ x

/-- Algebraic endpoint for a raw pushforward proof: if a reduced measure
has the density obtained by radial integration, then it satisfies the
`HasUniversalReducedDensity` interface exactly. -/
theorem hasUniversalReducedDensity_of_radial_lintegral
    {reference Q : Measure UniversalReducedObservation}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (hQ :
      Q =
        reference.withDensity
          (fun x =>
            ∫⁻ t : ℝ in Ioi 0,
              ENNReal.ofReal
                (universalPreRadialDensity a b θ x t))) :
    HasUniversalReducedDensity reference Q a b θ := by
  unfold HasUniversalReducedDensity
  rw [hQ]
  congr 1
  funext x
  exact
    lintegral_universalPreRadialDensity_eq_fullReducedDensity
      ha hb θ x

/-- A constant scale `τ` passes transparently through the radial
integration.  This is the normalization form used when the raw
risk-weighted law has density `τ` times the canonical reduced density. -/
theorem integral_const_mul_universalPreRadialDensity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (τ : ℝ)
    (θ : UniversalInteriorTheta)
    (x : UniversalReducedObservation) :
    ∫ t : ℝ in Ioi 0,
        τ * universalPreRadialDensity a b θ x t
      =
    τ * universalFullReducedDensity a b θ x := by
  rw [MeasureTheory.integral_const_mul]
  rw [integral_universalPreRadialDensity_eq_fullReducedDensity
    ha hb θ x]

end

end GraybillDeal
