import GraybillDeal.Canonical
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.HasLaw

/-!
# The centered `Beta(6,6)` probability-law bridge

This file proves the affine pushforward formula that was left as the
`hbeta_linear` and `hbeta_quadratic` hypotheses in `Canonical.lean`.
-/

namespace GraybillDeal

open MeasureTheory Set ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem beta_six_six :
    ProbabilityTheory.beta 6 6 = (1 / 2772 : ℝ) := by
  unfold ProbabilityTheory.beta
  norm_num [Real.Gamma_ofNat_eq_factorial]

theorem betaPDF_six_six_toReal (p : ℝ) :
    (betaPDF 6 6 p).toReal =
      if 0 < p ∧ p < 1 then
        2772 * p ^ 5 * (1 - p) ^ 5
      else 0 := by
  by_cases hp : 0 < p ∧ p < 1
  · rw [betaPDF, betaPDFReal, if_pos hp, ENNReal.toReal_ofReal, if_pos hp]
    · rw [beta_six_six]
      have hfive : (6 : ℝ) - 1 = 5 := by norm_num
      rw [hfive]
      change
        (1 / (1 / 2772 : ℝ)) * p ^ (5 : ℝ) * (1 - p) ^ (5 : ℝ)
          = 2772 * p ^ 5 * (1 - p) ^ 5
      norm_num
    · exact le_of_lt <| mul_pos
        (mul_pos (one_div_pos.mpr (beta_pos (by norm_num) (by norm_num)))
          (Real.rpow_pos_of_pos hp.1 _))
        (Real.rpow_pos_of_pos (sub_pos.mpr hp.2) _)
  · simp [betaPDF, betaPDFReal, hp]

/--
Integrating against `Beta(6,6)` is ordinary integration against its
polynomial density on `(0,1)`.
-/
theorem integral_betaMeasure_six_six_eq_interval
    (f : ℝ → ℝ) :
    (∫ p, f p ∂betaMeasure 6 6)
      =
    ∫ p in (0 : ℝ)..1, 2772 * p ^ 5 * (1 - p) ^ 5 * f p := by
  rw [betaMeasure]
  unfold betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_betaPDFReal 6 6).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  calc
    (∫ p, (betaPDF 6 6 p).toReal * f p)
        =
      ∫ p, (Ioo (0 : ℝ) 1).indicator
        (fun q => 2772 * q ^ 5 * (1 - q) ^ 5 * f q) p := by
          apply integral_congr_ae
          filter_upwards [] with p
          rw [betaPDF_six_six_toReal]
          by_cases hp : p ∈ Ioo (0 : ℝ) 1
          · simp only [mem_Ioo] at hp
            simp [hp]
          · have hp' : ¬ (0 < p ∧ p < 1) := by
              simpa only [mem_Ioo] using hp
            simp [hp, hp']
    _ =
      ∫ p in Ioo (0 : ℝ) 1,
        2772 * p ^ 5 * (1 - p) ^ 5 * f p :=
      integral_indicator measurableSet_Ioo
    _ =
      ∫ p in Ioc (0 : ℝ) 1,
        2772 * p ^ 5 * (1 - p) ^ 5 * f p := by
          apply setIntegral_congr_set
          exact Ioo_ae_eq_Ioc
    _ =
      ∫ p in (0 : ℝ)..1,
        2772 * p ^ 5 * (1 - p) ^ 5 * f p := by
          rw [intervalIntegral.integral_of_le (by norm_num)]

/--
The centered-coordinate form of expectation under `Beta(6,6)`.

The factor `canonicalKa13 = 693/512` includes both the beta density
normalization and the Jacobian of `x = 2p-1`.
-/
theorem integral_betaMeasure_six_six_eq_centered
    (f : ℝ → ℝ) :
    (∫ p, f p ∂betaMeasure 6 6)
      =
    canonicalKa13 * ∫ x in (-1 : ℝ)..1,
      f ((1 + x) / 2) * (1 - x ^ 2) ^ 5 := by
  rw [integral_betaMeasure_six_six_eq_interval]
  have hsubst :
      (∫ x in (-1 : ℝ)..1,
        2772 * (x / 2 + 1 / 2) ^ 5
          * (1 - (x / 2 + 1 / 2)) ^ 5
          * f (x / 2 + 1 / 2))
        =
      2 * ∫ p in (0 : ℝ)..1,
        2772 * p ^ 5 * (1 - p) ^ 5 * f p := by
    have h :=
      intervalIntegral.integral_comp_div_add
        (f := fun p : ℝ => 2772 * p ^ 5 * (1 - p) ^ 5 * f p)
        (a := (-1 : ℝ)) (b := 1) (c := 2) (d := (1 / 2 : ℝ))
        (by norm_num : (2 : ℝ) ≠ 0)
    have hzero : (-1 : ℝ) / 2 + 1 / 2 = 0 := by norm_num
    have hone : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
    rw [hzero, hone] at h
    simpa only [smul_eq_mul] using h
  calc
    (∫ p in (0 : ℝ)..1,
      2772 * p ^ 5 * (1 - p) ^ 5 * f p)
        =
      (1 / 2 : ℝ) *
        (2 * ∫ p in (0 : ℝ)..1,
          2772 * p ^ 5 * (1 - p) ^ 5 * f p) := by ring
    _ =
      (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1,
        2772 * (x / 2 + 1 / 2) ^ 5
          * (1 - (x / 2 + 1 / 2)) ^ 5
          * f (x / 2 + 1 / 2) := by rw [← hsubst]
    _ =
      canonicalKa13 * ∫ x in (-1 : ℝ)..1,
        f ((1 + x) / 2) * (1 - x ^ 2) ^ 5 := by
          rw [← intervalIntegral.integral_const_mul,
            ← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x _
          unfold canonicalKa13
          ring_nf

/--
Expectation of an arbitrary measurable test function of a `Beta(6,6)`
random variable, expressed in centered coordinates.
-/
theorem integral_comp_eq_centered_of_hasLaw_beta_six_six
    (P : Ω → ℝ) (mu : Measure Ω)
    (hP : HasLaw P (betaMeasure 6 6) mu)
    (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (betaMeasure 6 6)) :
    (∫ ω, f (P ω) ∂mu)
      =
    canonicalKa13 * ∫ x in (-1 : ℝ)..1,
      f ((1 + x) / 2) * (1 - x ^ 2) ^ 5 := by
  calc
    (∫ ω, f (P ω) ∂mu)
        = ∫ p, f p ∂betaMeasure 6 6 := by
            simpa only [Function.comp_apply] using hP.integral_comp hf
    _ =
      canonicalKa13 * ∫ x in (-1 : ℝ)..1,
        f ((1 + x) / 2) * (1 - x ^ 2) ^ 5 :=
      integral_betaMeasure_six_six_eq_centered f

/--
The beta formula required for the linear canonical `P`-integrand follows
directly from the law of `P`.
-/
theorem canonicalLinear_beta_formula_of_hasLaw
    (s : ℝ) (P : Ω → ℝ) (mu : Measure Ω)
    (hP : HasLaw P (betaMeasure 6 6) mu) :
    (∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂mu)
      =
    canonicalKa13 * ∫ x in (-1 : ℝ)..1,
      canonicalLinearPIntegrand13 s ((1 + x) / 2)
        * (1 - x ^ 2) ^ 5 := by
  apply integral_comp_eq_centered_of_hasLaw_beta_six_six P mu hP
  apply Measurable.aestronglyMeasurable
  unfold canonicalLinearPIntegrand13 canonicalR canonicalDenom
    canonicalTheta weightPolynomial
  fun_prop

/--
The beta formula required for the quadratic canonical `P`-integrand follows
directly from the law of `P`.
-/
theorem canonicalQuadratic_beta_formula_of_hasLaw
    (s : ℝ) (P : Ω → ℝ) (mu : Measure Ω)
    (hP : HasLaw P (betaMeasure 6 6) mu) :
    (∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂mu)
      =
    canonicalKa13 * ∫ x in (-1 : ℝ)..1,
      canonicalQuadraticPIntegrand13 s ((1 + x) / 2)
        * (1 - x ^ 2) ^ 5 := by
  apply integral_comp_eq_centered_of_hasLaw_beta_six_six P mu hP
  apply Measurable.aestronglyMeasurable
  unfold canonicalQuadraticPIntegrand13 canonicalR canonicalDenom
    canonicalTheta weightPolynomial
  fun_prop

/--
The linear canonical `P`-expectation has the reduced coefficient `Bg13`
whenever `P` has the required beta law.
-/
theorem canonicalLinearPExpectation_eq_Bg13_of_hasLaw
    {s : ℝ} (P : Ω → ℝ) (mu : Measure Ω)
    (hs : |s| < 1)
    (hP : HasLaw P (betaMeasure 6 6) mu) :
    (∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂mu)
      = Bg13 canonicalKa13 s :=
  canonicalLinearPExpectation_eq_Bg13 canonicalKa13 s P mu hs
    (canonicalLinear_beta_formula_of_hasLaw s P mu hP)

/--
The quadratic canonical `P`-expectation has the reduced coefficient `Cg13`
whenever `P` has the required beta law.
-/
theorem canonicalQuadraticPExpectation_eq_Cg13_of_hasLaw
    {s : ℝ} (P : Ω → ℝ) (mu : Measure Ω)
    (hs : |s| < 1)
    (hP : HasLaw P (betaMeasure 6 6) mu) :
    (∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂mu)
      = Cg13 canonicalKa13 s :=
  canonicalQuadraticPExpectation_eq_Cg13 canonicalKa13 s P mu hs
    (canonicalQuadratic_beta_formula_of_hasLaw s P mu hP)

end

end GraybillDeal
