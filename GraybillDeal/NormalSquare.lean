import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity

open scoped ENNReal NNReal Real

open MeasureTheory Real Set

namespace GraybillDeal

open ProbabilityTheory

private lemma gammaPDFReal_half_half_sq_eq_two_mul_gaussianPDFReal
    {x : ℝ} (hx : 0 < x) :
    2 * x * gammaPDFReal (1 / 2) (1 / 2) (x ^ 2) =
      2 * gaussianPDFReal 0 1 x := by
  rw [gammaPDFReal, if_pos (sq_nonneg x), gaussianPDFReal, Real.Gamma_one_half_eq]
  norm_num only [NNReal.coe_one, sub_zero, one_div, inv_pow]
  have hsqrt2 : √(2 : ℝ) ≠ 0 := by positivity
  have hsqrtpi : √π ≠ 0 := by positivity
  rw [show (x ^ 2 : ℝ) ^ (-(1 / 2 : ℝ)) = x⁻¹ by
    rw [show -(1 / 2 : ℝ) = -(2 : ℝ)⁻¹ by norm_num,
      ← Real.rpow_two x, ← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]]
  rw [show (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = (√2)⁻¹ by
    rw [Real.sqrt_eq_rpow]
    simpa [one_div] using Real.inv_rpow (x := (2 : ℝ)) (by positivity) (1 / 2 : ℝ)]
  rw [show √(2 * π * (1 : ℝ)) = √2 * √π by
    norm_num [Real.sqrt_mul (by positivity)]]
  field_simp

private lemma gaussianPDFReal_zero_one_abs (x : ℝ) :
    gaussianPDFReal 0 1 |x| = gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero]
  rw [sq_abs]

private lemma integral_gaussianPDFReal_sq_preimage
    (s : Set ℝ) (hs : MeasurableSet s) :
    (∫ x in (fun x : ℝ ↦ x ^ 2) ⁻¹' s, gaussianPDFReal 0 1 x) =
      2 * ∫ x in Ioi 0 ∩ (fun x : ℝ ↦ x ^ 2) ⁻¹' s, gaussianPDFReal 0 1 x := by
  let t := (fun x : ℝ ↦ x ^ 2) ⁻¹' s
  have ht : MeasurableSet t := hs.preimage (by fun_prop)
  let f := t.indicator (gaussianPDFReal 0 1)
  have hf_abs (x : ℝ) : f |x| = f x := by
    by_cases hx : x ^ 2 ∈ s
    · simp [f, t, hx, gaussianPDFReal_zero_one_abs]
    · simp [f, t, hx]
  calc
    (∫ x in t, gaussianPDFReal 0 1 x) = ∫ x, f x := (integral_indicator ht).symm
    _ = ∫ x, f |x| := integral_congr_ae (ae_of_all _ fun x ↦ (hf_abs x).symm)
    _ = 2 * ∫ x in Ioi 0, f x := integral_comp_abs
    _ = 2 * ∫ x in Ioi 0 ∩ t, gaussianPDFReal 0 1 x := by
      rw [setIntegral_indicator ht]

private lemma gammaPDFReal_half_half_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    gammaPDFReal (1 / 2) (1 / 2) x = 0 := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [gammaPDFReal, if_pos le_rfl]
    have hz : (0 : ℝ) ^ ((1 / 2 : ℝ) - 1) = 0 :=
      Real.zero_rpow (by norm_num)
    rw [hz]
    ring
  · simp [gammaPDFReal, hx.not_ge]

private lemma integral_gammaPDFReal_half_half
    (s : Set ℝ) (hs : MeasurableSet s) :
    (∫ y in s, gammaPDFReal (1 / 2) (1 / 2) y) =
      2 * ∫ x in Ioi 0 ∩ (fun x : ℝ ↦ x ^ 2) ⁻¹' s, gaussianPDFReal 0 1 x := by
  let t := (fun x : ℝ ↦ x ^ 2) ⁻¹' s
  have ht : MeasurableSet t := hs.preimage (by fun_prop)
  let g := s.indicator (gammaPDFReal (1 / 2) (1 / 2))
  have hg_support :
      (∫ y in Ioi 0, g y) = ∫ y, g y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hy_nonpos : y ≤ 0 := not_lt.mp hy
    by_cases hys : y ∈ s
    · rw [show g y = gammaPDFReal (1 / 2) (1 / 2) y by simp [g, hys]]
      exact gammaPDFReal_half_half_of_nonpos hy_nonpos
    · simp [g, hys]
  have hsub :=
    integral_comp_rpow_Ioi (g := g) (p := (2 : ℝ)) (by norm_num)
  norm_num [Real.rpow_one] at hsub
  have hpoint (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      2 * x * g (x ^ 2) =
        2 * t.indicator (gaussianPDFReal 0 1) x := by
    by_cases hxs : x ^ 2 ∈ s
    · have hxt : x ∈ t := hxs
      rw [show g (x ^ 2) = gammaPDFReal (1 / 2) (1 / 2) (x ^ 2) by
        simp [g, hxs], indicator_of_mem hxt]
      exact gammaPDFReal_half_half_sq_eq_two_mul_gaussianPDFReal hx
    · have hxt : x ∉ t := hxs
      simp [g, hxs, Set.indicator_of_notMem hxt]
  calc
    (∫ y in s, gammaPDFReal (1 / 2) (1 / 2) y) = ∫ y, g y :=
      (integral_indicator hs).symm
    _ = ∫ y in Ioi 0, g y := hg_support.symm
    _ = ∫ x in Ioi 0, 2 * x * g (x ^ 2) := by
      exact hsub.symm
    _ = ∫ x in Ioi 0, 2 * t.indicator (gaussianPDFReal 0 1) x :=
      setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = 2 * ∫ x in Ioi 0, t.indicator (gaussianPDFReal 0 1) x := by
      rw [integral_const_mul]
    _ = 2 * ∫ x in Ioi 0 ∩ t, gaussianPDFReal 0 1 x := by
      rw [setIntegral_indicator ht]

private lemma integrable_gammaPDFReal_half_half :
    Integrable (gammaPDFReal (1 / 2) (1 / 2)) := by
  refine ⟨(stronglyMeasurable_gammaPDFReal _ _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (gammaPDFReal_nonneg (by norm_num) (by norm_num)))]
  change (∫⁻ x, gammaPDF (1 / 2) (1 / 2) x) < ∞
  rw [lintegral_gammaPDF_eq_one (by norm_num) (by norm_num)]
  simp

private lemma gammaMeasure_half_half_apply_eq_integral
    (s : Set ℝ) (hs : MeasurableSet s) :
    gammaMeasure (1 / 2) (1 / 2) s =
      ENNReal.ofReal (∫ x in s, gammaPDFReal (1 / 2) (1 / 2) x) := by
  rw [gammaMeasure, withDensity_apply _ hs]
  change (∫⁻ x in s, ENNReal.ofReal (gammaPDFReal (1 / 2) (1 / 2) x)) =
    ENNReal.ofReal (∫ x in s, gammaPDFReal (1 / 2) (1 / 2) x)
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact integrable_gammaPDFReal_half_half.restrict
  · exact ae_of_all _ (gammaPDFReal_nonneg (by norm_num) (by norm_num))

/-- The square of a standard real Gaussian has the gamma law with shape and rate `1 / 2`. -/
theorem gaussianReal_zero_one_map_sq :
    (gaussianReal 0 1).map (fun x : ℝ ↦ x ^ 2) =
      gammaMeasure (1 / 2) (1 / 2) := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    gaussianReal_apply_eq_integral 0 (by norm_num)
      ((fun x : ℝ ↦ x ^ 2) ⁻¹' s),
    gammaMeasure_half_half_apply_eq_integral s hs]
  congr 1
  exact (integral_gaussianPDFReal_sq_preimage s hs).trans
    (integral_gammaPDFReal_half_half s hs).symm

/-- A squared standard-normal random variable has gamma shape-rate law
`Gamma(1 / 2, 1 / 2)`. -/
theorem hasLaw_sq_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ Z ω ^ 2) (gammaMeasure (1 / 2) (1 / 2)) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_zero_one_map_sq⟩ hZ

/-- Measurable squaring preserves mutual independence. -/
theorem iIndepFun_sq
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ι → Ω → ℝ}
    (h_indep : iIndepFun Z P) :
    iIndepFun (fun i ω ↦ Z i ω ^ 2) P := by
  simpa only [Function.comp_def] using
    h_indep.comp (fun _ : ι ↦ fun x : ℝ ↦ x ^ 2)
      (fun _ ↦ measurable_id.pow_const 2)

/-- Independent standard Gaussians, squared coordinatewise, have the product law of
`Gamma(1 / 2, 1 / 2)` variables. -/
theorem hasLaw_pi_sq_standardGaussian
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ι → Ω → ℝ} (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (h_indep : iIndepFun Z P) :
    HasLaw (fun ω i ↦ Z i ω ^ 2)
      (Measure.pi fun _ : ι ↦ gammaMeasure (1 / 2) (1 / 2)) P := by
  apply (iIndepFun_sq h_indep).hasLaw_pi
  exact fun i ↦ hasLaw_sq_standardGaussian (hZ i)

/-- The sum of squares of independent standard Gaussians is reduced to the pushforward of
the corresponding product gamma law. Identifying this pushforward with a one-dimensional
gamma measure is the remaining gamma-additivity step. -/
theorem hasLaw_sum_sq_standardGaussian_as_map
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ι → Ω → ℝ} (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (h_indep : iIndepFun Z P) :
    HasLaw (fun ω ↦ ∑ i, Z i ω ^ 2)
      ((Measure.pi fun _ : ι ↦ gammaMeasure (1 / 2) (1 / 2)).map
        fun x ↦ ∑ i, x i) P := by
  let μ : Measure (ι → ℝ) :=
    Measure.pi fun _ : ι ↦ gammaMeasure (1 / 2) (1 / 2)
  let F : (ι → ℝ) → ℝ := fun x ↦ ∑ i, x i
  have hF : HasLaw F (μ.map F) μ := ⟨by fun_prop, rfl⟩
  simpa only [F, μ, Function.comp_def] using
    hF.comp (hasLaw_pi_sq_standardGaussian hZ h_indep)

private lemma integral_rpow_mul_sub_rpow
    {a s t : ℝ} (ha : 0 < a) (hs : 0 < s) (ht : 0 < t) :
    (∫ x in 0..a, x ^ (s - 1) * (a - x) ^ (t - 1)) =
      a ^ (s + t - 1) * (Real.Gamma s * Real.Gamma t / Real.Gamma (s + t)) := by
  have hc := Complex.betaIntegral_scaled (s : ℂ) (t : ℂ) ha
  rw [Complex.betaIntegral_eq_Gamma_mul_div (s : ℂ) (t : ℂ)
    (by simpa) (by simpa)] at hc
  rw [← Complex.ofReal_inj, ← intervalIntegral.integral_ofReal]
  calc
    (∫ x in 0..a, ((x ^ (s - 1) * (a - x) ^ (t - 1) : ℝ) : ℂ)) =
        ∫ x in 0..a, (x : ℂ) ^ ((s : ℂ) - 1) *
          ((a : ℂ) - x) ^ ((t : ℂ) - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      rw [uIoc_of_le ha.le] at hx
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
        Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
      push_cast
      rfl
    _ = (a : ℂ) ^ ((s : ℂ) + t - 1) *
        (Complex.Gamma (s : ℂ) * Complex.Gamma (t : ℂ) /
          Complex.Gamma ((s : ℂ) + t)) := hc
    _ = ((a ^ (s + t - 1) *
        (Real.Gamma s * Real.Gamma t / Real.Gamma (s + t)) : ℝ) : ℂ) := by
      rw [show (s : ℂ) + t - 1 = ((s + t - 1 : ℝ) : ℂ) by push_cast; rfl]
      rw [← Complex.ofReal_cpow ha.le]
      simp only [Complex.Gamma_ofReal]
      rw [show (s : ℂ) + t = ((s + t : ℝ) : ℂ) by push_cast; rfl,
        Complex.Gamma_ofReal]
      push_cast
      rfl

private lemma integral_gammaPDFReal_mul_gammaPDFReal_sub_of_pos
    {a b r x : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hx : 0 < x) :
    (∫ y, gammaPDFReal a r y * gammaPDFReal b r (x - y)) =
      gammaPDFReal (a + b) r x := by
  let f : ℝ → ℝ := fun y ↦ gammaPDFReal a r y * gammaPDFReal b r (x - y)
  let K : ℝ :=
    (r ^ a / Real.Gamma a) * (r ^ b / Real.Gamma b) * Real.exp (-(r * x))
  have h_support : (∫ y, f y) = ∫ y in Icc 0 x, f y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    simp only [mem_Icc, not_and_or, not_le] at hy
    rcases hy with hy | hy
    · have hz : gammaPDFReal a r y = 0 := by
        rw [gammaPDFReal, if_neg hy.not_ge]
      simp [f, hz]
    · have hxy : x - y < 0 := sub_neg.mpr hy
      have hz : gammaPDFReal b r (x - y) = 0 := by
        rw [gammaPDFReal, if_neg hxy.not_ge]
      simp [f, hz]
  have h_inside (y : ℝ) (hy : y ∈ Icc (0 : ℝ) x) :
      f y = K * (y ^ (a - 1) * (x - y) ^ (b - 1)) := by
    have hxy : 0 ≤ x - y := sub_nonneg.mpr hy.2
    dsimp only [f]
    rw [gammaPDFReal, if_pos hy.1, gammaPDFReal, if_pos hxy]
    have hexp :
        Real.exp (-(r * y)) * Real.exp (-(r * (x - y))) =
          Real.exp (-(r * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [K]
    rw [← hexp]
    ring
  calc
    (∫ y, gammaPDFReal a r y * gammaPDFReal b r (x - y)) =
        ∫ y, f y := rfl
    _ = ∫ y in Icc 0 x, f y := h_support
    _ = ∫ y in Icc 0 x,
        K * (y ^ (a - 1) * (x - y) ^ (b - 1)) :=
      setIntegral_congr_fun measurableSet_Icc h_inside
    _ = K * ∫ y in Icc 0 x, y ^ (a - 1) * (x - y) ^ (b - 1) := by
      rw [integral_const_mul]
    _ = K * ∫ y in 0..x, y ^ (a - 1) * (x - y) ^ (b - 1) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.le]
    _ = K * (x ^ (a + b - 1) *
        (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b))) := by
      rw [integral_rpow_mul_sub_rpow hx ha hb]
    _ = gammaPDFReal (a + b) r x := by
      dsimp only [K]
      rw [gammaPDFReal, if_pos hx.le]
      rw [Real.rpow_add hr]
      field_simp [ne_of_gt (Real.Gamma_pos_of_pos ha),
        ne_of_gt (Real.Gamma_pos_of_pos hb),
        ne_of_gt (Real.Gamma_pos_of_pos (add_pos ha hb))]

/-- Gamma measures with a common rate are closed under convolution, with additive shapes. -/
theorem gammaMeasure_conv_same_rate
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    gammaMeasure a r ∗ gammaMeasure b r = gammaMeasure (a + b) r := by
  have hconv_pos (x : ℝ) (hx : 0 < x) :
      (gammaPDF a r ⋆ₗ[volume] gammaPDF b r) x =
        gammaPDF (a + b) r x := by
    have hreal :
        (∫ y, gammaPDFReal a r y * gammaPDFReal b r (-y + x)) =
          gammaPDFReal (a + b) r x := by
      simpa [sub_eq_add_neg, add_comm] using
        integral_gammaPDFReal_mul_gammaPDFReal_sub_of_pos ha hb hr hx
    have hreal_pos : 0 < gammaPDFReal (a + b) r x :=
      gammaPDFReal_pos (add_pos ha hb) hr hx
    have hint : Integrable
        (fun y ↦ gammaPDFReal a r y * gammaPDFReal b r (-y + x)) :=
      Integrable.of_integral_ne_zero (hreal.trans_ne hreal_pos.ne')
    rw [lconvolution_def]
    simp_rw [gammaPDF, ← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun y ↦ mul_nonneg
        (gammaPDFReal_nonneg ha hr y)
        (gammaPDFReal_nonneg hb hr (-y + x)))]
    rw [hreal]
  have hconv_neg (x : ℝ) (hx : x < 0) :
      (gammaPDF a r ⋆ₗ[volume] gammaPDF b r) x =
        gammaPDF (a + b) r x := by
    rw [lconvolution_def, gammaPDF_of_neg hx]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ fun y ↦ by
      change gammaPDF a r y * gammaPDF b r (-y + x) = 0
      by_cases hy : y < 0
      · rw [gammaPDF_of_neg hy, zero_mul]
      · have hy0 : 0 ≤ y := not_lt.mp hy
        have hxy : -y + x < 0 := by linarith
        rw [gammaPDF_of_neg hxy, mul_zero]
  have hconv_ae :
      (gammaPDF a r ⋆ₗ[volume] gammaPDF b r) =ᵐ[volume]
        gammaPDF (a + b) r := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    rcases lt_or_gt_of_ne hx with hx | hx
    · exact hconv_neg x hx
    · exact hconv_pos x hx
  change volume.withDensity (gammaPDF a r) ∗
      volume.withDensity (gammaPDF b r) =
    volume.withDensity (gammaPDF (a + b) r)
  rw [conv_withDensity_eq_lconvolution
      (by
        change Measurable (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x))
        exact (measurable_gammaPDFReal a r).ennreal_ofReal)
      (by
        change Measurable (fun x ↦ ENNReal.ofReal (gammaPDFReal b r x))
        exact (measurable_gammaPDFReal b r).ennreal_ofReal)]
  exact withDensity_congr_ae hconv_ae

/-- A nonempty finite sum of mutually independent gamma variables with a common rate is gamma,
with shape equal to the sum of the component shapes. -/
theorem hasLaw_finset_sum_gamma_same_rate
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → ℝ} {shape : ι → ℝ} {r : ℝ}
    (hshape : ∀ i, 0 < shape i) (hr : 0 < r)
    (hX : ∀ i, HasLaw (X i) (gammaMeasure (shape i) r) P)
    (h_indep : iIndepFun X P) (s : Finset ι) (hs : s.Nonempty) :
    HasLaw (fun ω ↦ ∑ i ∈ s, X i ω)
      (gammaMeasure (∑ i ∈ s, shape i) r) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
      by_cases hs_empty : s = ∅
      · subst s
        simpa using hX i
      · have hs_nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
        have hsum := ih hs_nonempty
        have hsum_shape : 0 < ∑ j ∈ s, shape j :=
          Finset.sum_pos (fun j _ ↦ hshape j) hs_nonempty
        have hmeas : ∀ j, AEMeasurable (X j) P := fun j ↦ (hX j).aemeasurable
        have hind :
            IndepFun (∑ j ∈ s, X j) (X i) P :=
          h_indep.indepFun_finsetSum_of_notMem₀ hmeas hi
        have hind' :
            IndepFun (fun ω ↦ ∑ j ∈ s, X j ω) (X i) P := by
          have hsum_fun :
              (∑ j ∈ s, X j) = fun ω ↦ ∑ j ∈ s, X j ω := by
            funext ω
            simp
          rw [← hsum_fun]
          exact hind
        letI : IsProbabilityMeasure (gammaMeasure (∑ j ∈ s, shape j) r) :=
          isProbabilityMeasure_gammaMeasure hsum_shape hr
        letI : IsProbabilityMeasure (gammaMeasure (shape i) r) :=
          isProbabilityMeasure_gammaMeasure (hshape i) hr
        have hadd := hind'.hasLaw_add hsum (hX i)
        rw [gammaMeasure_conv_same_rate hsum_shape (hshape i) hr] at hadd
        have hadd_fun :
            (fun ω ↦ ∑ j ∈ s, X j ω) + X i =
              fun ω ↦ (∑ j ∈ s, X j ω) + X i ω := by
          funext ω
          rfl
        rw [hadd_fun] at hadd
        simpa only [Finset.sum_insert hi, add_comm] using hadd

/-- A finite nonempty sum of mutually independent gamma variables with a common rate is gamma. -/
theorem hasLaw_sum_gamma_same_rate
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → ℝ} {shape : ι → ℝ} {r : ℝ}
    (hshape : ∀ i, 0 < shape i) (hr : 0 < r)
    (hX : ∀ i, HasLaw (X i) (gammaMeasure (shape i) r) P)
    (h_indep : iIndepFun X P) :
    HasLaw (fun ω ↦ ∑ i, X i ω)
      (gammaMeasure (∑ i, shape i) r) P := by
  simpa using hasLaw_finset_sum_gamma_same_rate hshape hr hX h_indep
    Finset.univ Finset.univ_nonempty

/-- The sum of squares of a nonempty finite family of independent standard Gaussians has the
chi-square gamma law `Gamma(card / 2, 1 / 2)`. -/
theorem hasLaw_sum_sq_standardGaussian
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ι → Ω → ℝ} (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (h_indep : iIndepFun Z P) :
    HasLaw (fun ω ↦ ∑ i, Z i ω ^ 2)
      (gammaMeasure ((Fintype.card ι : ℝ) / 2) (1 / 2)) P := by
  have h := hasLaw_sum_gamma_same_rate
    (X := fun i ω ↦ Z i ω ^ 2) (shape := fun _ : ι ↦ (1 / 2 : ℝ))
    (fun _ ↦ by norm_num) (by norm_num)
    (fun i ↦ hasLaw_sq_standardGaussian (hZ i)) (iIndepFun_sq h_indep)
  simpa [div_eq_mul_inv] using h

/-- Twelve independent standard-normal squares sum to `Gamma(6, 1 / 2)`. -/
theorem hasLaw_sum_sq_standardGaussian_fin12
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Fin 12 → Ω → ℝ} (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (h_indep : iIndepFun Z P) :
    HasLaw (fun ω ↦ ∑ i, Z i ω ^ 2) (gammaMeasure 6 (1 / 2)) P := by
  convert hasLaw_sum_sq_standardGaussian hZ h_indep using 1
  all_goals norm_num

/-- Twenty-four independent standard-normal squares sum to `Gamma(12, 1 / 2)`. -/
theorem hasLaw_sum_sq_standardGaussian_fin24
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Fin 24 → Ω → ℝ} (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (h_indep : iIndepFun Z P) :
    HasLaw (fun ω ↦ ∑ i, Z i ω ^ 2) (gammaMeasure 12 (1 / 2)) P := by
  convert hasLaw_sum_sq_standardGaussian hZ h_indep using 1
  all_goals norm_num

end GraybillDeal
