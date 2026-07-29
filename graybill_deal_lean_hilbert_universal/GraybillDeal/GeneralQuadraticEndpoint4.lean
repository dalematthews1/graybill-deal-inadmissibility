import GraybillDeal.GeneralQuadratic
import GraybillDeal.GeneralIntegralPairing
import GraybillDeal.GeneralMomentIntegral

/-!
# The generalized fourth-order quadratic endpoint

For residual degrees of freedom `ν ≥ 9`, pairing the fourth-order quadratic
kernel and sending `|s|` to one gives

`(1-x)^(ν/2+1) (1+x)^(ν/2-3)
  + (1+x)^(ν/2+1) (1-x)^(ν/2-3)`.

Its integral is evaluated exactly by an affine change of variables to the
beta integral.  The same endpoint then bounds the fourth-order kernel
uniformly for `|s| < 1`.
-/

namespace GraybillDeal

open Set MeasureTheory ProbabilityTheory

noncomputable section

/-- One unpaired half of the fourth-order endpoint kernel. -/
def generalQuadraticEndpointHalf4 (ν x : ℝ) : ℝ :=
  (1 - x) ^ (ν / 2 + 1) * (1 + x) ^ (ν / 2 - 3)

/--
The even endpoint kernel obtained by pairing the values at `x` and `-x`.
At `ν = 12` this is exactly `endpointKernel4`.
-/
def generalQuadraticEndpointKernel4 (ν x : ℝ) : ℝ :=
  (1 - x) ^ (ν / 2 + 1) * (1 + x) ^ (ν / 2 - 3)
    + (1 + x) ^ (ν / 2 + 1) * (1 - x) ^ (ν / 2 - 3)

/-- The generalized fourth-order endpoint integral. -/
def generalQuadraticEndpointIntegral4 (ν : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, generalQuadraticEndpointKernel4 ν x

theorem generalQuadraticEndpointKernel4_eq_pair (ν x : ℝ) :
    generalQuadraticEndpointKernel4 ν x
      =
    generalQuadraticEndpointHalf4 ν x
      + generalQuadraticEndpointHalf4 ν (-x) := by
  unfold generalQuadraticEndpointKernel4
    generalQuadraticEndpointHalf4
  rw [show 1 - -x = 1 + x by ring]
  rw [show 1 + -x = 1 - x by ring]

private theorem continuous_generalQuadraticEndpointHalf4
    {ν : ℝ} (hν : 9 ≤ ν) :
    Continuous (generalQuadraticEndpointHalf4 ν) := by
  have htop : 0 ≤ ν / 2 + 1 := by linarith
  have hbottom : 0 ≤ ν / 2 - 3 := by linarith
  unfold generalQuadraticEndpointHalf4
  exact
    ((Real.continuous_rpow_const htop).comp
      (continuous_const.sub continuous_id)).mul
    ((Real.continuous_rpow_const hbottom).comp
      (continuous_const.add continuous_id))

private theorem integral_rpow_mul_one_sub_rpow_eq_beta4
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1))
      = beta a b := by
  have hcomplex :
      Complex.betaIntegral (a : ℂ) (b : ℂ)
        =
      ((∫ t in (0 : ℝ)..1,
        t ^ (a - 1) * (1 - t) ^ (b - 1) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2)]
    push_cast
    rfl
  calc
    (∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1))
        =
      (((∫ t in (0 : ℝ)..1,
        t ^ (a - 1) * (1 - t) ^ (b - 1) : ℝ) : ℂ)).re := by simp
    _ = (Complex.betaIntegral (a : ℂ) (b : ℂ)).re := by rw [hcomplex]
    _ = beta a b := (beta_eq_betaIntegralReal a b ha hb).symm

private theorem generalQuadraticEndpointHalf4_affine
    {ν t : ℝ} (_hν : 9 ≤ ν) (ht : t ∈ Icc (0 : ℝ) 1) :
    generalQuadraticEndpointHalf4 ν (2 * t - 1)
      =
    (2 : ℝ) ^ (ν - 2)
      * (t ^ (ν / 2 - 3) * (1 - t) ^ (ν / 2 + 1)) := by
  have ht0 : 0 ≤ t := ht.1
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hpow :
      (2 : ℝ) ^ (ν - 2)
        = (2 : ℝ) ^ (ν / 2 + 1) * (2 : ℝ) ^ (ν / 2 - 3) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  unfold generalQuadraticEndpointHalf4
  rw [show 1 - (2 * t - 1) = 2 * (1 - t) by ring]
  rw [show 1 + (2 * t - 1) = 2 * t by ring]
  rw [Real.mul_rpow (by norm_num) h1t,
    Real.mul_rpow (by norm_num) ht0, hpow]
  ring

/--
Exact beta evaluation of the generalized fourth-order endpoint integral.
-/
theorem integral_generalQuadraticEndpointKernel4
    {ν : ℝ} (hν : 9 ≤ ν) :
    generalQuadraticEndpointIntegral4 ν
      =
    (2 : ℝ) ^ (ν - 1) * beta (ν / 2 + 2) (ν / 2 - 2) := by
  let F : ℝ → ℝ := generalQuadraticEndpointHalf4 ν
  let g : ℝ → ℝ := fun t =>
    t ^ (ν / 2 - 3) * (1 - t) ^ (ν / 2 + 1)
  have hFcont : Continuous F := by
    dsimp only [F]
    exact continuous_generalQuadraticEndpointHalf4 hν
  have hpair :
      generalQuadraticEndpointIntegral4 ν
        =
      ∫ x in (-1 : ℝ)..1, F x := by
    unfold generalQuadraticEndpointIntegral4
    calc
      (∫ x in (0 : ℝ)..1, generalQuadraticEndpointKernel4 ν x)
          =
        ∫ x in (0 : ℝ)..1, (F x + F (-x)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp only [F]
          exact generalQuadraticEndpointKernel4_eq_pair ν x
      _ = ∫ x in (-1 : ℝ)..1, F x := by
        symm
        exact integral_neg_one_one_eq_pair F
          (hFcont.intervalIntegrable (-1) 0)
          (hFcont.intervalIntegrable 0 1)
  have hsubst :
      (2 : ℝ) * (∫ t in (0 : ℝ)..1, F (2 * t - 1))
        =
      ∫ x in (-1 : ℝ)..1, F x := by
    have h :=
      intervalIntegral.smul_integral_comp_mul_add
        (f := F) (a := (0 : ℝ)) (b := 1) (c := 2) (d := -1)
    have hone : (2 : ℝ) + -1 = 1 := by norm_num
    simpa only [smul_eq_mul, sub_eq_add_neg, mul_zero, zero_add,
      mul_one, hone] using h
  have htransform :
      (∫ t in (0 : ℝ)..1, F (2 * t - 1))
        =
      (2 : ℝ) ^ (ν - 2) * ∫ t in (0 : ℝ)..1, g t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using ht
    dsimp only [F, g]
    exact generalQuadraticEndpointHalf4_affine hν ht'
  have hbeta :
      (∫ t in (0 : ℝ)..1, g t)
        =
      beta (ν / 2 - 2) (ν / 2 + 2) := by
    dsimp only [g]
    convert
      integral_rpow_mul_one_sub_rpow_eq_beta4
        (a := ν / 2 - 2) (b := ν / 2 + 2)
        (by linarith) (by linarith) using 1
    all_goals ring_nf
  have hbeta_comm :
      beta (ν / 2 - 2) (ν / 2 + 2)
        = beta (ν / 2 + 2) (ν / 2 - 2) := by
    unfold beta
    rw [mul_comm
      (Real.Gamma (ν / 2 - 2)) (Real.Gamma (ν / 2 + 2))]
    congr 2
    ring
  have htwo :
      (2 : ℝ) * (2 : ℝ) ^ (ν - 2) = (2 : ℝ) ^ (ν - 1) := by
    calc
      (2 : ℝ) * (2 : ℝ) ^ (ν - 2)
          = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (ν - 2) := by
            rw [Real.rpow_one]
      _ = (2 : ℝ) ^ ((1 : ℝ) + (ν - 2)) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = (2 : ℝ) ^ (ν - 1) := by
            congr 1
            ring
  calc
    generalQuadraticEndpointIntegral4 ν
        = ∫ x in (-1 : ℝ)..1, F x := hpair
    _ = (2 : ℝ) * (∫ t in (0 : ℝ)..1, F (2 * t - 1)) :=
      hsubst.symm
    _ = (2 : ℝ) *
        ((2 : ℝ) ^ (ν - 2) * ∫ t in (0 : ℝ)..1, g t) := by
      rw [htransform]
    _ = (2 : ℝ) ^ (ν - 1)
        * beta (ν / 2 + 2) (ν / 2 - 2) := by
      rw [hbeta, hbeta_comm, ← mul_assoc, htwo]

/--
The generalized quadratic weight factors into the endpoint singularity
power and the fourth power used in the rational comparison.
-/
theorem generalQuadraticWeight_eq_endpointFactor4
    {ν x : ℝ} (hν : 9 ≤ ν) (hx : |x| ≤ 1) :
    generalQuadraticWeight ν x
      =
    (1 - x ^ 2) ^ (ν / 2 - 3) * (1 - x ^ 2) ^ 4 := by
  have hbase : 0 ≤ 1 - x ^ 2 := by
    rcases abs_le.mp hx with ⟨hxl, hxu⟩
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + x)
      (by linarith : 0 ≤ 1 - x)]
  have hexponent : 0 ≤ ν / 2 - 3 := by linarith
  unfold generalQuadraticWeight
  calc
    (1 - x ^ 2) ^ (ν / 2 + 1)
        =
      (1 - x ^ 2) ^ ((ν / 2 - 3) + (4 : ℝ)) := by
        congr 1
        ring
    _ =
      (1 - x ^ 2) ^ (ν / 2 - 3)
        * (1 - x ^ 2) ^ (4 : ℝ) :=
      Real.rpow_add_of_nonneg hbase hexponent (by norm_num)
    _ =
      (1 - x ^ 2) ^ (ν / 2 - 3) * (1 - x ^ 2) ^ 4 := by
      congr 1
      exact Real.rpow_natCast (1 - x ^ 2) 4

/-- Factored algebraic form of the paired fourth-order endpoint. -/
theorem generalQuadraticEndpointKernel4_algebra
    {ν x : ℝ} (hν : 9 ≤ ν) (hx : x ∈ Icc (0 : ℝ) 1) :
    generalQuadraticEndpointKernel4 ν x
      =
    2 * (1 - x ^ 2) ^ (ν / 2 - 3)
      * (1 + 6 * x ^ 2 + x ^ 4) := by
  have hminus : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hplus : 0 ≤ 1 + x := by linarith [hx.1]
  have hexponent : 0 ≤ ν / 2 - 3 := by linarith
  have hminus_add :
      (1 - x) ^ (ν / 2 + 1)
        =
      (1 - x) ^ (ν / 2 - 3) * (1 - x) ^ 4 := by
    calc
      (1 - x) ^ (ν / 2 + 1)
          = (1 - x) ^ ((ν / 2 - 3) + (4 : ℝ)) := by
              congr 1
              ring
      _ =
        (1 - x) ^ (ν / 2 - 3) * (1 - x) ^ (4 : ℝ) :=
          Real.rpow_add_of_nonneg hminus hexponent (by norm_num)
      _ = (1 - x) ^ (ν / 2 - 3) * (1 - x) ^ 4 := by
        congr 1
        exact Real.rpow_natCast (1 - x) 4
  have hplus_add :
      (1 + x) ^ (ν / 2 + 1)
        =
      (1 + x) ^ (ν / 2 - 3) * (1 + x) ^ 4 := by
    calc
      (1 + x) ^ (ν / 2 + 1)
          = (1 + x) ^ ((ν / 2 - 3) + (4 : ℝ)) := by
              congr 1
              ring
      _ =
        (1 + x) ^ (ν / 2 - 3) * (1 + x) ^ (4 : ℝ) :=
          Real.rpow_add_of_nonneg hplus hexponent (by norm_num)
      _ = (1 + x) ^ (ν / 2 - 3) * (1 + x) ^ 4 := by
        congr 1
        exact Real.rpow_natCast (1 + x) 4
  unfold generalQuadraticEndpointKernel4
  rw [hminus_add, hplus_add]
  rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
  rw [Real.mul_rpow hminus hplus]
  ring

/-- Exact pairing identity for the generalized fourth-order kernel. -/
theorem generalQuadraticKernel4_add_neg
    {ν s x : ℝ} (hs : |s| < 1) (hx : |x| ≤ 1) :
    generalQuadraticKernel4 ν s x
        + generalQuadraticKernel4 ν s (-x)
      =
    2 * generalQuadraticWeight ν x
      * (1 + 6 * s ^ 2 * x ^ 2 + s ^ 4 * x ^ 4)
      / (1 - s ^ 2 * x ^ 2) ^ 4 := by
  have hplus : 1 + s * x ≠ 0 :=
    ne_of_gt (one_add_sx_pos hs hx)
  have hxneg : |-x| ≤ 1 := by simpa only [abs_neg] using hx
  have hminus : 1 - s * x ≠ 0 := by
    have h := ne_of_gt (one_add_sx_pos hs hxneg)
    simpa only [mul_neg, sub_eq_add_neg] using h
  have hplus4 : (1 + s * x) ^ 4 ≠ 0 := pow_ne_zero 4 hplus
  have hminus4 : (1 - s * x) ^ 4 ≠ 0 := pow_ne_zero 4 hminus
  have hden :
      (1 + s * x) ^ 4 * (1 - s * x) ^ 4
        = (1 - s ^ 2 * x ^ 2) ^ 4 := by ring
  unfold generalQuadraticKernel4
  rw [show generalQuadraticWeight ν (-x)
      = generalQuadraticWeight ν x by
        unfold generalQuadraticWeight
        rw [show 1 - (-x) ^ 2 = 1 - x ^ 2 by ring]]
  rw [show 1 + s * -x = 1 - s * x by ring]
  rw [div_add_div _ _ hplus4 hminus4, hden]
  congr 1
  ring

/--
After pairing, the generalized fourth-order kernel is bounded pointwise by
its `|s| = 1` endpoint.
-/
theorem generalQuadraticKernel4_pair_le_endpoint
    {ν s x : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    generalQuadraticKernel4 ν s x
        + generalQuadraticKernel4 ν s (-x)
      ≤ generalQuadraticEndpointKernel4 ν x := by
  have hxabs : |x| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [generalQuadraticKernel4_add_neg hs hxabs,
    generalQuadraticEndpointKernel4_algebra hν hx]
  by_cases hx1 : x = 1
  · subst x
    have htop_ne : ν / 2 + 1 ≠ 0 := by linarith
    have hbottom_ne : ν / 2 - 3 ≠ 0 := by linarith
    simp [generalQuadraticWeight, Real.zero_rpow htop_ne,
      Real.zero_rpow hbottom_ne]
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
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
    have hy1 : y < 1 := by
      dsimp [y]
      nlinarith [hx.1, hxlt]
    have hA0 : 0 ≤ 1 - y := by linarith
    have hApos : 0 < 1 - y := by linarith
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
    have hzsqysq : z ^ 2 * y ^ 2 ≤ y ^ 2 := by
      simpa using mul_le_mul_of_nonneg_right hzsq (sq_nonneg y)
    have hNz0 : 0 ≤ 1 + 6 * z * y + z ^ 2 * y ^ 2 := by
      positivity
    have hNz :
        1 + 6 * z * y + z ^ 2 * y ^ 2
          ≤ 1 + 6 * y + y ^ 2 := by
      nlinarith
    have hpow : (1 - y) ^ 4 ≤ (1 - z * y) ^ 4 :=
      pow_le_pow_left₀ hA0 hAD 4
    have hprod :
        (1 - y) ^ 4 * (1 + 6 * z * y + z ^ 2 * y ^ 2)
          ≤
        (1 - z * y) ^ 4 * (1 + 6 * y + y ^ 2) := by
      calc
        (1 - y) ^ 4 * (1 + 6 * z * y + z ^ 2 * y ^ 2)
            ≤ (1 - z * y) ^ 4
                * (1 + 6 * z * y + z ^ 2 * y ^ 2) :=
          mul_le_mul_of_nonneg_right hpow hNz0
        _ ≤ (1 - z * y) ^ 4 * (1 + 6 * y + y ^ 2) :=
          mul_le_mul_of_nonneg_left hNz
            (pow_nonneg (le_of_lt hD) 4)
    apply (div_le_iff₀ (pow_pos hD 4)).2
    rw [generalQuadraticWeight_eq_endpointFactor4 hν hxabs]
    dsimp [z, y] at hprod ⊢
    calc
      2
          * ((1 - x ^ 2) ^ (ν / 2 - 3) * (1 - x ^ 2) ^ 4)
          * (1 + 6 * s ^ 2 * x ^ 2 + s ^ 4 * x ^ 4)
          =
        (2 * (1 - x ^ 2) ^ (ν / 2 - 3))
          * ((1 - x ^ 2) ^ 4
            * (1 + 6 * s ^ 2 * x ^ 2
              + (s ^ 2) ^ 2 * (x ^ 2) ^ 2)) := by ring
      _ ≤
        (2 * (1 - x ^ 2) ^ (ν / 2 - 3))
          * ((1 - s ^ 2 * x ^ 2) ^ 4
            * (1 + 6 * x ^ 2 + (x ^ 2) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hprod (by positivity)
      _ =
        (2 * (1 - x ^ 2) ^ (ν / 2 - 3)
            * (1 + 6 * x ^ 2 + x ^ 4))
          * (1 - s ^ 2 * x ^ 2) ^ 4 := by ring

theorem generalQuadraticKernel4_continuousOn
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    ContinuousOn (generalQuadraticKernel4 ν s) (Icc (-1) 1) := by
  have hden : ∀ x ∈ Icc (-1 : ℝ) 1, (1 + s * x) ^ 4 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply ne_of_gt
    apply one_add_sx_pos hs
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hweight :
      Continuous (generalQuadraticWeight ν) := by
    unfold generalQuadraticWeight
    exact
      (Real.continuous_rpow_const (by linarith : 0 ≤ ν / 2 + 1)).comp
        (continuous_const.sub (continuous_id.pow 2))
  unfold generalQuadraticKernel4
  exact hweight.continuousOn.div
    ((continuous_const.add
      (continuous_const.mul continuous_id)).pow 4).continuousOn hden

private theorem generalQuadraticKernel4_intervalIntegrable_neg
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    IntervalIntegrable (generalQuadraticKernel4 ν s) volume (-1) 0 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (generalQuadraticKernel4_continuousOn hν hs).mono (by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩)

private theorem generalQuadraticKernel4_intervalIntegrable_pos
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    IntervalIntegrable (generalQuadraticKernel4 ν s) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact (generalQuadraticKernel4_continuousOn hν hs).mono (by
    intro x hx
    exact ⟨(by linarith [hx.1]), hx.2⟩)

theorem continuous_generalQuadraticEndpointKernel4
    {ν : ℝ} (hν : 9 ≤ ν) :
    Continuous (generalQuadraticEndpointKernel4 ν) := by
  have hhalf := continuous_generalQuadraticEndpointHalf4 hν
  rw [show
      generalQuadraticEndpointKernel4 ν
        =
      fun x =>
        generalQuadraticEndpointHalf4 ν x
          + generalQuadraticEndpointHalf4 ν (-x) by
    funext x
    exact generalQuadraticEndpointKernel4_eq_pair ν x]
  exact hhalf.add (hhalf.comp continuous_id.neg)

/--
The endpoint beta value is a uniform bound for the generalized fourth-order
quadratic-kernel integral.
-/
theorem integral_generalQuadraticKernel4_le
    {ν s : ℝ} (hν : 9 ≤ ν) (hs : |s| < 1) :
    (∫ x in (-1 : ℝ)..1, generalQuadraticKernel4 ν s x)
      ≤ (2 : ℝ) ^ (ν - 1)
        * beta (ν / 2 + 2) (ν / 2 - 2) := by
  have hbound :
      (∫ x in (-1 : ℝ)..1, generalQuadraticKernel4 ν s x)
        ≤ generalQuadraticEndpointIntegral4 ν := by
    rw [integral_neg_one_one_eq_pair
      (generalQuadraticKernel4 ν s)
      (generalQuadraticKernel4_intervalIntegrable_neg hν hs)
      (generalQuadraticKernel4_intervalIntegrable_pos hν hs)]
    unfold generalQuadraticEndpointIntegral4
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact
        (generalQuadraticKernel4_intervalIntegrable_pos hν hs).add
          (by
            have hcomp10 :
                IntervalIntegrable
                  (fun x : ℝ => generalQuadraticKernel4 ν s (-x))
                  volume 1 0 := by
              simpa using
                (IntervalIntegrable.iff_comp_neg
                  (a := (-1 : ℝ)) (b := 0)
                  (f := generalQuadraticKernel4 ν s) (by simp)).mp
                    (generalQuadraticKernel4_intervalIntegrable_neg hν hs)
            exact hcomp10.symm)
    · exact
        (continuous_generalQuadraticEndpointKernel4 hν).intervalIntegrable
          0 1
    · intro x hx
      exact generalQuadraticKernel4_pair_le_endpoint hν hs hx
  rw [← integral_generalQuadraticEndpointKernel4 hν]
  exact hbound

end

end GraybillDeal
