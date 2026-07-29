import GraybillDeal.UnequalFixedDifferenceFourRealCoordinates

/-!
# Real-parameter canonical coordinates for the difference-four family

For a real family parameter `m ≥ 7`, the residual beta coordinate has shapes
`(m-1,m+1)`.  If `θ` is the oracle weight and `p` is that beta coordinate,
the normalized residual denominator is

`(θ / t) p + ((1-θ) / q) (1-p)`,

where `t=(m-1)/(2m)` and `q=(m+1)/(2m)`.  The canonical quadratic statistic
is `4m V/(L D)`.

The definitions deliberately use the generic unequal-damped perturbation,
clipping, and direction functions, so the later canonical reduced-risk
transport can reuse the established generic algebra.
-/

namespace GraybillDeal

noncomputable section

/-- Real-family normalized residual denominator. -/
def unequalFixedDifferenceFourRealCanonicalDenom
    (m θ p : ℝ) : ℝ :=
  (θ / unequalFixedDifferenceFourRealT m) * p
    + ((1 - θ) / unequalFixedDifferenceFourRealQ m) * (1 - p)

/-- Canonical Graybill--Deal weight on the second sample mean. -/
def unequalFixedDifferenceFourRealCanonicalR
    (m θ p : ℝ) : ℝ :=
  ((θ / unequalFixedDifferenceFourRealT m) * p)
    / unequalFixedDifferenceFourRealCanonicalDenom m θ p

/-- Canonical quadratic statistic `D²/(A₁+A₂)`. -/
def unequalFixedDifferenceFourRealCanonicalQ
    (m θ p l v : ℝ) : ℝ :=
  4 * m * v
    / (l * unequalFixedDifferenceFourRealCanonicalDenom m θ p)

/-- Endpoint-damped real-family perturbation direction. -/
def unequalFixedDifferenceFourRealCanonicalH
    (m θ p l v : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourRealT m)
      (unequalFixedDifferenceFourRealKappa m)
      (unequalFixedDifferenceFourRealCanonicalR m θ p)
    * (unequalFixedDifferenceFourRealC m
      - unequalFixedDifferenceFourRealCanonicalQ m θ p l v)

/-- The un-clipped real-family canonical competitor weight. -/
def unequalFixedDifferenceFourRealCanonicalWeight
    (m ε θ p l v : ℝ) : ℝ :=
  perturbation (unequalFixedDifferenceFourRealCanonicalR m θ p) ε
    (unequalFixedDifferenceFourRealCanonicalH m θ p l v)

/-- The real-family canonical competitor weight projected to `[0,1]`. -/
def unequalFixedDifferenceFourRealCanonicalClippedWeight
    (m ε θ p l v : ℝ) : ℝ :=
  clip01
    (unequalFixedDifferenceFourRealCanonicalWeight m ε θ p l v)

/--
The real-family normalized residual denominator is strictly positive for an
interior oracle weight and a beta coordinate in `[0,1]`.
-/
theorem unequalFixedDifferenceFourRealCanonicalDenom_pos
    {m : ℝ} (hm : 7 ≤ m)
    {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 < unequalFixedDifferenceFourRealCanonicalDenom m θ p := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have hright :
      0 ≤
        ((1 - θ) / unequalFixedDifferenceFourRealQ m) * (1 - p) :=
    mul_nonneg (div_nonneg (by linarith) hq.le)
      (sub_nonneg.mpr hp.2)
  by_cases hp0 : p = 0
  · subst hp0
    unfold unequalFixedDifferenceFourRealCanonicalDenom
    simp only [mul_zero, sub_zero, mul_one, zero_add]
    exact div_pos (by linarith) hq
  · have hp' : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    have hleft :
        0 < (θ / unequalFixedDifferenceFourRealT m) * p :=
      mul_pos (div_pos hθ0 ht) hp'
    unfold unequalFixedDifferenceFourRealCanonicalDenom
    linarith

/-- The canonical Graybill--Deal weight lies in `[0,1]`. -/
theorem unequalFixedDifferenceFourRealCanonicalR_mem_Icc
    {m : ℝ} (hm : 7 ≤ m)
    {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    unequalFixedDifferenceFourRealCanonicalR m θ p
      ∈ Set.Icc (0 : ℝ) 1 := by
  have ht := unequalFixedDifferenceFourRealT_pos hm
  have hq := unequalFixedDifferenceFourRealQ_pos hm
  have hd :=
    unequalFixedDifferenceFourRealCanonicalDenom_pos
      hm hθ0 hθ1 hp
  have hn :
      0 ≤ (θ / unequalFixedDifferenceFourRealT m) * p :=
    mul_nonneg (div_nonneg hθ0.le ht.le) hp.1
  constructor
  · exact div_nonneg hn hd.le
  · rw [unequalFixedDifferenceFourRealCanonicalR, div_le_one hd]
    have hr :
        0 ≤
          ((1 - θ) / unequalFixedDifferenceFourRealQ m) * (1 - p) :=
      mul_nonneg (div_nonneg (by linarith) hq.le)
        (sub_nonneg.mpr hp.2)
    unfold unequalFixedDifferenceFourRealCanonicalDenom
    linarith

/--
Clipping the real-family competitor cannot increase squared distance from an
oracle weight in `[0,1]`.
-/
theorem unequalFixedDifferenceFourRealCanonicalClippedWeight_sq_sub_le
    {m ε θ p l v : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (unequalFixedDifferenceFourRealCanonicalClippedWeight
        m ε θ p l v - θ) ^ 2
      ≤
    (unequalFixedDifferenceFourRealCanonicalWeight
        m ε θ p l v - θ) ^ 2 := by
  unfold unequalFixedDifferenceFourRealCanonicalClippedWeight
  exact clip01_sq_sub_le_sq_sub _ _ hθ

end

end GraybillDeal
