import GraybillDeal.UnequalFixedDifferenceFourCoordinates

/-!
# Canonical coordinates for the fixed-difference-four family

For the unequal sample-size family

`(n₁,n₂) = (2m-1,2m+3)`, `m ≥ 7`,

the residual beta coordinate has law `Beta(m-1,m+1)`.  If `θ` is the
oracle weight and `p` is that beta coordinate, the normalized residual
denominator is

`(θ / t) p + ((1-θ) / q) (1-p)`,

where `t=(m-1)/(2m)` and `q=(m+1)/(2m)`.  The actual variance estimate
sum is this denominator times `λ L/(4m)`, so the canonical quadratic
statistic is `4m V/(L D)`.
-/

namespace GraybillDeal

noncomputable section

/-- Family-indexed normalized residual denominator. -/
def unequalFixedDifferenceFourCanonicalDenom
    (m : ℕ) (θ p : ℝ) : ℝ :=
  (θ / unequalFixedDifferenceFourT m) * p
    + ((1 - θ) / unequalFixedDifferenceFourQ m) * (1 - p)

/-- Canonical Graybill--Deal weight on the second sample mean. -/
def unequalFixedDifferenceFourCanonicalR
    (m : ℕ) (θ p : ℝ) : ℝ :=
  ((θ / unequalFixedDifferenceFourT m) * p)
    / unequalFixedDifferenceFourCanonicalDenom m θ p

/-- Canonical quadratic statistic `D²/(A₁+A₂)`. -/
def unequalFixedDifferenceFourCanonicalQ
    (m : ℕ) (θ p l v : ℝ) : ℝ :=
  4 * (m : ℝ) * v
    / (l * unequalFixedDifferenceFourCanonicalDenom m θ p)

/-- Endpoint-damped family perturbation direction. -/
def unequalFixedDifferenceFourCanonicalH
    (m : ℕ) (θ p l v : ℝ) : ℝ :=
  unequalDampedPhi
      (unequalFixedDifferenceFourT m)
      (unequalFixedDifferenceFourKappa m)
      (unequalFixedDifferenceFourCanonicalR m θ p)
    * (unequalFixedDifferenceFourC m
      - unequalFixedDifferenceFourCanonicalQ m θ p l v)

/-- The un-clipped canonical competitor weight. -/
def unequalFixedDifferenceFourCanonicalWeight
    (m : ℕ) (ε θ p l v : ℝ) : ℝ :=
  perturbation (unequalFixedDifferenceFourCanonicalR m θ p) ε
    (unequalFixedDifferenceFourCanonicalH m θ p l v)

/-- The canonical competitor weight projected to `[0,1]`. -/
def unequalFixedDifferenceFourCanonicalClippedWeight
    (m : ℕ) (ε θ p l v : ℝ) : ℝ :=
  clip01
    (unequalFixedDifferenceFourCanonicalWeight m ε θ p l v)

theorem unequalFixedDifferenceFourCanonicalDenom_pos
    {m : ℕ} (hm : 7 ≤ m)
    {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 < unequalFixedDifferenceFourCanonicalDenom m θ p := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have hright :
      0 ≤
        ((1 - θ) / unequalFixedDifferenceFourQ m) * (1 - p) :=
    mul_nonneg (div_nonneg (by linarith) hq.le)
      (sub_nonneg.mpr hp.2)
  by_cases hp0 : p = 0
  · subst hp0
    unfold unequalFixedDifferenceFourCanonicalDenom
    simp only [mul_zero, sub_zero, mul_one, zero_add]
    exact div_pos (by linarith) hq
  · have hp' : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    have hleft :
        0 < (θ / unequalFixedDifferenceFourT m) * p :=
      mul_pos (div_pos hθ0 ht) hp'
    unfold unequalFixedDifferenceFourCanonicalDenom
    linarith

theorem unequalFixedDifferenceFourCanonicalR_mem_Icc
    {m : ℕ} (hm : 7 ≤ m)
    {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    unequalFixedDifferenceFourCanonicalR m θ p
      ∈ Set.Icc (0 : ℝ) 1 := by
  have ht := unequalFixedDifferenceFourT_pos hm
  have hq := unequalFixedDifferenceFourQ_pos hm
  have hd :=
    unequalFixedDifferenceFourCanonicalDenom_pos
      hm hθ0 hθ1 hp
  have hn :
      0 ≤ (θ / unequalFixedDifferenceFourT m) * p :=
    mul_nonneg (div_nonneg hθ0.le ht.le) hp.1
  constructor
  · exact div_nonneg hn hd.le
  · rw [unequalFixedDifferenceFourCanonicalR, div_le_one hd]
    have hr :
        0 ≤
          ((1 - θ) / unequalFixedDifferenceFourQ m) * (1 - p) :=
      mul_nonneg (div_nonneg (by linarith) hq.le)
        (sub_nonneg.mpr hp.2)
    unfold unequalFixedDifferenceFourCanonicalDenom
    linarith

theorem unequalFixedDifferenceFourCanonicalClippedWeight_sq_sub_le
    {m : ℕ} {ε θ p l v : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (unequalFixedDifferenceFourCanonicalClippedWeight
        m ε θ p l v - θ) ^ 2
      ≤
    (unequalFixedDifferenceFourCanonicalWeight
        m ε θ p l v - θ) ^ 2 := by
  unfold unequalFixedDifferenceFourCanonicalClippedWeight
  exact clip01_sq_sub_le_sq_sub _ _ hθ

end

end GraybillDeal
