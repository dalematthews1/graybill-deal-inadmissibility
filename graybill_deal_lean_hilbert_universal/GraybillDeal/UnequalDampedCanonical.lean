import GraybillDeal.UnequalDampedCoordinates

/-!
# Direct canonical coordinates for the fixed `(13,17)` certificate

Here `θ` is the oracle weight, `p` is the `Beta(6,8)` residual ratio,
`l` is the `Gamma(14,1/2)` residual sum, and `v=D²/λ`.

The denominator is normalized so that

`A₁+A₂ = λ l * unequalDampedCanonicalDenom13_17 θ p / 28`.
-/

namespace GraybillDeal

noncomputable section

/-- The fixed unequal-size normalized residual denominator. -/
def unequalDampedCanonicalDenom13_17 (θ p : ℝ) : ℝ :=
  (7 * θ / 3) * p + (7 * (1 - θ) / 4) * (1 - p)

/-- The canonical Graybill--Deal weight on the second sample mean. -/
def unequalDampedCanonicalR13_17 (θ p : ℝ) : ℝ :=
  ((7 * θ / 3) * p) / unequalDampedCanonicalDenom13_17 θ p

/-- The canonical raw quadratic statistic. -/
def unequalDampedCanonicalQ13_17 (θ p l v : ℝ) : ℝ :=
  28 * v / (l * unequalDampedCanonicalDenom13_17 θ p)

/-- The endpoint-damped perturbation direction after the `V,L` variables enter. -/
def unequalDampedCanonicalH13_17 (θ p l v : ℝ) : ℝ :=
  unequalDampedPhi13_17 (unequalDampedCanonicalR13_17 θ p)
    * (unequalDampedC13_17
      - unequalDampedCanonicalQ13_17 θ p l v)

/-- The un-clipped canonical competitor weight. -/
def unequalDampedCanonicalWeight13_17
    (ε θ p l v : ℝ) : ℝ :=
  perturbation (unequalDampedCanonicalR13_17 θ p) ε
    (unequalDampedCanonicalH13_17 θ p l v)

/-- The canonical competitor weight projected to `[0,1]`. -/
def unequalDampedCanonicalClippedWeight13_17
    (ε θ p l v : ℝ) : ℝ :=
  clip01 (unequalDampedCanonicalWeight13_17 ε θ p l v)

/-- The squared standardized mean difference used in the unequal bridge. -/
def unequalStandardizedDifference13_17 (varianceSum d : ℝ) : ℝ :=
  d ^ 2 / varianceSum

theorem unequalDampedCanonicalDenom13_17_pos
    {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 < unequalDampedCanonicalDenom13_17 θ p := by
  have hright : 0 ≤ (7 * (1 - θ) / 4) * (1 - p) :=
    mul_nonneg
      (by nlinarith : 0 ≤ 7 * (1 - θ) / 4)
      (sub_nonneg.mpr hp.2)
  by_cases hp0 : p = 0
  · subst hp0
    norm_num [unequalDampedCanonicalDenom13_17]
    linarith
  · have hp' : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    have hleft : 0 < (7 * θ / 3) * p :=
      mul_pos (by nlinarith : 0 < 7 * θ / 3) hp'
    unfold unequalDampedCanonicalDenom13_17
    linarith

theorem unequalDampedCanonicalR13_17_mem_Icc
    {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    unequalDampedCanonicalR13_17 θ p ∈ Set.Icc (0 : ℝ) 1 := by
  have hd :=
    unequalDampedCanonicalDenom13_17_pos hθ0 hθ1 hp
  have hn : 0 ≤ (7 * θ / 3) * p :=
    mul_nonneg (by nlinarith) hp.1
  constructor
  · exact div_nonneg hn hd.le
  · rw [unequalDampedCanonicalR13_17, div_le_one hd]
    have hr : 0 ≤ (7 * (1 - θ) / 4) * (1 - p) :=
      mul_nonneg (by nlinarith) (sub_nonneg.mpr hp.2)
    unfold unequalDampedCanonicalDenom13_17
    linarith

theorem unequalDampedCanonicalClippedWeight13_17_sq_sub_le
    {ε θ p l v : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (unequalDampedCanonicalClippedWeight13_17 ε θ p l v - θ) ^ 2
      ≤
    (unequalDampedCanonicalWeight13_17 ε θ p l v - θ) ^ 2 := by
  unfold unequalDampedCanonicalClippedWeight13_17
  exact clip01_sq_sub_le_sq_sub _ _ hθ

theorem unequalStandardizedDifference13_17_scale
    {varianceSum d : ℝ} (hvarianceSum : varianceSum ≠ 0) :
    varianceSum * unequalStandardizedDifference13_17 varianceSum d = d ^ 2 := by
  unfold unequalStandardizedDifference13_17
  field_simp

end

end GraybillDeal
