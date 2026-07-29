import GraybillDeal.UniversalReducedKernel

/-!
# Translating sample sizes into universal shape parameters

For a normal sample of size `n`, the residual chi-square degrees of freedom
are `n - 1`, and the corresponding gamma shape is `(n - 1) / 2`.
This file records the elementary coercion facts used when the final
universal analytic theorem is specialized to integer sample sizes.
-/

namespace GraybillDeal

noncomputable section

/-- Gamma shape associated with a normal sample of size `n`. -/
def universalShape (n : ℕ) : ℝ :=
  ((n : ℝ) - 1) / 2

theorem universalShape_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < universalShape n := by
  unfold universalShape
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

theorem universalShape_eq_iff
    {n₁ n₂ : ℕ} :
    universalShape n₁ = universalShape n₂ ↔ n₁ = n₂ := by
  constructor
  · intro h
    unfold universalShape at h
    have hR : (n₁ : ℝ) = (n₂ : ℝ) := by linarith
    exact_mod_cast hR
  · intro h
    simpa [h]

theorem universalShape_ne
    {n₁ n₂ : ℕ} (hne : n₁ ≠ n₂) :
    universalShape n₁ ≠ universalShape n₂ := by
  exact fun h => hne (universalShape_eq_iff.mp h)

theorem universalExponent_shapes
    (n₁ n₂ : ℕ) :
    universalExponent (universalShape n₁) (universalShape n₂)
      =
    ((n₁ : ℝ) + (n₂ : ℝ) + 1) / 2 := by
  unfold universalExponent universalShape
  ring

end

end GraybillDeal
