import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# A Stein-type integration-by-parts identity for the beta weight

This module proves the exact identity

```math
\int_0^1 x^{a_1-1}(1-x)^{a_2-1}\bigl(a_1-(a_1+a_2)x\bigr)f(x)\,dx
  = -\int_0^1 x^{a_1}(1-x)^{a_2}f'(x)\,dx ,
```

valid for `1 ≤ a₁`, `1 ≤ a₂` and any `f` continuously differentiable on
`[0,1]`.  Up to normalizing constants this is the probabilistic statement

```math
\mathbb E_{\mathrm{Beta}(a_1,a_2)}\bigl[(a_1-(a_1+a_2)P)f(P)\bigr]
  = -\frac{B(a_1+1,a_2+1)}{B(a_1,a_2)}\,
    \mathbb E_{\mathrm{Beta}(a_1+1,a_2+1)}\bigl[f'(P)\bigr].
```

## Why this is the right tool for unequal sample sizes

In the risk reduction for two normal samples of sizes `ν₁+1`, `ν₂+1`, the
linear coefficient of the perturbation is

```math
B_\theta=\mathbb E_P\bigl[(r-\theta)\,\varphi(r)\,\psi\bigr],
\qquad
r-\theta=\frac{\theta(1-\theta)\,(mP-\nu_1)}{d},
\qquad m=\nu_1+\nu_2 ,
```

and the factor `mP - ν₁` is exactly what makes the integrand
sign-indefinite: it changes sign at the pivot `P = ν₁/m`.  With
`a_g = ν_g/2` one has `a₁ - (a₁+a₂)P = -(mP-ν₁)/2`, so **that troublesome
factor is precisely the derivative of the beta weight**, and the identity
above converts the linear coefficient into

```math
B_\theta=\frac{2\theta(1-\theta)}{B(a_1,a_2)}
  \int_0^1 P^{a_1}(1-P)^{a_2}\,
    \frac{d}{dP}\!\left[\frac{\varphi(r)\psi}{d}\right]dP .
```

The equal-size development instead exploits the `x ↦ -x` parity of
`Beta(a,a)`, which is unavailable once `a₁ ≠ a₂`.  This identity uses no
symmetry at all, so it applies to equal and unequal sample sizes alike.

## Scope: this is an identity, not a positivity result

Nothing here proves any dominance statement.  Moreover the pointwise
strengthening one might hope for — negativity of the integrand
`d/dP[φψ/d]` — is provably unattainable, so a dominance proof must still
extract genuine cancellation from the integral.  The obstruction: writing
`u = 1/d`, one has the exact facts that `u` is affine in `r` and that
`u = m/(ν₁ν₂)` at `P = ν₁/m` for *every* `θ`.  Examining `θ → 0` forces
`φ(1) > 0`, `θ → 1` forces `φ(0) < 0`, and `θ = ν₁/m` forces `φ` to be
strictly decreasing; no function satisfies all three.
-/

namespace GraybillDeal

open MeasureTheory intervalIntegral Set

noncomputable section

private theorem continuousOn_rpow_const_of_nonneg
    {p : ℝ} (hp : 0 ≤ p) {s : Set ℝ} :
    ContinuousOn (fun x : ℝ => x ^ p) s := fun x _ =>
  (Real.continuousAt_rpow_const x p (Or.inr hp)).continuousWithinAt

private theorem continuousOn_one_sub_rpow_const_of_nonneg
    {p : ℝ} (hp : 0 ≤ p) {s : Set ℝ} :
    ContinuousOn (fun x : ℝ => (1 - x) ^ p) s := fun x _ => by
  have h := Real.continuousAt_rpow_const (1 - x) p (Or.inr hp)
  have hi : ContinuousAt (fun y : ℝ => 1 - y) x := by fun_prop
  exact (h.comp hi).continuousWithinAt

/-- The shifted beta weight `x ^ a₁ * (1 - x) ^ a₂`, whose derivative
carries the beta score factor. -/
def betaWeightShift (a₁ a₂ x : ℝ) : ℝ := x ^ a₁ * (1 - x) ^ a₂

theorem continuousOn_betaWeightShift
    {a₁ a₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) {s : Set ℝ} :
    ContinuousOn (betaWeightShift a₁ a₂) s :=
  (continuousOn_rpow_const_of_nonneg ha₁).mul
    (continuousOn_one_sub_rpow_const_of_nonneg ha₂)

theorem betaWeightShift_zero {a₁ a₂ : ℝ} (ha₁ : a₁ ≠ 0) :
    betaWeightShift a₁ a₂ 0 = 0 := by
  simp [betaWeightShift, Real.zero_rpow ha₁]

theorem betaWeightShift_one {a₁ a₂ : ℝ} (ha₂ : a₂ ≠ 0) :
    betaWeightShift a₁ a₂ 1 = 0 := by
  simp [betaWeightShift, Real.zero_rpow ha₂]

/-- The derivative of the shifted beta weight, in product-rule form. -/
theorem hasDerivAt_betaWeightShift
    {a₁ a₂ x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (betaWeightShift a₁ a₂)
      (a₁ * x ^ (a₁ - 1) * (1 - x) ^ a₂
        - a₂ * (x ^ a₁ * (1 - x) ^ (a₂ - 1))) x := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1sub : (1 : ℝ) - x ≠ 0 := by
    have hpos : (0 : ℝ) < 1 - x := by linarith
    exact ne_of_gt hpos
  have hpow₁ : HasDerivAt (fun y : ℝ => y ^ a₁) (a₁ * x ^ (a₁ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hxne)
  have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hpow₂outer :
      HasDerivAt (fun y : ℝ => y ^ a₂) (a₂ * (1 - x) ^ (a₂ - 1)) (1 - x) :=
    Real.hasDerivAt_rpow_const (Or.inl h1sub)
  have hpow₂ :
      HasDerivAt (fun y : ℝ => (1 - y) ^ a₂)
        (a₂ * (1 - x) ^ (a₂ - 1) * (-1)) x :=
    hpow₂outer.comp x hinner
  have hmul := hpow₁.mul hpow₂
  have heq :
      a₁ * x ^ (a₁ - 1) * (1 - x) ^ a₂
          - a₂ * (x ^ a₁ * (1 - x) ^ (a₂ - 1))
        =
      a₁ * x ^ (a₁ - 1) * (1 - x) ^ a₂
          + x ^ a₁ * (a₂ * (1 - x) ^ (a₂ - 1) * (-1)) := by
    ring
  rw [heq]
  exact hmul

/--
The derivative of the shifted beta weight, rewritten as the beta density
times the beta score factor `a₁ - (a₁+a₂)x`.  Valid on the open interval,
where both `x` and `1 - x` are positive.
-/
theorem betaWeightShift_deriv_eq
    {a₁ a₂ x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    a₁ * x ^ (a₁ - 1) * (1 - x) ^ a₂
        - a₂ * (x ^ a₁ * (1 - x) ^ (a₂ - 1))
      =
    x ^ (a₁ - 1) * (1 - x) ^ (a₂ - 1) * (a₁ - (a₁ + a₂) * x) := by
  have hx1pos : (0 : ℝ) < 1 - x := by linarith
  have hsplit₁ : x ^ (a₁ - 1) * x = x ^ a₁ := by
    have h := Real.rpow_add hx0 (a₁ - 1) 1
    have hexp : a₁ - 1 + 1 = a₁ := by ring
    rw [Real.rpow_one, hexp] at h
    exact h.symm
  have hsplit₂ : (1 - x) ^ (a₂ - 1) * (1 - x) = (1 - x) ^ a₂ := by
    have h := Real.rpow_add hx1pos (a₂ - 1) 1
    have hexp : a₂ - 1 + 1 = a₂ := by ring
    rw [Real.rpow_one, hexp] at h
    exact h.symm
  rw [← hsplit₁, ← hsplit₂]
  ring

/--
**Stein-type integration by parts for the beta weight.**

For `1 ≤ a₁`, `1 ≤ a₂` and `f` continuously differentiable on `[0,1]`,

```math
\int_0^1 x^{a_1-1}(1-x)^{a_2-1}(a_1-(a_1+a_2)x)f(x)\,dx
  = -\int_0^1 x^{a_1}(1-x)^{a_2}f'(x)\,dx .
```

The boundary terms vanish because `a₁, a₂ > 0`.  No symmetry in `a₁, a₂` is
assumed, so this covers the asymmetric beta laws arising from unequal
sample sizes.
-/
theorem integral_betaScore_mul
    {a₁ a₂ : ℝ} (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hfc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf'c : ContinuousOn f' (Icc (0 : ℝ) 1)) :
    (∫ x in (0 : ℝ)..1,
        x ^ (a₁ - 1) * (1 - x) ^ (a₂ - 1) * (a₁ - (a₁ + a₂) * x) * f x)
      =
    -∫ x in (0 : ℝ)..1, x ^ a₁ * (1 - x) ^ a₂ * f' x := by
  have ha₁0 : (0 : ℝ) ≤ a₁ := le_trans zero_le_one ha₁
  have ha₂0 : (0 : ℝ) ≤ a₂ := le_trans zero_le_one ha₂
  have ha₁ne : a₁ ≠ 0 := by linarith
  have ha₂ne : a₂ ≠ 0 := by linarith
  have huIcc : uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := uIcc_of_le zero_le_one
  set W' : ℝ → ℝ := fun x =>
    a₁ * x ^ (a₁ - 1) * (1 - x) ^ a₂
      - a₂ * (x ^ a₁ * (1 - x) ^ (a₂ - 1)) with hW'
  have hW'cont : ContinuousOn W' (Icc (0 : ℝ) 1) := by
    rw [hW']
    refine ContinuousOn.sub ?_ ?_
    · exact (continuousOn_const.mul
        (continuousOn_rpow_const_of_nonneg
          (by linarith : (0 : ℝ) ≤ a₁ - 1))).mul
        (continuousOn_one_sub_rpow_const_of_nonneg ha₂0)
    · exact continuousOn_const.mul
        ((continuousOn_rpow_const_of_nonneg ha₁0).mul
          (continuousOn_one_sub_rpow_const_of_nonneg
            (by linarith : (0 : ℝ) ≤ a₂ - 1)))
  have hWcont : ContinuousOn (betaWeightShift a₁ a₂) (uIcc (0 : ℝ) 1) := by
    rw [huIcc]
    exact continuousOn_betaWeightShift ha₁0 ha₂0
  have hfcont : ContinuousOn f (uIcc (0 : ℝ) 1) := by rw [huIcc]; exact hfc
  have hWderiv : ∀ x ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (betaWeightShift a₁ a₂) (W' x) x := by
    intro x hx
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hx
    exact hasDerivAt_betaWeightShift hx.1 hx.2
  have hfderiv : ∀ x ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt f (f' x) x := by
    intro x hx
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hx
    exact hf x hx
  have hW'int : IntervalIntegrable W' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hW'cont
  have hf'int : IntervalIntegrable f' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hf'c
  have hIBP :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hWcont hfcont hWderiv hfderiv hW'int hf'int
  rw [betaWeightShift_one (a₁ := a₁) ha₂ne,
    betaWeightShift_zero (a₂ := a₂) ha₁ne] at hIBP
  simp only [zero_mul, sub_zero, zero_sub] at hIBP
  have hcongr :
      (∫ x in (0 : ℝ)..1,
          x ^ (a₁ - 1) * (1 - x) ^ (a₂ - 1) * (a₁ - (a₁ + a₂) * x) * f x)
        =
      ∫ x in (0 : ℝ)..1, W' x * f x := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [Set.uIoo_of_le zero_le_one] at hx
    rw [hW']
    exact congrArg (fun t => t * f x)
      (betaWeightShift_deriv_eq hx.1 hx.2).symm
  rw [hcongr]
  simp only [betaWeightShift] at hIBP
  linarith [hIBP]

/--
**The identity in the risk reduction's own variables.**

With residual degrees of freedom `ν₁, ν₂ ≥ 2` and `m = ν₁ + ν₂`, the beta
shapes are `a_g = ν_g / 2` and the pivot factor `m x - ν₁` — the factor
that makes the linear risk coefficient sign-indefinite, vanishing at
`x = ν₁/m` — satisfies

```math
\int_0^1 x^{\nu_1/2-1}(1-x)^{\nu_2/2-1}\,(mx-\nu_1)\,f(x)\,dx
  = 2\int_0^1 x^{\nu_1/2}(1-x)^{\nu_2/2}\,f'(x)\,dx .
```

This is the form consumed by the unequal-size linear-term analysis: it
trades the sign-indefinite pivot factor for a derivative.
-/
theorem integral_betaPivot_mul
    {ν₁ ν₂ : ℝ} (hν₁ : 2 ≤ ν₁) (hν₂ : 2 ≤ ν₂)
    {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hfc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf'c : ContinuousOn f' (Icc (0 : ℝ) 1)) :
    (∫ x in (0 : ℝ)..1,
        x ^ (ν₁ / 2 - 1) * (1 - x) ^ (ν₂ / 2 - 1)
          * ((ν₁ + ν₂) * x - ν₁) * f x)
      =
    2 * ∫ x in (0 : ℝ)..1,
      x ^ (ν₁ / 2) * (1 - x) ^ (ν₂ / 2) * f' x := by
  have hmain :=
    integral_betaScore_mul (a₁ := ν₁ / 2) (a₂ := ν₂ / 2)
      (by linarith) (by linarith) hf hfc hf'c
  have hint :
      (∫ x in (0 : ℝ)..1,
          x ^ (ν₁ / 2 - 1) * (1 - x) ^ (ν₂ / 2 - 1)
            * ((ν₁ + ν₂) * x - ν₁) * f x)
        =
      -2 * ∫ x in (0 : ℝ)..1,
        x ^ (ν₁ / 2 - 1) * (1 - x) ^ (ν₂ / 2 - 1)
          * (ν₁ / 2 - (ν₁ / 2 + ν₂ / 2) * x) * f x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hint, hmain]
  ring

end

end GraybillDeal
