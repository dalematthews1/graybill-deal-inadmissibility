import GraybillDeal.Risk
import GraybillDeal.Reduced

/-!
# Canonical probability-law bridge for `n = 13`

This file connects the analytic certificate in `Reduced.lean` to a genuine
squared-risk comparison.  It deliberately separates the deterministic and
measure-theoretic part of the bridge from the remaining distribution theory.

The random variables `P`, `L`, and `V` stand for

* `P = U₁ / (U₁ + U₂)`,
* `L = U₁ + U₂`,
* `V = 13 D² / λ`.

The proposition `CanonicalMomentBridge13` records precisely the two canonical
expectations that the beta--gamma calculation must identify with
`Btheta13` and `Ctheta13`.  No distributional statement is postulated as an
axiom: the identities are ordinary hypotheses of the bridge theorem.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The normalizing constant of the centered `Beta(6,6)` density. -/
def canonicalKa13 : ℝ :=
  693 / 512

theorem canonicalKa13_pos : 0 < canonicalKa13 := by
  unfold canonicalKa13
  norm_num

/-- Exact normalization integral for the centered `Beta(6,6)` kernel. -/
theorem centeredBetaKernel13_integral :
    (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ 5) = 512 / 693 := by
  let F : ℝ → ℝ := fun x =>
    x - 5 * x ^ 3 / 3 + 2 * x ^ 5 - 10 * x ^ 7 / 7
      + 5 * x ^ 9 / 9 - x ^ 11 / 11
  calc
    (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ 5)
        =
      ∫ x in (-1 : ℝ)..1,
        (1 - 5 * x ^ 2 + 10 * x ^ 4 - 10 * x ^ 6
          + 5 * x ^ 8 - x ^ 10) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
    _ = 512 / 693 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := F)
        (by
          intro x hx
          dsimp [F]
          have h1 := hasDerivAt_id x
          have h3 := ((hasDerivAt_pow 3 x).const_mul 5).div_const 3
          have h5 := (hasDerivAt_pow 5 x).const_mul 2
          have h7 := ((hasDerivAt_pow 7 x).const_mul 10).div_const 7
          have h9 := ((hasDerivAt_pow 9 x).const_mul 5).div_const 9
          have h11 := (hasDerivAt_pow 11 x).div_const 11
          have hderiv :=
            ((((h1.sub h3).add h5).sub h7).add h9).sub h11
          convert hderiv using 1
          · funext y
            simp only [Pi.add_apply, Pi.sub_apply, id_eq]
          · norm_num
            ring)
        ((by fun_prop : Continuous fun x : ℝ =>
          1 - 5 * x ^ 2 + 10 * x ^ 4 - 10 * x ^ 6
            + 5 * x ^ 8 - x ^ 10).intervalIntegrable (-1) 1)]
      norm_num [F]

theorem canonicalKa13_normalizes :
    canonicalKa13 * (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ 5) = 1 := by
  rw [centeredBetaKernel13_integral]
  unfold canonicalKa13
  norm_num

/-- The variance-ratio parameter `θ = (1+s)/2`. -/
def canonicalTheta (s : ℝ) : ℝ :=
  (1 + s) / 2

/-- The denominator `d = θP + (1-θ)(1-P) = (1+s(2P-1))/2`. -/
def canonicalDenom (s p : ℝ) : ℝ :=
  canonicalTheta s * p + (1 - canonicalTheta s) * (1 - p)

/-- The Graybill--Deal weight expressed in the canonical beta coordinate. -/
def canonicalR (s p : ℝ) : ℝ :=
  canonicalTheta s * p / canonicalDenom s p

/-- The polynomial `p(r) = r(1-r)(1-2r)` used in the perturbation. -/
def weightPolynomial (r : ℝ) : ℝ :=
  r * (1 - r) * (1 - 2 * r)

/-- The statistic `q = 12V/(Ld)` at `n=13`, `ν=12`. -/
def canonicalQ13 (s p l v : ℝ) : ℝ :=
  12 * v / (l * canonicalDenom s p)

/-- The perturbation direction `h = p(r)(4-q)`. -/
def canonicalH13 (s p l v : ℝ) : ℝ :=
  weightPolynomial (canonicalR s p) * (4 - canonicalQ13 s p l v)

/-- The un-clipped perturbed canonical weight. -/
def canonicalWeight13 (ε s p l v : ℝ) : ℝ :=
  perturbation (canonicalR s p) ε (canonicalH13 s p l v)

/--
The linear `P`-integrand left after taking the `V` and `L` moments at
`ν=12`.  It is the integrand in equation (5), before the beta density and
the change of variables `x=2P-1` are applied.
-/
def canonicalLinearPIntegrand13 (s p : ℝ) : ℝ :=
  (canonicalR s p - canonicalTheta s) * weightPolynomial (canonicalR s p)
    * (1 - 9 / (22 * canonicalDenom s p))

/--
The quadratic `P`-integrand left after taking the `V` and `L` moments at
`ν=12`.  It is the integrand in equation (6), before the beta density and
the centered-coordinate change.
-/
def canonicalQuadraticPIntegrand13 (s p : ℝ) : ℝ :=
  weightPolynomial (canonicalR s p) ^ 2
    * (1 - 9 / (11 * canonicalDenom s p)
      + 27 / (88 * canonicalDenom s p ^ 2))

/-- The standardized squared mean difference `V = 13D²/λ`. -/
def standardizedDifference13 (varianceSum d : ℝ) : ℝ :=
  13 * d ^ 2 / varianceSum

theorem canonicalTheta_mem_Icc {s : ℝ} (hs : |s| < 1) :
    canonicalTheta s ∈ Icc (0 : ℝ) 1 := by
  rcases abs_lt.mp hs with ⟨hleft, hright⟩
  constructor <;> unfold canonicalTheta <;> linarith

theorem standardizedDifference13_nonneg
    (varianceSum d : ℝ) (hvarianceSum : 0 < varianceSum) :
    0 ≤ standardizedDifference13 varianceSum d := by
  unfold standardizedDifference13
  positivity

theorem scale_standardizedDifference13
    (varianceSum d : ℝ) (hvarianceSum : varianceSum ≠ 0) :
    varianceSum / 13 * standardizedDifference13 varianceSum d = d ^ 2 := by
  unfold standardizedDifference13
  field_simp

/-- The canonical denominator written directly in terms of `θ` and `P`. -/
def canonicalDenomTheta (θ pcoord : ℝ) : ℝ :=
  θ * pcoord + (1 - θ) * (1 - pcoord)

/-- The canonical Graybill--Deal weight written directly in terms of `θ`. -/
def canonicalRTheta (θ pcoord : ℝ) : ℝ :=
  θ * pcoord / canonicalDenomTheta θ pcoord

/-- The general canonical `q=νV/(Ld)` statistic. -/
def canonicalQ (ν θ pcoord l v : ℝ) : ℝ :=
  ν * v / (l * canonicalDenomTheta θ pcoord)

/-- The rescaled direction `g=p(r)(1-q/4)`, so that `h=4g`. -/
def canonicalG (ν θ pcoord l v : ℝ) : ℝ :=
  weightPolynomial (canonicalRTheta θ pcoord)
    * (1 - canonicalQ ν θ pcoord l v / 4)

/--
Pointwise expansion of the linear canonical integrand into the two mixed
moments needed from the independent `V` and `L` coordinates.
-/
theorem canonicalLinearIntegrand_expand
    (ν θ pcoord l v : ℝ) :
    v * (canonicalRTheta θ pcoord - θ) * canonicalG ν θ pcoord l v
      =
    ((canonicalRTheta θ pcoord - θ)
        * weightPolynomial (canonicalRTheta θ pcoord)) * v
      - (ν / 4)
        * (((canonicalRTheta θ pcoord - θ)
            * weightPolynomial (canonicalRTheta θ pcoord))
          / canonicalDenomTheta θ pcoord)
        * (v ^ 2 / l) := by
  unfold canonicalG canonicalQ
  simp only [div_eq_mul_inv, mul_inv]
  ring

/--
Pointwise expansion of the quadratic canonical integrand into the three mixed
moments needed from the independent `V` and `L` coordinates.
-/
theorem canonicalQuadraticIntegrand_expand
    (ν θ pcoord l v : ℝ) :
    v * canonicalG ν θ pcoord l v ^ 2
      =
    weightPolynomial (canonicalRTheta θ pcoord) ^ 2 * v
      - (ν / 2)
        * (weightPolynomial (canonicalRTheta θ pcoord) ^ 2
          / canonicalDenomTheta θ pcoord)
        * (v ^ 2 / l)
      + (ν ^ 2 / 16)
        * (weightPolynomial (canonicalRTheta θ pcoord) ^ 2
          / canonicalDenomTheta θ pcoord ^ 2)
        * (v ^ 3 / l ^ 2) := by
  unfold canonicalG canonicalQ
  simp only [div_eq_mul_inv, mul_inv]
  ring

@[simp]
theorem canonicalDenomTheta_canonicalTheta (s pcoord : ℝ) :
    canonicalDenomTheta (canonicalTheta s) pcoord
      = canonicalDenom s pcoord := rfl

@[simp]
theorem canonicalRTheta_canonicalTheta (s pcoord : ℝ) :
    canonicalRTheta (canonicalTheta s) pcoord = canonicalR s pcoord := rfl

@[simp]
theorem canonicalQ_twelve (s pcoord l v : ℝ) :
    canonicalQ 12 (canonicalTheta s) pcoord l v
      = canonicalQ13 s pcoord l v := rfl

theorem canonicalH13_eq_four_mul_G (s pcoord l v : ℝ) :
    canonicalH13 s pcoord l v
      = 4 * canonicalG 12 (canonicalTheta s) pcoord l v := by
  unfold canonicalH13 canonicalG
  rw [canonicalRTheta_canonicalTheta, canonicalQ_twelve]
  unfold canonicalQ13
  ring

/--
Specialization of the mixed-moment expansion to the actual direction
`h=p(r)(4-q)` at `ν=12`.
-/
theorem canonicalLinearH13_expand (s pcoord l v : ℝ) :
    v * (canonicalR s pcoord - canonicalTheta s)
        * canonicalH13 s pcoord l v
      =
    4 * ((canonicalR s pcoord - canonicalTheta s)
        * weightPolynomial (canonicalR s pcoord)) * v
      - 12
        * (((canonicalR s pcoord - canonicalTheta s)
            * weightPolynomial (canonicalR s pcoord))
          / canonicalDenom s pcoord)
        * (v ^ 2 / l) := by
  unfold canonicalH13 canonicalQ13
  simp only [div_eq_mul_inv, mul_inv]
  ring

/--
The corresponding three-term expansion of `Vh²`.  These are exactly the
moments `E[V]`, `E[V²/L]`, and `E[V³/L²]` used in equation (6).
-/
theorem canonicalQuadraticH13_expand (s pcoord l v : ℝ) :
    v * canonicalH13 s pcoord l v ^ 2
      =
    16 * weightPolynomial (canonicalR s pcoord) ^ 2 * v
      - 96
        * (weightPolynomial (canonicalR s pcoord) ^ 2
          / canonicalDenom s pcoord)
        * (v ^ 2 / l)
      + 144
        * (weightPolynomial (canonicalR s pcoord) ^ 2
          / canonicalDenom s pcoord ^ 2)
        * (v ^ 3 / l ^ 2) := by
  unfold canonicalH13 canonicalQ13
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The canonical denominator in the centered beta coordinate `x=2P-1`. -/
theorem canonicalDenom_centered (s x : ℝ) :
    canonicalDenom s ((1 + x) / 2) = dSX s x := by
  unfold canonicalDenom canonicalTheta dSX
  ring

/-- The canonical Graybill--Deal weight in centered beta coordinates. -/
theorem canonicalR_centered {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    canonicalR s ((1 + x) / 2) = rSX s x := by
  have hne : 1 + s * x ≠ 0 := ne_of_gt (one_add_sx_pos hs hx)
  unfold canonicalR
  rw [canonicalDenom_centered]
  unfold canonicalTheta dSX rSX
  field_simp [hne]

/--
The exact centered-coordinate form of the linear `P`-integrand.  Multiplying
by the beta density `Ka(1-x²)^5` produces the kernel defining `Bg13`.
-/
theorem canonicalLinearPIntegrand13_centered {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    canonicalLinearPIntegrand13 s ((1 + x) / 2)
      =
    -((1 - s ^ 2) ^ 2 / 8)
      * ((1 - x ^ 2) * x * (s + x) * (2 / 11 + s * x)
        / (1 + s * x) ^ 5) := by
  have hne : 1 + s * x ≠ 0 := ne_of_gt (one_add_sx_pos hs hx)
  unfold canonicalLinearPIntegrand13
  rw [canonicalR_centered hs hx, canonicalDenom_centered]
  change
    (rSX s x - thetaOfS s) * p (rSX s x)
        * (1 - 9 / (22 * dSX s x)) =
      -((1 - s ^ 2) ^ 2 / 8)
        * ((1 - x ^ 2) * x * (s + x) * (2 / 11 + s * x)
          / (1 + s * x) ^ 5)
  rw [rSX_sub_thetaOfS hs hx, p_rSX hs hx]
  unfold dSX
  field_simp [hne]
  ring

/--
The exact centered-coordinate form of the quadratic `P`-integrand.
Multiplying by `Ka(1-x²)^5` produces the integrand defining `Cg13`.
-/
theorem canonicalQuadraticPIntegrand13_centered {s x : ℝ}
    (hs : |s| < 1) (hx : |x| ≤ 1) :
    canonicalQuadraticPIntegrand13 s ((1 + x) / 2)
      =
    (1 - s ^ 2) ^ 2 / 16
      * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2 / (1 + s * x) ^ 6
        - (18 / 11) * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2)
            / (1 + s * x) ^ 7
        + (27 / 22) * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2)
            / (1 + s * x) ^ 8) := by
  have hne : 1 + s * x ≠ 0 := ne_of_gt (one_add_sx_pos hs hx)
  unfold canonicalQuadraticPIntegrand13
  rw [canonicalR_centered hs hx, canonicalDenom_centered]
  change
    p (rSX s x) ^ 2
        * (1 - 9 / (11 * dSX s x) + 27 / (88 * dSX s x ^ 2)) =
      (1 - s ^ 2) ^ 2 / 16
        * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2 / (1 + s * x) ^ 6
          - (18 / 11) * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2)
              / (1 + s * x) ^ 7
          + (27 / 22) * ((1 - x ^ 2) ^ 2 * (s + x) ^ 2)
              / (1 + s * x) ^ 8)
  rw [p_rSX hs hx]
  unfold dSX
  field_simp [hne]
  ring

/--
The beta-coordinate change of variables identifies the remaining linear
expectation with `Bg13`.  The hypothesis is the exact integration formula
for the centered `Beta(6,6)` coordinate; the rest of the proof is now
machine-checked algebra and interval integration.
-/
theorem canonicalLinearPExpectation_eq_Bg13
    (Ka s : ℝ) (P : Ω → ℝ) (ℙ : Measure Ω)
    (hs : |s| < 1)
    (hbeta :
      (∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        canonicalLinearPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5) :
    (∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂ℙ) = Bg13 Ka s := by
  have hcentered :
      (∫ x in (-1 : ℝ)..1,
        canonicalLinearPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5)
        =
      -((1 - s ^ 2) ^ 2 / 8) * I13 s := by
    unfold I13
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hxabs : |x| ≤ 1 := by
      rw [abs_le]
      exact hx
    dsimp only
    rw [canonicalLinearPIntegrand13_centered hs hxabs]
    unfold linearKernel13 linearCore13 alpha13
    ring
  rw [hbeta, hcentered]
  unfold Bg13
  ring

/--
The analogous beta-coordinate calculation for the quadratic expectation.
The hypothesis isolates only the centered `Beta(6,6)` integration formula.
-/
theorem canonicalQuadraticPExpectation_eq_Cg13
    (Ka s : ℝ) (P : Ω → ℝ) (ℙ : Measure Ω)
    (hs : |s| < 1)
    (hbeta :
      (∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        canonicalQuadraticPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5) :
    (∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂ℙ) = Cg13 Ka s := by
  have hcentered :
      (∫ x in (-1 : ℝ)..1,
        canonicalQuadraticPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5)
        =
      (1 - s ^ 2) ^ 2 / 16
        * (∫ x in (-1 : ℝ)..1, CgIntegrand13 s x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hxabs : |x| ≤ 1 := by
      rw [abs_le]
      exact hx
    dsimp only
    rw [canonicalQuadraticPIntegrand13_centered hs hxabs]
    unfold CgIntegrand13
    ring
  rw [hbeta, hcentered]
  unfold Cg13
  ring

/--
The normalized quadratic risk difference in canonical coordinates.

Multiplication by `λ/13` converts this quantity to the ordinary squared-risk
difference after the common centered term has been removed by orthogonality.
-/
def canonicalNormalizedRiskDifference13
    (ε s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω) : ℝ :=
  ∫ ω,
    V ω *
      ((canonicalWeight13 ε s (P ω) (L ω) (V ω) - canonicalTheta s) ^ 2
        - (canonicalR s (P ω) - canonicalTheta s) ^ 2) ∂ℙ

/--
The exact two-moment interface between a canonical probability law and the
one-dimensional analytic quantities certified in `Reduced.lean`.

Proving this proposition from the beta--gamma product law is the remaining
distributional calculation; all later bridge theorems consume only these two
expectations.
-/
structure CanonicalMomentBridge13
    (Ka s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω) : Prop where
  linear_integrable :
    Integrable
      (fun ω =>
        V ω * (canonicalR s (P ω) - canonicalTheta s)
          * canonicalH13 s (P ω) (L ω) (V ω)) ℙ
  quadratic_integrable :
    Integrable
      (fun ω =>
        V ω * (canonicalH13 s (P ω) (L ω) (V ω)) ^ 2) ℙ
  linear_moment :
    (∫ ω,
      V ω * (canonicalR s (P ω) - canonicalTheta s)
        * canonicalH13 s (P ω) (L ω) (V ω) ∂ℙ)
      = Btheta13 Ka s
  quadratic_moment :
    (∫ ω,
      V ω * (canonicalH13 s (P ω) (L ω) (V ω)) ^ 2 ∂ℙ)
      = Ctheta13 Ka s

/--
Build the two-moment bridge from its two genuinely probabilistic pieces:

1. integrate out the independent `V,L` coordinates using their five required
   moments, leaving the two `P`-integrands;
2. apply the centered `Beta(6,6)` integration formula.

The deterministic passage from those statements to `Btheta13,Ctheta13` is
fully proved here.
-/
theorem canonicalMomentBridge13_of_product_reductions
    (Ka s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hs : |s| < 1)
    (hlinear_integrable :
      Integrable
        (fun ω =>
          V ω * (canonicalR s (P ω) - canonicalTheta s)
            * canonicalH13 s (P ω) (L ω) (V ω)) ℙ)
    (hquadratic_integrable :
      Integrable
        (fun ω =>
          V ω * (canonicalH13 s (P ω) (L ω) (V ω)) ^ 2) ℙ)
    (hlinear_product_reduction :
      (∫ ω,
        V ω * (canonicalR s (P ω) - canonicalTheta s)
          * canonicalH13 s (P ω) (L ω) (V ω) ∂ℙ)
        =
      4 * ∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂ℙ)
    (hquadratic_product_reduction :
      (∫ ω,
        V ω * (canonicalH13 s (P ω) (L ω) (V ω)) ^ 2 ∂ℙ)
        =
      16 * ∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂ℙ)
    (hbeta_linear :
      (∫ ω, canonicalLinearPIntegrand13 s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        canonicalLinearPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5)
    (hbeta_quadratic :
      (∫ ω, canonicalQuadraticPIntegrand13 s (P ω) ∂ℙ)
        =
      Ka * ∫ x in (-1 : ℝ)..1,
        canonicalQuadraticPIntegrand13 s ((1 + x) / 2)
          * (1 - x ^ 2) ^ 5) :
    CanonicalMomentBridge13 Ka s P L V ℙ := by
  refine
    { linear_integrable := hlinear_integrable
      quadratic_integrable := hquadratic_integrable
      linear_moment := ?_
      quadratic_moment := ?_ }
  · rw [hlinear_product_reduction,
      canonicalLinearPExpectation_eq_Bg13 Ka s P ℙ hs hbeta_linear]
    unfold Btheta13
    rfl
  · rw [hquadratic_product_reduction,
      canonicalQuadraticPExpectation_eq_Cg13 Ka s P ℙ hs hbeta_quadratic]
    unfold Ctheta13
    rfl

/--
The canonical normalized risk difference is exactly the reduced quadratic
expression.  This is the algebra-and-expectation half of equation (2).
-/
theorem canonicalNormalizedRiskDifference13_eq_reduced
    (Ka ε s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hbridge : CanonicalMomentBridge13 Ka s P L V ℙ) :
    canonicalNormalizedRiskDifference13 ε s P L V ℙ
      =
        2 * ε * Btheta13 Ka s + ε ^ 2 * Ctheta13 Ka s := by
  let linear : Ω → ℝ :=
    fun ω =>
      V ω * (canonicalR s (P ω) - canonicalTheta s)
        * canonicalH13 s (P ω) (L ω) (V ω)
  let quadratic : Ω → ℝ :=
    fun ω => V ω * (canonicalH13 s (P ω) (L ω) (V ω)) ^ 2
  have hpointwise :
      ∀ ω,
        V ω *
            ((canonicalWeight13 ε s (P ω) (L ω) (V ω)
                - canonicalTheta s) ^ 2
              - (canonicalR s (P ω) - canonicalTheta s) ^ 2)
          =
        2 * ε * linear ω + ε ^ 2 * quadratic ω := by
    intro ω
    unfold canonicalWeight13
    rw [perturbation_sq_sub_diff]
    dsimp only [linear, quadratic]
    ring
  unfold canonicalNormalizedRiskDifference13
  calc
    (∫ ω,
      V ω *
        ((canonicalWeight13 ε s (P ω) (L ω) (V ω)
            - canonicalTheta s) ^ 2
          - (canonicalR s (P ω) - canonicalTheta s) ^ 2) ∂ℙ)
        =
      ∫ ω, 2 * ε * linear ω + ε ^ 2 * quadratic ω ∂ℙ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hpointwise ω
    _ =
        (∫ ω, 2 * ε * linear ω ∂ℙ)
          + ∫ ω, ε ^ 2 * quadratic ω ∂ℙ := by
            exact integral_add
              (hbridge.linear_integrable.const_mul (2 * ε))
              (hbridge.quadratic_integrable.const_mul (ε ^ 2))
    _ =
        2 * ε * (∫ ω, linear ω ∂ℙ)
          + ε ^ 2 * (∫ ω, quadratic ω ∂ℙ) := by
            rw [integral_const_mul, integral_const_mul]
    _ = 2 * ε * Btheta13 Ka s + ε ^ 2 * Ctheta13 Ka s := by
      rw [show (∫ ω, linear ω ∂ℙ) = Btheta13 Ka s by
            exact hbridge.linear_moment,
          show (∫ ω, quadratic ω ∂ℙ) = Ctheta13 Ka s by
            exact hbridge.quadratic_moment]

/--
Under the exact canonical moment bridge, the normalized risk difference of
the un-clipped competitor is strictly negative.
-/
theorem canonicalNormalizedRiskDifference13_neg
    (Ka s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hKa : 0 < Ka) (hs : |s| < 1)
    (hbridge : CanonicalMomentBridge13 Ka s P L V ℙ) :
    canonicalNormalizedRiskDifference13 epsilon13 s P L V ℙ < 0 := by
  rw [canonicalNormalizedRiskDifference13_eq_reduced
    Ka epsilon13 s P L V ℙ hbridge]
  exact reducedRiskDifference13_neg Ka hKa hs

/--
Estimator-level probability bridge.

Here `centered` is the error of the known-variance estimator, `D` is the
difference of sample means, and `P,L` are the beta--gamma coordinates.  The
canonical variable `V` is defined, rather than assumed, to be `13D²/λ`.
The hypotheses involving `centered` are exactly the integrability and
orthogonality conditions needed by `sqRisk_weight_difference`.
-/
theorem canonicalEstimatorRiskDifference13_neg
    (μ varianceSum Ka s : ℝ) (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum) (hKa : 0 < Ka) (hs : |s| < 1)
    (hbridge :
      CanonicalMomentBridge13 Ka s P L
        (fun ω => standardizedDifference13 varianceSum (D ω)) ℙ)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) ℙ)
    (hcross_new :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (canonicalWeight13 epsilon13 s (P ω) (L ω)
                (standardizedDifference13 varianceSum (D ω))
              - canonicalTheta s)) ℙ)
    (hcross_base :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (canonicalR s (P ω) - canonicalTheta s)) ℙ)
    (hquadratic_new :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * (canonicalWeight13 epsilon13 s (P ω) (L ω)
                (standardizedDifference13 varianceSum (D ω))
              - canonicalTheta s) ^ 2) ℙ)
    (hquadratic_base :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * (canonicalR s (P ω) - canonicalTheta s) ^ 2) ℙ)
    (hcross_new_zero :
      (∫ ω,
        centered ω * D ω
          * (canonicalWeight13 epsilon13 s (P ω) (L ω)
              (standardizedDifference13 varianceSum (D ω))
            - canonicalTheta s) ∂ℙ) = 0)
    (hcross_base_zero :
      (∫ ω,
        centered ω * D ω
          * (canonicalR s (P ω) - canonicalTheta s) ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (canonicalWeight13 epsilon13 s (P ω) (L ω)
                (standardizedDifference13 varianceSum (D ω))
              - canonicalTheta s)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω * (canonicalR s (P ω) - canonicalTheta s)) ℙ := by
  let V : Ω → ℝ := fun ω => standardizedDifference13 varianceSum (D ω)
  let w : Ω → ℝ :=
    fun ω => canonicalWeight13 epsilon13 s (P ω) (L ω) (V ω)
  let r : Ω → ℝ := fun ω => canonicalR s (P ω)
  have hrisk :=
    sqRisk_weight_difference μ (canonicalTheta s)
      centered D w r ℙ hcentered_sq hcross_new hcross_base
      hquadratic_new hquadratic_base hcross_new_zero hcross_base_zero
  have hnormalized :
      canonicalNormalizedRiskDifference13 epsilon13 s P L V ℙ < 0 :=
    canonicalNormalizedRiskDifference13_neg Ka s P L V ℙ
      hKa hs hbridge
  have hscale : 0 < varianceSum / 13 := by positivity
  rw [sub_lt_zero.symm]
  rw [hrisk]
  calc
    (∫ ω,
      (D ω) ^ 2 * ((w ω - canonicalTheta s) ^ 2
        - (r ω - canonicalTheta s) ^ 2) ∂ℙ)
        =
      varianceSum / 13 * canonicalNormalizedRiskDifference13
        epsilon13 s P L V ℙ := by
          unfold canonicalNormalizedRiskDifference13
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with ω
          dsimp only [V, w, r]
          rw [← scale_standardizedDifference13 varianceSum (D ω)
            (ne_of_gt hvarianceSum)]
          ring
    _ < 0 := mul_neg_of_pos_of_neg hscale hnormalized

end

end GraybillDeal
