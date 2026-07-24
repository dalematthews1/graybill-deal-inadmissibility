import GraybillDeal.GeneralQuadraticBounds
import GraybillDeal.Canonical

/-!
# Canonical risk bridge at arbitrary equal sample size

This file is the sample-size-generic deterministic interface between the
reduced analytic coefficients and an actual squared-risk comparison.  The
probabilistic input is isolated in `GeneralCanonicalMomentBridge`: it records
the two moments which later follow from the beta--gamma component laws.
-/

namespace GraybillDeal

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The perturbation direction `h = p(r) (4-q)` at residual df `ν`. -/
def generalCanonicalH (ν s pcoord l v : ℝ) : ℝ :=
  4 * canonicalG ν (canonicalTheta s) pcoord l v

/-- The un-clipped perturbed canonical weight. -/
def generalCanonicalWeight
    (ε ν s pcoord l v : ℝ) : ℝ :=
  perturbation (canonicalR s pcoord) ε
    (generalCanonicalH ν s pcoord l v)

/-- The standardized mean-difference square for sample size `ν+1`. -/
def generalStandardizedDifference
    (ν varianceSum d : ℝ) : ℝ :=
  (ν + 1) * d ^ 2 / varianceSum

theorem generalCanonicalH_eq
    (ν s pcoord l v : ℝ) :
    generalCanonicalH ν s pcoord l v
      =
    weightPolynomial (canonicalR s pcoord)
      * (4 - canonicalQ ν (canonicalTheta s) pcoord l v) := by
  unfold generalCanonicalH canonicalG
  rw [canonicalRTheta_canonicalTheta]
  ring

theorem scale_generalStandardizedDifference
    (ν varianceSum d : ℝ)
    (hvarianceSum : varianceSum ≠ 0) (hν : ν + 1 ≠ 0) :
    varianceSum / (ν + 1)
        * generalStandardizedDifference ν varianceSum d
      = d ^ 2 := by
  unfold generalStandardizedDifference
  field_simp

/-- The normalized quadratic risk difference in generic canonical coordinates. -/
def generalCanonicalNormalizedRiskDifference
    (ε ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω) : ℝ :=
  ∫ ω,
    V ω *
      ((generalCanonicalWeight ε ν s (P ω) (L ω) (V ω)
          - canonicalTheta s) ^ 2
        - (canonicalR s (P ω) - canonicalTheta s) ^ 2) ∂ℙ

/--
The exact two-moment interface between the generic component laws and the
reduced coefficients.
-/
structure GeneralCanonicalMomentBridge
    (Ka ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω) : Prop where
  linear_integrable :
    Integrable
      (fun ω =>
        V ω * (canonicalR s (P ω) - canonicalTheta s)
          * generalCanonicalH ν s (P ω) (L ω) (V ω)) ℙ
  quadratic_integrable :
    Integrable
      (fun ω =>
        V ω * (generalCanonicalH ν s (P ω) (L ω) (V ω)) ^ 2) ℙ
  linear_moment :
    (∫ ω,
      V ω * (canonicalR s (P ω) - canonicalTheta s)
        * generalCanonicalH ν s (P ω) (L ω) (V ω) ∂ℙ)
      = generalBtheta Ka ν s
  quadratic_moment :
    (∫ ω,
      V ω * (generalCanonicalH ν s (P ω) (L ω) (V ω)) ^ 2 ∂ℙ)
      = generalCtheta Ka ν s

/-- The canonical normalized risk difference is exactly the reduced expression. -/
theorem generalCanonicalNormalizedRiskDifference_eq_reduced
    (Ka ε ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hbridge : GeneralCanonicalMomentBridge Ka ν s P L V ℙ) :
    generalCanonicalNormalizedRiskDifference ε ν s P L V ℙ
      =
    2 * ε * generalBtheta Ka ν s
      + ε ^ 2 * generalCtheta Ka ν s := by
  let linear : Ω → ℝ :=
    fun ω =>
      V ω * (canonicalR s (P ω) - canonicalTheta s)
        * generalCanonicalH ν s (P ω) (L ω) (V ω)
  let quadratic : Ω → ℝ :=
    fun ω =>
      V ω * (generalCanonicalH ν s (P ω) (L ω) (V ω)) ^ 2
  have hpointwise :
      ∀ ω,
        V ω *
            ((generalCanonicalWeight ε ν s (P ω) (L ω) (V ω)
                - canonicalTheta s) ^ 2
              - (canonicalR s (P ω) - canonicalTheta s) ^ 2)
          =
        2 * ε * linear ω + ε ^ 2 * quadratic ω := by
    intro ω
    unfold generalCanonicalWeight
    rw [perturbation_sq_sub_diff]
    dsimp only [linear, quadratic]
    ring
  unfold generalCanonicalNormalizedRiskDifference
  calc
    (∫ ω,
      V ω *
        ((generalCanonicalWeight ε ν s (P ω) (L ω) (V ω)
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
    _ =
      2 * ε * generalBtheta Ka ν s
        + ε ^ 2 * generalCtheta Ka ν s := by
          rw [show (∫ ω, linear ω ∂ℙ) = generalBtheta Ka ν s by
                exact hbridge.linear_moment,
            show (∫ ω, quadratic ω ∂ℙ) = generalCtheta Ka ν s by
                exact hbridge.quadratic_moment]

theorem generalCanonicalNormalizedRiskDifference_neg
    (Ka ε ν s : ℝ) (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hbridge : GeneralCanonicalMomentBridge Ka ν s P L V ℙ)
    (hreduced :
      2 * ε * generalBtheta Ka ν s
        + ε ^ 2 * generalCtheta Ka ν s < 0) :
    generalCanonicalNormalizedRiskDifference ε ν s P L V ℙ < 0 := by
  rw [generalCanonicalNormalizedRiskDifference_eq_reduced
    Ka ε ν s P L V ℙ hbridge]
  exact hreduced

/--
Once the two canonical moments are available for every variance ratio, the
endpoint bounds produce one positive perturbation coefficient whose
normalized risk difference is negative for every `|s| < 1`.
-/
theorem exists_generalCanonicalRisk_epsilon
    (Ka : ℝ) (ν : ℕ) (hν : 9 ≤ ν) (hKa : 0 < Ka)
    (P L V : Ω → ℝ) (ℙ : Measure Ω)
    (hbridge :
      ∀ s : ℝ, |s| < 1 →
        GeneralCanonicalMomentBridge
          Ka (ν : ℝ) s P L V ℙ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, |s| < 1 →
        generalCanonicalNormalizedRiskDifference
          ε (ν : ℝ) s P L V ℙ < 0 := by
  obtain ⟨ε, hε, hreduced⟩ :=
    exists_generalReducedRisk_epsilon_unconditional
      Ka ν hν hKa
  refine ⟨ε, hε, ?_⟩
  intro s hs
  exact generalCanonicalNormalizedRiskDifference_neg
    Ka ε (ν : ℝ) s P L V ℙ
      (hbridge s hs) (hreduced s hs)

/--
Estimator-level risk bridge for a fixed residual df and perturbation size.
All probability-law work is confined to `hbridge`; the remaining assumptions
are exactly the integrability and orthogonality hypotheses required by the
general squared-risk identity.
-/
theorem generalCanonicalEstimatorRiskDifference_neg
    (ν : ℕ) (hν : 9 ≤ ν)
    (μ varianceSum Ka ε s : ℝ)
    (centered D P L : Ω → ℝ) (ℙ : Measure Ω)
    (hvarianceSum : 0 < varianceSum)
    (hbridge :
      GeneralCanonicalMomentBridge Ka (ν : ℝ) s P L
        (fun ω =>
          generalStandardizedDifference (ν : ℝ)
            varianceSum (D ω)) ℙ)
    (hreduced :
      2 * ε * generalBtheta Ka (ν : ℝ) s
        + ε ^ 2 * generalCtheta Ka (ν : ℝ) s < 0)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) ℙ)
    (hcross_new :
      Integrable
        (fun ω =>
          centered ω * D ω
            * (generalCanonicalWeight ε (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
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
            * (generalCanonicalWeight ε (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
              - canonicalTheta s) ^ 2) ℙ)
    (hquadratic_base :
      Integrable
        (fun ω =>
          (D ω) ^ 2
            * (canonicalR s (P ω) - canonicalTheta s) ^ 2) ℙ)
    (hcross_new_zero :
      (∫ ω,
        centered ω * D ω
          * (generalCanonicalWeight ε (ν : ℝ) s
              (P ω) (L ω)
              (generalStandardizedDifference (ν : ℝ)
                varianceSum (D ω))
            - canonicalTheta s) ∂ℙ) = 0)
    (hcross_base_zero :
      (∫ ω,
        centered ω * D ω
          * (canonicalR s (P ω) - canonicalTheta s) ∂ℙ) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (generalCanonicalWeight ε (ν : ℝ) s
                (P ω) (L ω)
                (generalStandardizedDifference (ν : ℝ)
                  varianceSum (D ω))
              - canonicalTheta s)) ℙ
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω * (canonicalR s (P ω) - canonicalTheta s)) ℙ := by
  let V : Ω → ℝ :=
    fun ω =>
      generalStandardizedDifference (ν : ℝ) varianceSum (D ω)
  let w : Ω → ℝ :=
    fun ω =>
      generalCanonicalWeight ε (ν : ℝ) s (P ω) (L ω) (V ω)
  let r : Ω → ℝ := fun ω => canonicalR s (P ω)
  have hrisk :=
    sqRisk_weight_difference μ (canonicalTheta s)
      centered D w r ℙ hcentered_sq hcross_new hcross_base
      hquadratic_new hquadratic_base hcross_new_zero hcross_base_zero
  have hnormalized :
      generalCanonicalNormalizedRiskDifference
        ε (ν : ℝ) s P L V ℙ < 0 :=
    generalCanonicalNormalizedRiskDifference_neg
      Ka ε (ν : ℝ) s P L V ℙ hbridge hreduced
  have hνplus : (0 : ℝ) < (ν : ℝ) + 1 := by positivity
  have hscale : 0 < varianceSum / ((ν : ℝ) + 1) := by
    positivity
  rw [sub_lt_zero.symm]
  rw [hrisk]
  calc
    (∫ ω,
      (D ω) ^ 2 * ((w ω - canonicalTheta s) ^ 2
        - (r ω - canonicalTheta s) ^ 2) ∂ℙ)
        =
      varianceSum / ((ν : ℝ) + 1)
        * generalCanonicalNormalizedRiskDifference
          ε (ν : ℝ) s P L V ℙ := by
            unfold generalCanonicalNormalizedRiskDifference
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards [] with ω
            dsimp only [V, w, r]
            rw [← scale_generalStandardizedDifference
              (ν : ℝ) varianceSum (D ω)
              (ne_of_gt hvarianceSum) (ne_of_gt hνplus)]
            ring
    _ < 0 := mul_neg_of_pos_of_neg hscale hnormalized

end

end GraybillDeal
