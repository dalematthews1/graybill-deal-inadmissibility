import GraybillDeal.UniversalReducedChangeOfVariables
import GraybillDeal.UniversalRadialGammaIntegral

/-!
# Nested-coordinate density bridge

The Jacobian theorem in `UniversalReducedChangeOfVariables` is stated on
the Euclidean model `Fin 3 → ℝ`.  Raw component laws, however, naturally
live on the right-associated triple `ℝ × (ℝ × ℝ)`.  This file transports
the Jacobian theorem to that nested model and combines it with the radial
Gamma integral.

No probability law is assumed here.  The result is a purely analytic
pushforward identity for the canonical positive triple.
-/

namespace GraybillDeal

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The standard measurable equivalence which reads a three-vector as the
right-associated triple `(x₀,(x₁,x₂))`. -/
def universalFinThreeToNestedMeasurableEquiv :
    (Fin 3 → ℝ) ≃ᵐ (ℝ × ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)))

@[simp]
theorem universalFinThreeToNestedMeasurableEquiv_apply
    (x : Fin 3 → ℝ) :
    universalFinThreeToNestedMeasurableEquiv x
      =
    universalTripleContinuousLinearEquiv.symm x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> rfl

@[simp]
theorem universalFinThreeToNestedMeasurableEquiv_symm_apply
    (z : ℝ × ℝ × ℝ) :
    universalFinThreeToNestedMeasurableEquiv.symm z
      =
    universalTripleContinuousLinearEquiv z := by
  apply universalFinThreeToNestedMeasurableEquiv.injective
  simp

/-- Reading a three-vector as a nested triple preserves three-dimensional
Lebesgue measure. -/
theorem measurePreserving_universalFinThreeToNestedMeasurableEquiv :
    MeasurePreserving
      (universalFinThreeToNestedMeasurableEquiv :
        (Fin 3 → ℝ) → (ℝ × ℝ × ℝ))
      volume volume := by
  exact
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurePreserving.id (volume : Measure ℝ)).prod
        (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)))

theorem measurableSet_universalReducedRadialSource :
    MeasurableSet universalReducedRadialSource :=
  (isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioi)).measurableSet

theorem measurableSet_universalCanonicalPositiveTarget :
    MeasurableSet universalCanonicalPositiveTarget :=
  (isOpen_Ioi.prod (isOpen_Ioi.prod isOpen_Ioi)).measurableSet

theorem universalFinThreeToNested_preimage_radialSource :
    universalFinThreeToNestedMeasurableEquiv ⁻¹'
        universalReducedRadialSource
      =
    universalReducedRadialSourceVec := by
  ext x
  constructor
  · intro hx
    exact
      ⟨universalFinThreeToNestedMeasurableEquiv x, hx, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    simpa using hz

theorem universalFinThreeToNested_preimage_canonicalTarget :
    universalFinThreeToNestedMeasurableEquiv ⁻¹'
        universalCanonicalPositiveTarget
      =
    universalCanonicalPositiveTargetVec := by
  ext x
  constructor
  · intro hx
    exact
      ⟨universalFinThreeToNestedMeasurableEquiv x, hx, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    simpa using hz

/-- The complete Jacobian change of variables on the native nested-triple
coordinate model. -/
theorem lintegral_universalReducedRadialToCanonical_nested
    (g : (ℝ × ℝ × ℝ) → ℝ≥0∞) :
    (∫⁻ z in universalCanonicalPositiveTarget, g z)
      =
    ∫⁻ z in universalReducedRadialSource,
      ENNReal.ofReal (z.2.2 ^ 2)
        * g (universalReducedRadialToCanonical z) := by
  let e := universalFinThreeToNestedMeasurableEquiv
  have he :=
    measurePreserving_universalFinThreeToNestedMeasurableEquiv
  have hemb : MeasurableEmbedding (e : (Fin 3 → ℝ) → (ℝ × ℝ × ℝ)) :=
    e.measurableEmbedding
  have htarget :=
    (he.restrict_preimage
      measurableSet_universalCanonicalPositiveTarget).lintegral_comp_emb
        hemb g
  have hsource :=
    (he.restrict_preimage
      measurableSet_universalReducedRadialSource).lintegral_comp_emb
        hemb
        (fun z =>
          ENNReal.ofReal (z.2.2 ^ 2)
            * g (universalReducedRadialToCanonical z))
  have hvec :=
    lintegral_universalReducedRadialToCanonicalVec
      (fun x => g (universalTripleContinuousLinearEquiv.symm x))
  rw [universalFinThreeToNested_preimage_canonicalTarget] at htarget
  rw [universalFinThreeToNested_preimage_radialSource] at hsource
  calc
    (∫⁻ z in universalCanonicalPositiveTarget, g z)
        =
      ∫⁻ x in universalCanonicalPositiveTargetVec,
        g (universalTripleContinuousLinearEquiv.symm x) := by
          simpa [e] using htarget.symm
    _ =
      ∫⁻ x in universalReducedRadialSourceVec,
        ENNReal.ofReal
            ((universalTripleContinuousLinearEquiv.symm x).2.2 ^ 2)
          * g
              (universalTripleContinuousLinearEquiv.symm
                (universalReducedRadialToCanonicalVec x)) := hvec
    _ =
      ∫⁻ z in universalReducedRadialSource,
        ENNReal.ofReal (z.2.2 ^ 2)
          * g (universalReducedRadialToCanonical z) := by
            simpa [e, universalReducedRadialToCanonicalVec] using hsource

/-! ## A total measurable reduced-coordinate projection -/

/-- The open support of the reduced pair in the ambient plane. -/
def universalReducedAmbientSupport : Set (ℝ × ℝ) :=
  Ioo (0 : ℝ) 1 ×ˢ Ioi 0

theorem measurableSet_universalReducedAmbientSupport :
    MeasurableSet universalReducedAmbientSupport :=
  measurableSet_Ioo.prod measurableSet_Ioi

/-- A fixed interior point used only to totalize the reduced-coordinate
projection away from its positive support. -/
def universalReducedObservationFallback : UniversalReducedObservation :=
  ⟨((1 / 2 : ℝ), 1), by norm_num⟩

/-- Totalized first reduced coordinate. -/
def universalSafeReducedR (r : ℝ) : ℝ :=
  if r ∈ Ioo (0 : ℝ) 1 then r else 1 / 2

/-- Totalized second reduced coordinate. -/
def universalSafeReducedQ (q : ℝ) : ℝ :=
  if q ∈ Ioi (0 : ℝ) then q else 1

theorem universalSafeReducedR_pos (r : ℝ) :
    0 < universalSafeReducedR r := by
  unfold universalSafeReducedR
  split_ifs with h
  · exact h.1
  · norm_num

theorem universalSafeReducedR_lt_one (r : ℝ) :
    universalSafeReducedR r < 1 := by
  unfold universalSafeReducedR
  split_ifs with h
  · exact h.2
  · norm_num

theorem universalSafeReducedQ_pos (q : ℝ) :
    0 < universalSafeReducedQ q := by
  unfold universalSafeReducedQ
  split_ifs with h
  · exact h
  · norm_num

@[measurability, fun_prop]
theorem measurable_universalSafeReducedR :
    Measurable universalSafeReducedR := by
  unfold universalSafeReducedR
  exact Measurable.ite measurableSet_Ioo measurable_id measurable_const

@[measurability, fun_prop]
theorem measurable_universalSafeReducedQ :
    Measurable universalSafeReducedQ := by
  unfold universalSafeReducedQ
  exact Measurable.ite measurableSet_Ioi measurable_id measurable_const

/-- Total measurable inclusion of an ambient pair into the reduced sample
space.  It agrees with the literal subtype inclusion on the open support
and takes a harmless fixed value elsewhere. -/
def universalSafeReducedObservation
    (x : ℝ × ℝ) : UniversalReducedObservation :=
  ⟨(universalSafeReducedR x.1, universalSafeReducedQ x.2),
    universalSafeReducedR_pos x.1,
    universalSafeReducedR_lt_one x.1,
    universalSafeReducedQ_pos x.2⟩

@[measurability, fun_prop]
theorem measurable_universalSafeReducedObservation :
    Measurable universalSafeReducedObservation := by
  unfold universalSafeReducedObservation
  exact
    ((measurable_universalSafeReducedR.comp measurable_fst).prodMk
      (measurable_universalSafeReducedQ.comp measurable_snd)).subtype_mk

@[simp]
theorem universalSafeReducedObservation_of_mem
    {x : ℝ × ℝ} (hx : x ∈ universalReducedAmbientSupport) :
    (universalSafeReducedObservation x : ℝ × ℝ) = x := by
  rcases hx with ⟨hr, hq⟩
  simp [universalSafeReducedObservation, universalSafeReducedR,
    universalSafeReducedQ, hr, hq]

@[simp]
theorem universalSafeReducedObservation_coe
    (x : UniversalReducedObservation) :
    universalSafeReducedObservation (x : ℝ × ℝ) = x := by
  apply Subtype.ext
  exact universalSafeReducedObservation_of_mem
    ⟨⟨x.r_pos, x.r_lt_one⟩, x.q_pos⟩

/-- Ambient reduced pair obtained from a canonical triple. -/
def universalCanonicalReducedPairNested
    (z : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  (z.1 / (z.1 + z.2.1), z.2.2 / (z.1 + z.2.1))

@[measurability, fun_prop]
theorem measurable_universalCanonicalReducedPairNested :
    Measurable universalCanonicalReducedPairNested := by
  unfold universalCanonicalReducedPairNested
  fun_prop

/-- Total measurable canonical-to-reduced projection. -/
def universalCanonicalToReducedObservationNested
    (z : ℝ × ℝ × ℝ) : UniversalReducedObservation :=
  universalSafeReducedObservation (universalCanonicalReducedPairNested z)

@[measurability, fun_prop]
theorem measurable_universalCanonicalToReducedObservationNested :
    Measurable universalCanonicalToReducedObservationNested :=
  measurable_universalSafeReducedObservation.comp
    measurable_universalCanonicalReducedPairNested

theorem universalCanonicalReducedPairNested_mem
    {z : ℝ × ℝ × ℝ}
    (hz : z ∈ universalCanonicalPositiveTarget) :
    universalCanonicalReducedPairNested z ∈ universalReducedAmbientSupport := by
  rcases hz with ⟨hg₁, hg₂, hw⟩
  change 0 < z.1 at hg₁
  change 0 < z.2.1 at hg₂
  change 0 < z.2.2 at hw
  have hsum : 0 < z.1 + z.2.1 := add_pos hg₁ hg₂
  exact
    ⟨⟨div_pos hg₁ hsum,
        (div_lt_one hsum).2 (by linarith)⟩,
      div_pos hw hsum⟩

theorem universalCanonicalToReducedObservationNested_radial
    {r q t : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (hq : 0 < q) (ht : 0 < t) :
    universalCanonicalToReducedObservationNested
        (universalReducedRadialToCanonical (r, q, t))
      =
    (⟨(r, q), hr0, hr1, hq⟩ : UniversalReducedObservation) := by
  apply Subtype.ext
  have hfull :=
    universalCanonicalToReducedRadial_toFun hr0 hr1 hq ht
  have hpair :
      universalCanonicalReducedPairNested
          (universalReducedRadialToCanonical (r, q, t))
        =
      (r, q) := by
    exact congrArg (fun z : ℝ × ℝ × ℝ => (z.1, z.2.1)) hfull
  unfold universalCanonicalToReducedObservationNested
  rw [hpair]
  exact universalSafeReducedObservation_of_mem
    ⟨⟨hr0, hr1⟩, hq⟩

/-- Joint measurability of the radially transformed integrand after the
safe reduced projection. -/
theorem measurable_universalPreRadialDensity_safe
    (a b : ℝ) (θ : UniversalInteriorTheta) :
    Measurable
      (fun z : ℝ × ℝ × ℝ =>
        universalPreRadialDensity a b θ
          (universalSafeReducedObservation (z.1, z.2.1)) z.2.2) := by
  unfold universalPreRadialDensity universalPreRadialFactor
    universalRadialGammaIntegrand universalRadialRate
    UniversalReducedObservation.r UniversalReducedObservation.q
  fun_prop

theorem universalCanonicalRadial_integrand_eq
    (a b : ℝ)
    (θ : UniversalInteriorTheta)
    (φ : UniversalReducedObservation → ℝ≥0∞)
    {z : ℝ × ℝ × ℝ}
    (hz : z ∈ universalReducedRadialSource) :
    ENNReal.ofReal (z.2.2 ^ 2)
        *
      (ENNReal.ofReal
          (universalCanonicalWeightedTripleDensity a b θ
            (universalReducedRadialToCanonical z))
        * φ
            (universalCanonicalToReducedObservationNested
              (universalReducedRadialToCanonical z)))
      =
    ENNReal.ofReal
        (universalPreRadialDensity a b θ
          (universalSafeReducedObservation (z.1, z.2.1)) z.2.2)
      * φ (universalSafeReducedObservation (z.1, z.2.1)) := by
  rcases z with ⟨r, q, t⟩
  rcases hz with ⟨hr, hq, ht⟩
  simp only [Prod.fst, Prod.snd] at hr hq ⊢
  change 0 < t at ht
  have hsafe :
      universalSafeReducedObservation (r, q)
        =
      (⟨(r, q), hr.1, hr.2, hq⟩ :
        UniversalReducedObservation) := by
    apply Subtype.ext
    exact universalSafeReducedObservation_of_mem ⟨hr, hq⟩
  have hproj :
      universalCanonicalToReducedObservationNested
          (universalReducedRadialToCanonical (r, q, t))
        =
      universalSafeReducedObservation (r, q) := by
    rw [universalCanonicalToReducedObservationNested_radial
      hr.1 hr.2 hq ht, hsafe]
  rw [hproj]
  rw [← mul_assoc]
  rw [← ENNReal.ofReal_mul (sq_nonneg t)]
  rw [show
      t ^ 2
          * universalCanonicalWeightedTripleDensity a b θ
              (universalReducedRadialToCanonical (r, q, t))
        =
      universalCanonicalWeightedTripleDensity a b θ
              (universalReducedInverseCoordinates r q t)
          * universalReducedInverseJacobian t by
        rw [universalReducedRadialToCanonical_apply]
        unfold universalReducedInverseJacobian
        ring]
  have hrSafe :
      (universalSafeReducedObservation (r, q)).r = r := by
    exact congrArg UniversalReducedObservation.r hsafe
  have hqSafe :
      (universalSafeReducedObservation (r, q)).q = q := by
    exact congrArg UniversalReducedObservation.q hsafe
  have hbridge :=
    canonicalWeightedTripleDensity_comp_inverse_mul_jacobian
      a b θ (universalSafeReducedObservation (r, q)) ht
  rw [hrSafe, hqSafe] at hbridge
  rw [hbridge]

/-! ## Integrating out the radial coordinate -/

/-- The defining ambient set of `UniversalReducedObservation`, named so
that `lintegral_subtype_comap` can be applied transparently. -/
def universalReducedObservationAmbientSet : Set (ℝ × ℝ) :=
  {x | 0 < x.1 ∧ x.1 < 1 ∧ 0 < x.2}

theorem measurableSet_universalReducedObservationAmbientSet :
    MeasurableSet universalReducedObservationAmbientSet := by
  unfold universalReducedObservationAmbientSet
  measurability

theorem universalReducedObservationAmbientSet_eq_support :
    universalReducedObservationAmbientSet
      =
    universalReducedAmbientSupport := by
  ext x
  simp [universalReducedObservationAmbientSet,
    universalReducedAmbientSupport, and_assoc]

/-- Fubini formula for the comapped Lebesgue measure on the reduced
subtype.  The safe totalization disappears on the open support. -/
theorem lintegral_universalReducedLebesgueMeasure_eq_iterated
    (φ : UniversalReducedObservation → ℝ≥0∞)
    (hφ : Measurable φ) :
    (∫⁻ x, φ x ∂universalReducedLebesgueMeasure)
      =
    ∫⁻ r : ℝ in Ioo 0 1,
      ∫⁻ q : ℝ in Ioi 0,
        φ (universalSafeReducedObservation (r, q)) := by
  have hamb :
      Measurable
        (fun x : ℝ × ℝ =>
          φ (universalSafeReducedObservation x)) :=
    hφ.comp measurable_universalSafeReducedObservation
  change
    (∫⁻ x : UniversalReducedObservation, φ x
      ∂Measure.comap Subtype.val (volume : Measure (ℝ × ℝ)))
      =
    _
  calc
    (∫⁻ x : UniversalReducedObservation, φ x
        ∂Measure.comap Subtype.val (volume : Measure (ℝ × ℝ)))
        =
      ∫⁻ x : UniversalReducedObservation,
        φ (universalSafeReducedObservation (x : ℝ × ℝ))
        ∂Measure.comap Subtype.val (volume : Measure (ℝ × ℝ)) := by
          apply lintegral_congr
          intro x
          rw [universalSafeReducedObservation_coe]
    _ =
      ∫⁻ x : ℝ × ℝ in universalReducedObservationAmbientSet,
        φ (universalSafeReducedObservation x) := by
          exact lintegral_subtype_comap
            measurableSet_universalReducedObservationAmbientSet
            (fun x : ℝ × ℝ =>
              φ (universalSafeReducedObservation x))
    _ =
      ∫⁻ x : ℝ × ℝ in universalReducedAmbientSupport,
        φ (universalSafeReducedObservation x) := by
          rw [universalReducedObservationAmbientSet_eq_support]
    _ =
      ∫⁻ r : ℝ in Ioo 0 1,
        ∫⁻ q : ℝ in Ioi 0,
          φ (universalSafeReducedObservation (r, q)) := by
          rw [universalReducedAmbientSupport, Measure.volume_eq_prod]
          exact setLIntegral_prod _ hamb.aemeasurable

/-- Test-function form of the complete analytic bridge.  A canonical
positive triple with the explicit weighted density projects to the
universal full reduced density. -/
theorem lintegral_canonicalWeightedTripleDensity_project
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (φ : UniversalReducedObservation → ℝ≥0∞)
    (hφ : Measurable φ) :
    (∫⁻ z : ℝ × ℝ × ℝ in universalCanonicalPositiveTarget,
      ENNReal.ofReal
          (universalCanonicalWeightedTripleDensity a b θ z)
        * φ (universalCanonicalToReducedObservationNested z))
      =
    ∫⁻ x : UniversalReducedObservation,
      ENNReal.ofReal (universalFullReducedDensity a b θ x)
        * φ x
      ∂universalReducedLebesgueMeasure := by
  let F : (ℝ × ℝ × ℝ) → ℝ≥0∞ :=
    fun z =>
      ENNReal.ofReal
          (universalPreRadialDensity a b θ
            (universalSafeReducedObservation (z.1, z.2.1)) z.2.2)
        * φ (universalSafeReducedObservation (z.1, z.2.1))
  have hF : Measurable F := by
    exact
      (measurable_universalPreRadialDensity_safe a b θ).ennreal_ofReal.mul
        (hφ.comp
          (measurable_universalSafeReducedObservation.comp
            (measurable_fst.prodMk
              (measurable_fst.comp measurable_snd))))
  have hcov :=
    lintegral_universalReducedRadialToCanonical_nested
      (fun z =>
        ENNReal.ofReal
            (universalCanonicalWeightedTripleDensity a b θ z)
          * φ (universalCanonicalToReducedObservationNested z))
  have hchanged :
      (∫⁻ z : ℝ × ℝ × ℝ in universalCanonicalPositiveTarget,
        ENNReal.ofReal
            (universalCanonicalWeightedTripleDensity a b θ z)
          * φ (universalCanonicalToReducedObservationNested z))
        =
      ∫⁻ z : ℝ × ℝ × ℝ in universalReducedRadialSource, F z := by
    rw [hcov]
    exact setLIntegral_congr_fun
      measurableSet_universalReducedRadialSource
      (fun z hz =>
        universalCanonicalRadial_integrand_eq a b θ φ hz)
  have hFubini :
      (∫⁻ z : ℝ × ℝ × ℝ in universalReducedRadialSource, F z)
        =
      ∫⁻ r : ℝ in Ioo 0 1,
        ∫⁻ q : ℝ in Ioi 0,
          ∫⁻ t : ℝ in Ioi 0, F (r, q, t) := by
    rw [universalReducedRadialSource, Measure.volume_eq_prod]
    rw [setLIntegral_prod F hF.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro r _hr
    rw [Measure.volume_eq_prod]
    exact
      setLIntegral_prod
        (fun y : ℝ × ℝ => F (r, y))
        ((hF.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  have hradial :
      (∫⁻ r : ℝ in Ioo 0 1,
        ∫⁻ q : ℝ in Ioi 0,
          ∫⁻ t : ℝ in Ioi 0, F (r, q, t))
        =
      ∫⁻ r : ℝ in Ioo 0 1,
        ∫⁻ q : ℝ in Ioi 0,
          ENNReal.ofReal
              (universalFullReducedDensity a b θ
                (universalSafeReducedObservation (r, q)))
            * φ (universalSafeReducedObservation (r, q)) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro r hr
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro q hq
    let x : UniversalReducedObservation :=
      universalSafeReducedObservation (r, q)
    have hx :
        x = (⟨(r, q), hr.1, hr.2, hq⟩ :
          UniversalReducedObservation) := by
      apply Subtype.ext
      exact universalSafeReducedObservation_of_mem ⟨hr, hq⟩
    have hmeas :
        Measurable
          (fun t : ℝ =>
            ENNReal.ofReal
              (universalPreRadialDensity a b θ x t)) :=
      (measurable_universalPreRadialDensity a b θ x).ennreal_ofReal
    change
      (∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal
            (universalPreRadialDensity a b θ x t)
          * φ x)
        =
      ENNReal.ofReal
          (universalFullReducedDensity a b θ x) * φ x
    rw [lintegral_mul_const (φ x) hmeas]
    rw [lintegral_universalPreRadialDensity_eq_fullReducedDensity
      ha hb θ x]
  have hright :=
    lintegral_universalReducedLebesgueMeasure_eq_iterated
      (fun x =>
        ENNReal.ofReal (universalFullReducedDensity a b θ x)
          * φ x)
      ((measurable_universalFullReducedDensity a b θ).ennreal_ofReal.mul
        hφ)
  exact hchanged.trans (hFubini.trans (hradial.trans hright.symm))

/-- Measure form of the analytic bridge.  The explicit positive canonical
triple density, restricted to its genuine support, pushes exactly to the
full universal reduced density with respect to reduced Lebesgue measure. -/
theorem map_canonicalWeightedTripleDensity_eq_reducedDensity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta) :
    Measure.map universalCanonicalToReducedObservationNested
        (((volume : Measure (ℝ × ℝ × ℝ)).restrict
            universalCanonicalPositiveTarget).withDensity
          (fun z =>
            ENNReal.ofReal
              (universalCanonicalWeightedTripleDensity a b θ z)))
      =
    universalReducedLebesgueMeasure.withDensity
      (fun x =>
        ENNReal.ofReal (universalFullReducedDensity a b θ x)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hmap :
      AEMeasurable universalCanonicalToReducedObservationNested
        (((volume : Measure (ℝ × ℝ × ℝ)).restrict
            universalCanonicalPositiveTarget).withDensity
          (fun z =>
            ENNReal.ofReal
              (universalCanonicalWeightedTripleDensity a b θ z))) :=
    measurable_universalCanonicalToReducedObservationNested.aemeasurable
  have hcanonical :
      Measurable
        (fun z : ℝ × ℝ × ℝ =>
          ENNReal.ofReal
            (universalCanonicalWeightedTripleDensity a b θ z)) :=
    (measurable_universalCanonicalWeightedTripleDensity a b θ).ennreal_ofReal
  have hreduced :
      Measurable
        (fun x : UniversalReducedObservation =>
          ENNReal.ofReal (universalFullReducedDensity a b θ x)) :=
    (measurable_universalFullReducedDensity a b θ).ennreal_ofReal
  calc
    (∫⁻ x, φ x
        ∂Measure.map universalCanonicalToReducedObservationNested
          (((volume : Measure (ℝ × ℝ × ℝ)).restrict
              universalCanonicalPositiveTarget).withDensity
            (fun z =>
              ENNReal.ofReal
                (universalCanonicalWeightedTripleDensity a b θ z))))
        =
      ∫⁻ z, φ (universalCanonicalToReducedObservationNested z)
        ∂((volume : Measure (ℝ × ℝ × ℝ)).restrict
            universalCanonicalPositiveTarget).withDensity
          (fun z =>
            ENNReal.ofReal
              (universalCanonicalWeightedTripleDensity a b θ z)) := by
          exact lintegral_map' hφ.aemeasurable hmap
    _ =
      ∫⁻ z,
        ENNReal.ofReal
            (universalCanonicalWeightedTripleDensity a b θ z)
          * φ (universalCanonicalToReducedObservationNested z)
        ∂(volume : Measure (ℝ × ℝ × ℝ)).restrict
            universalCanonicalPositiveTarget := by
          simpa only [Pi.mul_apply, Function.comp_apply] using
            lintegral_withDensity_eq_lintegral_mul
              ((volume : Measure (ℝ × ℝ × ℝ)).restrict
                universalCanonicalPositiveTarget)
              hcanonical
              (hφ.comp
                measurable_universalCanonicalToReducedObservationNested)
    _ =
      ∫⁻ z : ℝ × ℝ × ℝ in universalCanonicalPositiveTarget,
        ENNReal.ofReal
            (universalCanonicalWeightedTripleDensity a b θ z)
          * φ (universalCanonicalToReducedObservationNested z) := rfl
    _ =
      ∫⁻ x : UniversalReducedObservation,
        ENNReal.ofReal (universalFullReducedDensity a b θ x)
          * φ x
        ∂universalReducedLebesgueMeasure :=
      lintegral_canonicalWeightedTripleDensity_project
        ha hb θ φ hφ
    _ =
      ∫⁻ x, φ x
        ∂universalReducedLebesgueMeasure.withDensity
          (fun x =>
            ENNReal.ofReal
              (universalFullReducedDensity a b θ x)) := by
          simpa only [Pi.mul_apply, Function.comp_apply] using
            (lintegral_withDensity_eq_lintegral_mul
              universalReducedLebesgueMeasure hreduced hφ).symm

/-- Adapter form for downstream raw-coordinate maps.  Any total map which
agrees with the canonical reduced projection on the positive orthant has
the same exact pushforward density. -/
theorem map_canonicalWeightedTripleDensity_eq_reducedDensity_of_eqOn
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : UniversalInteriorTheta)
    (F : (ℝ × ℝ × ℝ) → UniversalReducedObservation)
    (hF :
      ∀ z ∈ universalCanonicalPositiveTarget,
        F z = universalCanonicalToReducedObservationNested z) :
    Measure.map F
        (((volume : Measure (ℝ × ℝ × ℝ)).restrict
            universalCanonicalPositiveTarget).withDensity
          (fun z =>
            ENNReal.ofReal
              (universalCanonicalWeightedTripleDensity a b θ z)))
      =
    universalReducedLebesgueMeasure.withDensity
      (fun x =>
        ENNReal.ofReal (universalFullReducedDensity a b θ x)) := by
  have hcanonical :
      Measurable
        (fun z : ℝ × ℝ × ℝ =>
          ENNReal.ofReal
            (universalCanonicalWeightedTripleDensity a b θ z)) :=
    (measurable_universalCanonicalWeightedTripleDensity a b θ).ennreal_ofReal
  have hae :
      F =ᵐ[
        ((volume : Measure (ℝ × ℝ × ℝ)).restrict
            universalCanonicalPositiveTarget).withDensity
          (fun z =>
            ENNReal.ofReal
              (universalCanonicalWeightedTripleDensity a b θ z))]
        universalCanonicalToReducedObservationNested := by
    change
      ∀ᵐ z
        ∂((volume : Measure (ℝ × ℝ × ℝ)).restrict
            universalCanonicalPositiveTarget).withDensity
          (fun z =>
            ENNReal.ofReal
              (universalCanonicalWeightedTripleDensity a b θ z)),
        F z = universalCanonicalToReducedObservationNested z
    rw [ae_withDensity_iff hcanonical]
    filter_upwards
      [self_mem_ae_restrict
        measurableSet_universalCanonicalPositiveTarget] with z hz _hden
    exact hF z hz
  rw [Measure.map_congr hae]
  exact map_canonicalWeightedTripleDensity_eq_reducedDensity ha hb θ

end

end GraybillDeal
