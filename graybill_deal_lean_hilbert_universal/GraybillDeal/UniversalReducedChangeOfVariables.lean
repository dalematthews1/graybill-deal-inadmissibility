import GraybillDeal.UniversalReducedDensity
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The three-coordinate universal reduced change of variables

This file isolates the deterministic coordinate map which remains between
the independent canonical variables and the universal reduced density.

For positive canonical coordinates `(g₁,g₂,w)`, put

```
t = g₁ + g₂,   r = g₁ / t,   q = w / t.
```

The inverse map is

```
(r,q,t) ↦ (r*t, (1-r)*t, q*t).
```

It is an open partial homeomorphism from
`(0,1) × (0,∞) × (0,∞)` to `(0,∞)^3`.  Keeping the radial coordinate
`t` in this file is useful: the final reduced law is obtained by integrating
it out, and the inverse Jacobian is `t²`.
-/

namespace GraybillDeal

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Add the positive radial coordinate to the reduced observation.  The
coordinate order is `(r,q,t)`. -/
abbrev UniversalReducedRadialCoordinates := ℝ × ℝ × ℝ

/-- Canonical positive coordinates `(g₁,g₂,w)`. -/
abbrev UniversalCanonicalCoordinates := ℝ × ℝ × ℝ

/-- The open support of `(r,q,t)`. -/
def universalReducedRadialSource : Set UniversalReducedRadialCoordinates :=
  Ioo (0 : ℝ) 1 ×ˢ (Ioi 0 ×ˢ Ioi 0)

/-- The open support of `(g₁,g₂,w)`. -/
def universalCanonicalPositiveTarget : Set UniversalCanonicalCoordinates :=
  Ioi (0 : ℝ) ×ˢ (Ioi 0 ×ˢ Ioi 0)

/-- The inverse-coordinate map `(r,q,t) ↦ (rt,(1-r)t,qt)`. -/
def universalReducedRadialToCanonical
    (z : UniversalReducedRadialCoordinates) :
    UniversalCanonicalCoordinates :=
  (z.1 * z.2.2, ((1 - z.1) * z.2.2, z.2.1 * z.2.2))

/-- The forward-coordinate map
`(g₁,g₂,w) ↦ (g₁/(g₁+g₂), w/(g₁+g₂), g₁+g₂)`. -/
def universalCanonicalToReducedRadial
    (z : UniversalCanonicalCoordinates) :
    UniversalReducedRadialCoordinates :=
  (z.1 / (z.1 + z.2.1),
    (z.2.2 / (z.1 + z.2.1), z.1 + z.2.1))

@[measurability, fun_prop]
theorem measurable_universalReducedRadialToCanonical :
    Measurable universalReducedRadialToCanonical := by
  unfold universalReducedRadialToCanonical
  fun_prop

@[measurability, fun_prop]
theorem measurable_universalCanonicalToReducedRadial :
    Measurable universalCanonicalToReducedRadial := by
  unfold universalCanonicalToReducedRadial
  fun_prop

/-- The positive three-coordinate transformation as an open partial
homeomorphism. -/
@[simps]
def universalReducedRadialPartialHomeomorph :
    OpenPartialHomeomorph
      UniversalReducedRadialCoordinates UniversalCanonicalCoordinates where
  toFun := universalReducedRadialToCanonical
  invFun := universalCanonicalToReducedRadial
  source := universalReducedRadialSource
  target := universalCanonicalPositiveTarget
  map_target' := by
    rintro ⟨g₁, g₂, w⟩ ⟨hg₁, hg₂, hw⟩
    dsimp at hg₁ hg₂ hw
    change 0 < g₁ at hg₁
    change 0 < g₂ at hg₂
    change 0 < w at hw
    change
      (0 < g₁ / (g₁ + g₂) ∧ g₁ / (g₁ + g₂) < 1) ∧
        0 < w / (g₁ + g₂) ∧ 0 < g₁ + g₂
    have hsum : 0 < g₁ + g₂ := add_pos hg₁ hg₂
    exact
      ⟨⟨div_pos hg₁ hsum,
          (div_lt_one hsum).2 (by linarith [hg₂])⟩,
        div_pos hw hsum, hsum⟩
  map_source' := by
    rintro ⟨r, q, t⟩ ⟨hr, hq, ht⟩
    change
      0 < r * t ∧ 0 < (1 - r) * t ∧ 0 < q * t
    exact
      ⟨mul_pos hr.1 ht,
        mul_pos (sub_pos.mpr hr.2) ht,
        mul_pos hq ht⟩
  right_inv' := by
    rintro ⟨g₁, g₂, w⟩ ⟨hg₁, hg₂, hw⟩
    have hsum : g₁ + g₂ ≠ 0 := (add_pos hg₁ hg₂).ne'
    apply Prod.ext
    · simp only [universalCanonicalToReducedRadial,
        universalReducedRadialToCanonical]
      field_simp
    · apply Prod.ext
      · simp only [universalCanonicalToReducedRadial,
          universalReducedRadialToCanonical]
        field_simp
        ring
      · simp only [universalCanonicalToReducedRadial,
          universalReducedRadialToCanonical]
        field_simp
  left_inv' := by
    rintro ⟨r, q, t⟩ ⟨hr, hq, ht⟩
    have ht0 : t ≠ 0 := ht.ne'
    apply Prod.ext
    · simp only [universalReducedRadialToCanonical,
        universalCanonicalToReducedRadial]
      field_simp
      ring
    · apply Prod.ext
      · simp only [universalReducedRadialToCanonical,
          universalCanonicalToReducedRadial]
        field_simp
        ring
      · simp only [universalReducedRadialToCanonical,
          universalCanonicalToReducedRadial]
        ring
  open_source := isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioi)
  open_target := isOpen_Ioi.prod (isOpen_Ioi.prod isOpen_Ioi)
  continuousOn_toFun := by
    unfold universalReducedRadialToCanonical
    fun_prop
  continuousOn_invFun := by
    rintro ⟨g₁, g₂, w⟩ ⟨hg₁, hg₂, hw⟩
    have hsum : g₁ + g₂ ≠ 0 := (add_pos hg₁ hg₂).ne'
    unfold universalCanonicalToReducedRadial
    fun_prop

theorem universalReducedRadialToCanonical_apply
    (r q t : ℝ) :
    universalReducedRadialToCanonical (r, q, t)
      =
    universalReducedInverseCoordinates r q t := by
  rfl

theorem universalCanonicalToReducedRadial_toFun
    {r q t : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hq : 0 < q) (ht : 0 < t) :
    universalCanonicalToReducedRadial
        (universalReducedRadialToCanonical (r, q, t))
      =
    (r, q, t) := by
  exact universalReducedRadialPartialHomeomorph.left_inv
    ⟨⟨hr0, hr1⟩, hq, ht⟩

theorem universalReducedRadialToCanonical_image :
    universalReducedRadialToCanonical ''
        universalReducedRadialSource
      =
    universalCanonicalPositiveTarget := by
  simpa [universalReducedRadialPartialHomeomorph] using
    universalReducedRadialPartialHomeomorph.image_source_eq_target

/-! ## Differential and Jacobian -/

/-- The concrete linear equivalence which orders a right-associated triple
as the vector `(x₀,x₁,x₂)`. -/
def universalTripleLinearEquiv :
    (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun z := ![z.1, z.2.1, z.2.2]
  invFun x := (x 0, x 1, x 2)
  left_inv z := by
    ext <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' c x := by
    funext i
    fin_cases i <;> simp

/-- Continuous form of `universalTripleLinearEquiv`. -/
def universalTripleContinuousLinearEquiv :
    (ℝ × ℝ × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  universalTripleLinearEquiv.toContinuousLinearEquiv

/-- The Jacobian matrix of `(r,q,t) ↦ (rt,(1-r)t,qt)`. -/
def universalReducedRadialJacobianMatrix
    (z : UniversalReducedRadialCoordinates) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![z.2.2, 0, z.1;
     -z.2.2, 0, 1 - z.1;
     0, z.2.2, z.2.1]

/-- The derivative of `(r,q,t) ↦ (rt,(1-r)t,qt)`, defined by conjugating
its explicit matrix through the ordered-triple equivalence. -/
def universalReducedRadialToCanonicalFDeriv
    (z : UniversalReducedRadialCoordinates) :
    UniversalReducedRadialCoordinates →L[ℝ]
      UniversalCanonicalCoordinates :=
  LinearMap.toContinuousLinearMap
    (universalTripleLinearEquiv.symm.toLinearMap ∘ₗ
      Matrix.toLin' (universalReducedRadialJacobianMatrix z) ∘ₗ
        universalTripleLinearEquiv.toLinearMap)

@[simp]
theorem universalReducedRadialToCanonicalFDeriv_apply
    (z h : UniversalReducedRadialCoordinates) :
    universalReducedRadialToCanonicalFDeriv z h
      =
    (z.2.2 * h.1 + z.1 * h.2.2,
      (-z.2.2 * h.1 + (1 - z.1) * h.2.2,
        z.2.2 * h.2.1 + z.2.1 * h.2.2)) := by
  apply universalTripleContinuousLinearEquiv.injective
  funext i
  fin_cases i <;>
    simp [universalReducedRadialToCanonicalFDeriv,
      universalTripleContinuousLinearEquiv,
      universalTripleLinearEquiv,
      universalReducedRadialJacobianMatrix,
      Matrix.toLin'_apply, Matrix.mulVec]

theorem hasFDerivAt_universalReducedRadialToCanonical
    (z : ℝ × (ℝ × ℝ)) :
    HasFDerivAt
      (fun y : ℝ × (ℝ × ℝ) =>
        (y.1 * y.2.2, ((1 - y.1) * y.2.2, y.2.1 * y.2.2)))
      (universalReducedRadialToCanonicalFDeriv z) z := by
  let dr : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  let dq : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  let dt : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hdr : HasFDerivAt
      (fun y : ℝ × (ℝ × ℝ) => y.1) dr z := by
    exact hasFDerivAt_fst
  have hdq : HasFDerivAt
      (fun y : ℝ × (ℝ × ℝ) => y.2.1) dq z := by
    fun_prop
  have hdt : HasFDerivAt
      (fun y : ℝ × (ℝ × ℝ) => y.2.2) dt z := by
    fun_prop
  have hfirst := hdr.mul hdt
  have hsecond :=
    ((hasFDerivAt_const (x := z) (c := (1 : ℝ))).sub hdr).mul hdt
  have hthird := hdq.mul hdt
  have hprod := hfirst.prodMk (hsecond.prodMk hthird)
  have hmanual :
      HasFDerivAt
        (fun y : ℝ × (ℝ × ℝ) =>
          (y.1 * y.2.2, ((1 - y.1) * y.2.2, y.2.1 * y.2.2)))
        ((z.1 • dt + z.2.2 • dr).prod
          (((1 - z.1) • dt + z.2.2 • (0 - dr)).prod
            (z.2.1 • dt + z.2.2 • dq))) z := by
    simpa only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply] using hprod
  apply hmanual.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  rw [universalReducedRadialToCanonicalFDeriv_apply]
  simp [dr, dq, dt]
  constructor
  · ring
  constructor <;> ring

/-- The oriented inverse-coordinate Jacobian is `-t²`. -/
theorem det_universalReducedRadialToCanonicalFDeriv
    (z : UniversalReducedRadialCoordinates) :
    (universalReducedRadialToCanonicalFDeriv z).det = -(z.2.2 ^ 2) := by
  change LinearMap.det
      (universalReducedRadialToCanonicalFDeriv z).toLinearMap
    = -(z.2.2 ^ 2)
  rw [show
    (universalReducedRadialToCanonicalFDeriv z).toLinearMap
      =
    universalTripleLinearEquiv.symm.toLinearMap ∘ₗ
      Matrix.toLin' (universalReducedRadialJacobianMatrix z) ∘ₗ
        universalTripleLinearEquiv.toLinearMap by
      rfl]
  have hconj :=
    LinearMap.det_conj
      (Matrix.toLin' (universalReducedRadialJacobianMatrix z))
      universalTripleLinearEquiv.symm
  rw [show
      LinearMap.det
          (universalTripleLinearEquiv.symm.toLinearMap ∘ₗ
            Matrix.toLin' (universalReducedRadialJacobianMatrix z) ∘ₗ
              universalTripleLinearEquiv.toLinearMap)
        =
      LinearMap.det
        (Matrix.toLin' (universalReducedRadialJacobianMatrix z)) by
      simpa using hconj]
  rw [← LinearMap.det_toMatrix' (Matrix.toLin'
    (universalReducedRadialJacobianMatrix z))]
  rw [LinearMap.toMatrix'_toLin']
  rw [Matrix.det_fin_three]
  simp [universalReducedRadialJacobianMatrix]
  ring

/-- The absolute inverse-coordinate Jacobian is `t²` on `t > 0`. -/
theorem abs_det_universalReducedRadialToCanonicalFDeriv
    (z : UniversalReducedRadialCoordinates) :
    |(universalReducedRadialToCanonicalFDeriv z).det| = z.2.2 ^ 2 := by
  rw [det_universalReducedRadialToCanonicalFDeriv]
  rw [abs_neg, abs_of_nonneg (sq_nonneg _)]

/-!
The Jacobian theorem is most convenient on the Euclidean coordinate model
`Fin 3 → ℝ`: unlike an iterated product, this type has a canonical
finite-dimensional Haar volume with no topology-instance diamond.  The
following definitions are exactly the conjugates of the preceding ones.
-/

-- Force the norm-induced Euclidean topology on the finite function space.
-- Without this local choice, Lean can select the pointwise product topology
-- in some derivative goals and the norm topology in the Haar-volume goal.
@[reducible] local instance universalFinThreeNormTopology :
    TopologicalSpace (Fin 3 → ℝ) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Euclidean-vector form of the inverse-coordinate map. -/
def universalReducedRadialToCanonicalVec (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  universalTripleContinuousLinearEquiv
    (universalReducedRadialToCanonical
      (universalTripleContinuousLinearEquiv.symm x))

/-- Euclidean-vector source support. -/
def universalReducedRadialSourceVec : Set (Fin 3 → ℝ) :=
  universalTripleContinuousLinearEquiv '' universalReducedRadialSource

/-- Euclidean-vector target support. -/
def universalCanonicalPositiveTargetVec : Set (Fin 3 → ℝ) :=
  universalTripleContinuousLinearEquiv '' universalCanonicalPositiveTarget

theorem isOpen_universalReducedRadialSourceVec :
    IsOpen universalReducedRadialSourceVec := by
  exact universalTripleContinuousLinearEquiv.toHomeomorph.isOpenMap _
    (isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioi))

theorem measurableSet_universalReducedRadialSourceVec :
    MeasurableSet universalReducedRadialSourceVec :=
  isOpen_universalReducedRadialSourceVec.measurableSet

theorem universalReducedRadialToCanonicalVec_image :
    universalReducedRadialToCanonicalVec ''
        universalReducedRadialSourceVec
      =
    universalCanonicalPositiveTargetVec := by
  ext y
  constructor
  · rintro ⟨x, ⟨x', hx', rfl⟩, rfl⟩
    have htarget :
        universalReducedRadialToCanonical x'
          ∈ universalCanonicalPositiveTarget := by
      rw [← universalReducedRadialToCanonical_image]
      exact ⟨x', hx', rfl⟩
    refine ⟨universalReducedRadialToCanonical x', htarget, ?_⟩
    simp [universalReducedRadialToCanonicalVec]
  · rintro ⟨y', hy', rfl⟩
    rw [← universalReducedRadialToCanonical_image] at hy'
    rcases hy' with ⟨x', hx', hxy'⟩
    refine
      ⟨universalTripleContinuousLinearEquiv x',
        ⟨x', hx', rfl⟩, ?_⟩
    simp [universalReducedRadialToCanonicalVec, hxy']

theorem universalReducedRadialToCanonicalVec_injOn :
    Set.InjOn universalReducedRadialToCanonicalVec
      universalReducedRadialSourceVec := by
  intro x hx y hy hxy
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  have hF :
      universalReducedRadialToCanonical x'
        = universalReducedRadialToCanonical y' := by
    apply universalTripleContinuousLinearEquiv.injective
    simpa [universalReducedRadialToCanonicalVec] using hxy
  have hxy' :=
    universalReducedRadialPartialHomeomorph.injOn hx' hy' hF
  exact congrArg universalTripleContinuousLinearEquiv hxy'

/-- Derivative of the Euclidean-vector coordinate map. -/
def universalReducedRadialToCanonicalVecFDeriv (x : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  universalTripleContinuousLinearEquiv.toContinuousLinearMap.comp
    ((universalReducedRadialToCanonicalFDeriv
      (universalTripleContinuousLinearEquiv.symm x)).comp
        universalTripleContinuousLinearEquiv.symm.toContinuousLinearMap)

theorem hasFDerivAt_universalReducedRadialToCanonicalVec
    (x : Fin 3 → ℝ) :
    @HasFDerivAt ℝ _ (Fin 3 → ℝ)
      Pi.normedAddCommGroup.toAddCommGroup
      Pi.normedSpace.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (Fin 3 → ℝ)
      Pi.normedAddCommGroup.toAddCommGroup
      Pi.normedSpace.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      universalReducedRadialToCanonicalVec
      (universalReducedRadialToCanonicalVecFDeriv x) x := by
  have h₁ :=
    universalTripleContinuousLinearEquiv.symm.hasFDerivAt (x := x)
  have h₂ :=
    hasFDerivAt_universalReducedRadialToCanonical
      (universalTripleContinuousLinearEquiv.symm x)
  have h₃ := h₂.comp x h₁
  have h₄ :=
    universalTripleContinuousLinearEquiv.hasFDerivAt.comp x h₃
  simpa [universalReducedRadialToCanonicalVec,
    universalReducedRadialToCanonical,
    universalReducedRadialToCanonicalVecFDeriv,
    Function.comp_apply] using h₄

theorem abs_det_universalReducedRadialToCanonicalVecFDeriv
    (x : Fin 3 → ℝ) :
    |(universalReducedRadialToCanonicalVecFDeriv x).det|
      =
    (universalTripleContinuousLinearEquiv.symm x).2.2 ^ 2 := by
  change
    |LinearMap.det
      (universalReducedRadialToCanonicalVecFDeriv x).toLinearMap|
      =
    (universalTripleContinuousLinearEquiv.symm x).2.2 ^ 2
  have hconj :=
    LinearMap.det_conj
      (universalReducedRadialToCanonicalFDeriv
        (universalTripleContinuousLinearEquiv.symm x)).toLinearMap
      universalTripleLinearEquiv
  rw [show
      LinearMap.det
          (universalReducedRadialToCanonicalVecFDeriv x).toLinearMap
        =
      LinearMap.det
        (universalReducedRadialToCanonicalFDeriv
          (universalTripleContinuousLinearEquiv.symm x)).toLinearMap by
      simpa [universalReducedRadialToCanonicalVecFDeriv,
        universalTripleContinuousLinearEquiv] using hconj]
  exact abs_det_universalReducedRadialToCanonicalFDeriv _

/-- The complete three-dimensional Jacobian change of variables, stated
on the canonical Euclidean coordinate model. -/
theorem lintegral_universalReducedRadialToCanonicalVec
    (g : (Fin 3 → ℝ) → ℝ≥0∞) :
    (∫⁻ z in universalCanonicalPositiveTargetVec, g z)
      =
    ∫⁻ z in universalReducedRadialSourceVec,
      ENNReal.ofReal
          ((universalTripleContinuousLinearEquiv.symm z).2.2 ^ 2)
        * g (universalReducedRadialToCanonicalVec z) := by
  have h :=
    lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (μ := volume)
      (f := universalReducedRadialToCanonicalVec)
      (f' := universalReducedRadialToCanonicalVecFDeriv)
      measurableSet_universalReducedRadialSourceVec
      (fun z _ =>
        (hasFDerivAt_universalReducedRadialToCanonicalVec z)
          |>.hasFDerivWithinAt)
      universalReducedRadialToCanonicalVec_injOn g
  rw [universalReducedRadialToCanonicalVec_image] at h
  calc
    (∫⁻ z in universalCanonicalPositiveTargetVec, g z)
        =
      ∫⁻ z in universalReducedRadialSourceVec,
        ENNReal.ofReal
            |(universalReducedRadialToCanonicalVecFDeriv z).det|
          * g (universalReducedRadialToCanonicalVec z) := h
    _ =
      ∫⁻ z in universalReducedRadialSourceVec,
        ENNReal.ofReal
            ((universalTripleContinuousLinearEquiv.symm z).2.2 ^ 2)
          * g (universalReducedRadialToCanonicalVec z) := by
      apply setLIntegral_congr_fun
        measurableSet_universalReducedRadialSourceVec
      intro z _
      dsimp only
      rw [abs_det_universalReducedRadialToCanonicalVecFDeriv]

end

end GraybillDeal
