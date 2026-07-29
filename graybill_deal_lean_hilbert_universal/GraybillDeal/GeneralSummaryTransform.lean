import GraybillDeal.GeneralBetaGamma
import Mathlib.Probability.Independence.InfinitePi

/-!
# Generic transport of summary independence through the beta--gamma transform

For residual degrees of freedom `ν`, the standardized residual sums have
law `Gamma(ν / 2, 1 / 2)`.  This file replaces the residual coordinates
`(U₁,U₂)` by their ratio and sum

`P = U₁ / (U₁ + U₂)`, `L = U₁ + U₂`,

and packages both their laws and the four-way independence of
`(centered,D,P,L)`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem iIndepFun_finTwo_of_indepFun_general
    {E : Type*} [MeasurableSpace E]
    {X Y : Ω → E} {Pmeasure : Measure Ω}
    [IsProbabilityMeasure Pmeasure]
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y Pmeasure) :
    iIndepFun (fun i ω => ![X ω, Y ω] i) Pmeasure := by
  let μX : Measure E := Pmeasure.map X
  let μY : Measure E := Pmeasure.map Y
  have hLawX : HasLaw X μX Pmeasure :=
    ⟨hX.aemeasurable, rfl⟩
  have hLawY : HasLaw Y μY Pmeasure :=
    ⟨hY.aemeasurable, rfl⟩
  have hPair :
      HasLaw (fun ω => (X ω, Y ω)) (μX.prod μY) Pmeasure :=
    hXY.hasLaw_prod hLawX hLawY
  have hUnpair :
      HasLaw MeasurableEquiv.finTwoArrow.symm
        (Measure.pi ![μX, μY]) (μX.prod μY) :=
    (measurePreserving_finTwoArrow_vec μX μY).symm.hasLaw
  have hVec :
      HasLaw (fun ω => ![X ω, Y ω])
        (Measure.pi ![μX, μY]) Pmeasure := by
    convert hUnpair.fun_comp hPair using 1
    funext ω i
    fin_cases i <;> rfl
  apply (iIndepFun_iff_hasLaw_pi_pi (P := Pmeasure) ?_).2 hVec
  intro i
  fin_cases i
  · simpa using hLawX
  · simpa using hLawY

/-- The four summaries after the generic beta--gamma ratio/sum transform. -/
def generalTransformedSummary4
    (centered D U₁ U₂ : Ω → ℝ) : Fin 4 → Ω → ℝ :=
  ![centered, D,
    (fun ω => U₁ ω / (U₁ ω + U₂ ω)),
    (fun ω => U₁ ω + U₂ ω)]

/--
The generic block-form beta--gamma independence adapter.

The natural Gaussian decomposition supplies independence within the mean
block, within the residual block, and between the two blocks.  For `ν ≥ 9`
these hypotheses imply the symmetric beta law, the summed gamma law, and
mutual independence of `(centered,D,P,L)`.
-/
theorem betaGamma_laws_and_iIndepFun_generalTransformedSummary4_of_blocks
    (ν : ℕ) (hν : 9 ≤ ν)
    (centered D U₁ U₂ : Ω → ℝ) (Pmeasure : Measure Ω)
    [IsFiniteMeasure Pmeasure]
    (hcentered : Measurable centered) (hD : Measurable D)
    (hU₁meas : Measurable U₁) (hU₂meas : Measurable U₂)
    (hU₁ :
      HasLaw U₁
        (gammaMeasure ((ν : ℝ) / 2) (1 / 2)) Pmeasure)
    (hU₂ :
      HasLaw U₂
        (gammaMeasure ((ν : ℝ) / 2) (1 / 2)) Pmeasure)
    (hCD : IndepFun centered D Pmeasure)
    (hU₁U₂ : IndepFun U₁ U₂ Pmeasure)
    (hblocks :
      IndepFun
        (fun ω => (centered ω, D ω))
        (fun ω => (U₁ ω, U₂ ω)) Pmeasure) :
    HasLaw
        (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure ((ν : ℝ) / 2) ((ν : ℝ) / 2)) Pmeasure
      ∧
    HasLaw
        (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure (ν : ℝ) (1 / 2)) Pmeasure
      ∧
    iIndepFun
      (generalTransformedSummary4 centered D U₁ U₂) Pmeasure := by
  have hshape : 1 < (ν : ℝ) / 2 := by
    have hνR : (9 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
    linarith
  let P : Ω → ℝ := fun ω => U₁ ω / (U₁ ω + U₂ ω)
  let L : Ω → ℝ := fun ω => U₁ ω + U₂ ω
  obtain ⟨hP, hLraw, hPL⟩ :=
    betaGamma_component_laws_and_indep_general
      hshape (by norm_num : (0 : ℝ) < 1 / 2)
      U₁ U₂ Pmeasure hU₁ hU₂ hU₁U₂
  have hL :
      HasLaw L (gammaMeasure (ν : ℝ) (1 / 2)) Pmeasure := by
    convert hLraw using 1 <;> simp [L] <;> ring
  letI : IsProbabilityMeasure
      (gammaMeasure ((ν : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by linarith) (by norm_num)
  haveI : IsProbabilityMeasure Pmeasure := hU₁.isProbabilityMeasure
  have hPmeas : Measurable P := by
    unfold P
    fun_prop
  have hLmeas : Measurable L := by
    unfold L
    fun_prop
  have hblocks' :
      IndepFun
        (fun ω => ![centered ω, D ω])
        (fun ω => ![P ω, L ω]) Pmeasure := by
    have hout := hblocks.comp
      (show Measurable (fun z : ℝ × ℝ => ![z.1, z.2]) by fun_prop)
      (show Measurable
          (fun z : ℝ × ℝ =>
            ![z.1 / (z.1 + z.2), z.1 + z.2]) by fun_prop)
    simpa [Function.comp_def, P, L] using hout
  let blocks : Fin 2 → Fin 2 → Ω → ℝ :=
    fun i j ω => ![![centered ω, D ω], ![P ω, L ω]] i j
  have hblocks_iIndep :
      iIndepFun (fun i ω j => blocks i j ω) Pmeasure := by
    exact
      iIndepFun_finTwo_of_indepFun_general
        (show Measurable (fun ω => ![centered ω, D ω]) by fun_prop)
        (show Measurable (fun ω => ![P ω, L ω]) by fun_prop)
        hblocks'
  have hwithin : ∀ i, iIndepFun (blocks i) Pmeasure := by
    intro i
    fin_cases i
    · simpa [blocks] using
        iIndepFun_finTwo_of_indepFun_general hcentered hD hCD
    · simpa [blocks] using
        iIndepFun_finTwo_of_indepFun_general hPmeas hLmeas hPL
  have hflat :
      iIndepFun
        (fun p : Fin 2 × Fin 2 => fun ω => blocks p.1 p.2 ω) Pmeasure := by
    exact
      (iIndepFun_uncurry
        (fun i j => by
          fin_cases i <;> fin_cases j <;>
            simp_all [blocks])
        hblocks_iIndep hwithin).of_precomp
          (Equiv.sigmaEquivProd (Fin 2) (Fin 2)).surjective
  have htransformed :
      iIndepFun
        (generalTransformedSummary4 centered D U₁ U₂) Pmeasure := by
    apply iIndepFun.of_precomp
      (g := finProdFinEquiv (m := 2) (n := 2))
      finProdFinEquiv.surjective
    apply hflat.congr
    intro p
    filter_upwards [] with ω
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [blocks, generalTransformedSummary4, P, L, finProdFinEquiv]
  exact
    ⟨by simpa [P] using hP,
      by simpa [L] using hL,
      htransformed⟩

end

end GraybillDeal
