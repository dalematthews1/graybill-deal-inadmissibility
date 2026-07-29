import GraybillDeal.UnequalBetaGamma
import Mathlib.Probability.Independence.InfinitePi

/-!
# Unequal-shape transport of summary independence

This is the ratio/sum independence adapter needed for two normal samples
with different residual degrees of freedom.  It replaces independent

`U₁ ~ Gamma(a,r)` and `U₂ ~ Gamma(b,r)`

by

`P = U₁/(U₁+U₂)` and `L = U₁+U₂`,

and packages mutual independence of `(centered,D,P,L)`.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem iIndepFun_finTwo_of_indepFun_unequal
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

/-- The four summaries after the unequal-shape beta--gamma transform. -/
def unequalTransformedSummary4
    (centered D U₁ U₂ : Ω → ℝ) : Fin 4 → Ω → ℝ :=
  ![centered, D,
    (fun ω => U₁ ω / (U₁ ω + U₂ ω)),
    (fun ω => U₁ ω + U₂ ω)]

/--
The block-form unequal beta--gamma independence adapter.

The hypotheses separate into independence inside the mean block, inside the
residual block, and between the two blocks.
-/
theorem betaGamma_laws_and_iIndepFun_unequalTransformedSummary4_of_blocks
    {a b r : ℝ} (ha : 1 < a) (hb : 1 < b) (hr : 0 < r)
    (centered D U₁ U₂ : Ω → ℝ) (Pmeasure : Measure Ω)
    [IsFiniteMeasure Pmeasure]
    (hcentered : Measurable centered) (hD : Measurable D)
    (hU₁meas : Measurable U₁) (hU₂meas : Measurable U₂)
    (hU₁ : HasLaw U₁ (gammaMeasure a r) Pmeasure)
    (hU₂ : HasLaw U₂ (gammaMeasure b r) Pmeasure)
    (hCD : IndepFun centered D Pmeasure)
    (hU₁U₂ : IndepFun U₁ U₂ Pmeasure)
    (hblocks :
      IndepFun
        (fun ω => (centered ω, D ω))
        (fun ω => (U₁ ω, U₂ ω)) Pmeasure) :
    HasLaw
        (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure a b) Pmeasure
      ∧
    HasLaw
        (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure (a + b) r) Pmeasure
      ∧
    iIndepFun
      (unequalTransformedSummary4 centered D U₁ U₂) Pmeasure := by
  let P : Ω → ℝ := fun ω => U₁ ω / (U₁ ω + U₂ ω)
  let L : Ω → ℝ := fun ω => U₁ ω + U₂ ω
  obtain ⟨hP, hL, hPL⟩ :=
    betaGamma_component_laws_and_indep_unequal
      ha hb hr U₁ U₂ Pmeasure hU₁ hU₂ hU₁U₂
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha0 hr
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
      iIndepFun_finTwo_of_indepFun_unequal
        (show Measurable (fun ω => ![centered ω, D ω]) by fun_prop)
        (show Measurable (fun ω => ![P ω, L ω]) by fun_prop)
        hblocks'
  have hwithin : ∀ i, iIndepFun (blocks i) Pmeasure := by
    intro i
    fin_cases i
    · simpa [blocks] using
        iIndepFun_finTwo_of_indepFun_unequal hcentered hD hCD
    · simpa [blocks] using
        iIndepFun_finTwo_of_indepFun_unequal hPmeas hLmeas hPL
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
        (unequalTransformedSummary4 centered D U₁ U₂) Pmeasure := by
    apply iIndepFun.of_precomp
      (g := finProdFinEquiv (m := 2) (n := 2))
      finProdFinEquiv.surjective
    apply hflat.congr
    intro p
    filter_upwards [] with ω
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [blocks, unequalTransformedSummary4, P, L, finProdFinEquiv]
  exact
    ⟨by simpa [P] using hP,
      by simpa [L] using hL,
      htransformed⟩

end

end GraybillDeal
