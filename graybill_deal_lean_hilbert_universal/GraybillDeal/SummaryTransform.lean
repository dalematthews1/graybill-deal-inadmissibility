import GraybillDeal.BetaGamma
import Mathlib.Probability.Independence.InfinitePi

/-!
# Transporting summary independence through the beta--gamma transform

Suppose the centered oracle error, the mean difference, and the two scaled
residual sums of squares are mutually independent.  The last two coordinates
may be replaced by their beta--gamma ratio and sum.  The beta--gamma law says
that the two new coordinates are independent of one another; independence of
the residual block from the Gaussian block says that this replacement
preserves independence across the two blocks.

This file packages that argument as a four-way `iIndepFun` theorem.  It is the
independence-transport step needed between the raw Gaussian decomposition and
the estimator-level summary bridge.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/--
Two independent measurable random variables form a mutually independent
family indexed by `Fin 2`.
-/
private theorem iIndepFun_finTwo_of_indepFun
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

/-- The four raw summaries before the beta--gamma ratio/sum transform. -/
private def rawSummary4
    (centered D U₁ U₂ : Ω → ℝ) : Fin 4 → Ω → ℝ :=
  ![centered, D, U₁, U₂]

/-- The four summaries after the beta--gamma ratio/sum transform. -/
def transformedSummary4
    (centered D U₁ U₂ : Ω → ℝ) : Fin 4 → Ω → ℝ :=
  ![centered, D,
    (fun ω => U₁ ω / (U₁ ω + U₂ ω)),
    (fun ω => U₁ ω + U₂ ω)]

/--
The block-form independence adapter used by the raw-normal bridge.

It is enough to know independence inside the Gaussian pair, independence
inside the residual pair, and independence of the two pairs.  This is the
natural output of the Gaussian mean/residual decomposition and avoids first
having to synthesize a raw four-way `iIndepFun` statement.

Besides the transformed four-way independence statement, the theorem returns
the component laws because those are needed by the canonical risk bridge.
-/
theorem betaGamma_laws_and_iIndepFun_transformedSummary4_of_blocks
    (centered D U₁ U₂ : Ω → ℝ) (Pmeasure : Measure Ω)
    [IsFiniteMeasure Pmeasure]
    (hcentered : Measurable centered) (hD : Measurable D)
    (hU₁meas : Measurable U₁) (hU₂meas : Measurable U₂)
    (hU₁ : HasLaw U₁ (gammaMeasure 6 (1 / 2)) Pmeasure)
    (hU₂ : HasLaw U₂ (gammaMeasure 6 (1 / 2)) Pmeasure)
    (hCD : IndepFun centered D Pmeasure)
    (hU₁U₂ : IndepFun U₁ U₂ Pmeasure)
    (hblocks :
      IndepFun
        (fun ω => (centered ω, D ω))
        (fun ω => (U₁ ω, U₂ ω)) Pmeasure) :
    HasLaw
        (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure 6 6) Pmeasure
      ∧
    HasLaw
        (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure 12 (1 / 2)) Pmeasure
      ∧
    iIndepFun (transformedSummary4 centered D U₁ U₂) Pmeasure := by
  let P : Ω → ℝ := fun ω => U₁ ω / (U₁ ω + U₂ ω)
  let L : Ω → ℝ := fun ω => U₁ ω + U₂ ω
  obtain ⟨hP, hL, hPL⟩ :=
    betaGamma_component_laws_and_indep U₁ U₂ Pmeasure hU₁ hU₂ hU₁U₂
  letI : IsProbabilityMeasure (gammaMeasure 6 (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
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
    have hout :=
      iIndepFun_finTwo_of_indepFun
        (show Measurable (fun ω => ![centered ω, D ω]) by fun_prop)
        (show Measurable (fun ω => ![P ω, L ω]) by fun_prop)
        hblocks'
    exact hout
  have hwithin : ∀ i, iIndepFun (blocks i) Pmeasure := by
    intro i
    fin_cases i
    · simpa [blocks] using
        iIndepFun_finTwo_of_indepFun hcentered hD hCD
    · simpa [blocks] using
        iIndepFun_finTwo_of_indepFun hPmeas hLmeas hPL
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
      iIndepFun (transformedSummary4 centered D U₁ U₂) Pmeasure := by
    apply iIndepFun.of_precomp
      (g := finProdFinEquiv (m := 2) (n := 2))
      finProdFinEquiv.surjective
    apply hflat.congr
    intro p
    filter_upwards [] with ω
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [blocks, transformedSummary4, P, L, finProdFinEquiv]
  exact ⟨by simpa [P] using hP, by simpa [L] using hL, htransformed⟩

/--
The same independence transport stated from a single raw four-way mutual
independence hypothesis.
-/
theorem betaGamma_laws_and_iIndepFun_transformedSummary4
    (centered D U₁ U₂ : Ω → ℝ) (Pmeasure : Measure Ω)
    [IsFiniteMeasure Pmeasure]
    (hcentered : Measurable centered) (hD : Measurable D)
    (hU₁meas : Measurable U₁) (hU₂meas : Measurable U₂)
    (hU₁ : HasLaw U₁ (gammaMeasure 6 (1 / 2)) Pmeasure)
    (hU₂ : HasLaw U₂ (gammaMeasure 6 (1 / 2)) Pmeasure)
    (hraw : iIndepFun (rawSummary4 centered D U₁ U₂) Pmeasure) :
    HasLaw
        (fun ω => U₁ ω / (U₁ ω + U₂ ω))
        (betaMeasure 6 6) Pmeasure
      ∧
    HasLaw
        (fun ω => U₁ ω + U₂ ω)
        (gammaMeasure 12 (1 / 2)) Pmeasure
      ∧
    iIndepFun (transformedSummary4 centered D U₁ U₂) Pmeasure := by
  have hrawMeas :
      ∀ i, Measurable (rawSummary4 centered D U₁ U₂ i) := by
    intro i
    fin_cases i <;> simp_all [rawSummary4]
  have hCD : IndepFun centered D Pmeasure := by
    simpa [rawSummary4] using
      hraw.indepFun (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  have hU₁U₂ : IndepFun U₁ U₂ Pmeasure := by
    simpa [rawSummary4] using
      hraw.indepFun (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hblocks :
      IndepFun
        (fun ω => (centered ω, D ω))
        (fun ω => (U₁ ω, U₂ ω)) Pmeasure := by
    simpa [rawSummary4] using
      hraw.indepFun_prodMk_prodMk hrawMeas
        (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
        (by decide) (by decide) (by decide) (by decide)
  exact
    betaGamma_laws_and_iIndepFun_transformedSummary4_of_blocks
      centered D U₁ U₂ Pmeasure
      hcentered hD hU₁meas hU₂meas hU₁ hU₂ hCD hU₁U₂ hblocks

end

end GraybillDeal
