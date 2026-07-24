import GraybillDeal.GeneralCanonical
import Mathlib.Probability.Independence.InfinitePi

/-!
# Generic independence adapters for canonical summaries

Mutual independence of `(centered,D,P,L)` implies the three independence
statements used by the all-sample-size canonical risk decomposition.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem measurable_generalSummaryFamily4
    {centered D P L : Ω → ℝ}
    (hcentered : Measurable centered) (hD : Measurable D)
    (hP : Measurable P) (hL : Measurable L) :
    ∀ i, Measurable (![centered, D, P, L] i) := by
  intro i
  fin_cases i <;> simp_all

/--
Mutual independence of `(centered,D,P,L)` makes `P` independent of
`(L,(ν+1)D²/varianceSum)`.
-/
theorem indepFun_p_l_generalStandardizedDifference_of_iIndepFun_summary4
    (ν varianceSum : ℝ) (centered D P L : Ω → ℝ)
    (Pmeasure : Measure Ω)
    (hcentered : Measurable centered) (hD : Measurable D)
    (hP : Measurable P) (hL : Measurable L)
    (hsummary : iIndepFun ![centered, D, P, L] Pmeasure) :
    IndepFun P
      (fun ω =>
        (L ω, generalStandardizedDifference ν varianceSum (D ω)))
      Pmeasure := by
  have hmeas :=
    measurable_generalSummaryFamily4 hcentered hD hP hL
  have hpair :
      IndepFun (fun ω => (L ω, D ω)) P Pmeasure :=
    hsummary.indepFun_prodMk hmeas
      (3 : Fin 4) (1 : Fin 4) (2 : Fin 4) (by decide) (by decide)
  have hout := hpair.symm.comp measurable_id
    (show Measurable
        (fun z : ℝ × ℝ =>
          (z.1, generalStandardizedDifference ν varianceSum z.2)) by
      unfold generalStandardizedDifference
      fun_prop)
  simpa [Function.comp_def] using hout

/--
Mutual independence of the four summaries makes the standardized squared
mean difference independent of `L`.
-/
theorem indepFun_generalStandardizedDifference_l_of_iIndepFun_summary4
    (ν varianceSum : ℝ) (centered D P L : Ω → ℝ)
    (Pmeasure : Measure Ω)
    (hcentered : Measurable centered) (hD : Measurable D)
    (hP : Measurable P) (hL : Measurable L)
    (hsummary : iIndepFun ![centered, D, P, L] Pmeasure) :
    IndepFun
      (fun ω => generalStandardizedDifference ν varianceSum (D ω))
      L Pmeasure := by
  have hDL : IndepFun D L Pmeasure :=
    hsummary.indepFun (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hout := hDL.comp
    (show Measurable
        (fun d : ℝ => generalStandardizedDifference ν varianceSum d) by
      unfold generalStandardizedDifference
      fun_prop)
    measurable_id
  simpa [Function.comp_def] using hout

/--
Mutual independence of `(centered,D,P,L)` gives the nested independence
statement used to remove the centered cross terms.
-/
theorem indepFun_centered_d_p_l_of_iIndepFun_generalSummary4
    (centered D P L : Ω → ℝ) (Pmeasure : Measure Ω)
    (hcentered : Measurable centered) (hD : Measurable D)
    (hP : Measurable P) (hL : Measurable L)
    (hsummary : iIndepFun ![centered, D, P, L] Pmeasure) :
    IndepFun centered (fun ω => (D ω, (P ω, L ω))) Pmeasure := by
  classical
  have hmeas :=
    measurable_generalSummaryFamily4 hcentered hD hP hL
  let S : Finset (Fin 4) := {0}
  let T : Finset (Fin 4) := {1, 2, 3}
  have hgroups :=
    hsummary.indepFun_finset S T (by simp [S, T]) hmeas
  let i0 : S := ⟨0, by simp [S]⟩
  let i1 : T := ⟨1, by simp [T]⟩
  let i2 : T := ⟨2, by simp [T]⟩
  let i3 : T := ⟨3, by simp [T]⟩
  have hout := hgroups.comp
    (show Measurable (fun v : ∀ _ : S, ℝ => v i0) by fun_prop)
    (show Measurable
        (fun v : ∀ _ : T, ℝ => (v i1, (v i2, v i3))) by fun_prop)
  simpa [Function.comp_def, S, T, i0, i1, i2, i3] using hout

end

end GraybillDeal
