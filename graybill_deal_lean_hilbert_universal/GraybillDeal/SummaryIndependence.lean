import GraybillDeal.CanonicalSummary

/-!
# Independence adapter for raw normal summaries

The canonical estimator theorem asks for three independence statements:

* `P` is independent of `(L,V)`;
* `V` is independent of `L`;
* the centered oracle error is independent of `(D,P,L)`.

For a raw Gaussian proof it is cleaner to establish a single mutual
independence statement for the four scalar summaries

`centered, D, P, L`.

This file proves that the latter implies all three former statements.  It
also packages the resulting call to the estimator-level theorem.
-/

namespace GraybillDeal

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem measurable_summaryFamily4
    {centered D P L : Ω → ℝ}
    (hcentered : Measurable centered) (hD : Measurable D)
    (hP : Measurable P) (hL : Measurable L) :
    ∀ i, Measurable (![centered, D, P, L] i) := by
  intro i
  fin_cases i <;> simp_all

/--
Mutual independence of `(centered,D,P,L)` makes `P` independent of the
pair consisting of `L` and the standardized squared mean difference.
-/
theorem indepFun_p_l_standardizedDifference13_of_iIndepFun_summary4
    (varianceSum : ℝ) (centered D P L : Ω → ℝ) (Pmeasure : Measure Ω)
    (hcentered : Measurable centered) (hD : Measurable D)
    (hP : Measurable P) (hL : Measurable L)
    (hsummary : iIndepFun ![centered, D, P, L] Pmeasure) :
    IndepFun P
      (fun ω => (L ω, standardizedDifference13 varianceSum (D ω))) Pmeasure := by
  have hmeas :=
    measurable_summaryFamily4 hcentered hD hP hL
  have hpair :
      IndepFun (fun ω => (L ω, D ω)) P Pmeasure :=
    hsummary.indepFun_prodMk hmeas
      (3 : Fin 4) (1 : Fin 4) (2 : Fin 4) (by decide) (by decide)
  have hout := hpair.symm.comp measurable_id
    (show Measurable
        (fun z : ℝ × ℝ =>
          (z.1, standardizedDifference13 varianceSum z.2)) by
      unfold standardizedDifference13
      fun_prop)
  simpa [Function.comp_def] using hout

/--
Mutual independence of the four raw summaries makes the standardized
squared mean difference independent of the residual sum coordinate.
-/
theorem indepFun_standardizedDifference13_l_of_iIndepFun_summary4
    (varianceSum : ℝ) (centered D P L : Ω → ℝ) (Pmeasure : Measure Ω)
    (hcentered : Measurable centered) (hD : Measurable D)
    (hP : Measurable P) (hL : Measurable L)
    (hsummary : iIndepFun ![centered, D, P, L] Pmeasure) :
    IndepFun
      (fun ω => standardizedDifference13 varianceSum (D ω)) L Pmeasure := by
  have hmeas :=
    measurable_summaryFamily4 hcentered hD hP hL
  have hDL : IndepFun D L Pmeasure :=
    hsummary.indepFun (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hout := hDL.comp
    (show Measurable
        (fun d : ℝ => standardizedDifference13 varianceSum d) by
      unfold standardizedDifference13
      fun_prop)
    measurable_id
  simpa [Function.comp_def] using hout

/--
Mutual independence of `(centered,D,P,L)` gives exactly the nested
independence statement used to eliminate the centered cross terms.
-/
theorem indepFun_centered_d_p_l_of_iIndepFun_summary4
    (centered D P L : Ω → ℝ) (Pmeasure : Measure Ω)
    (hcentered : Measurable centered) (hD : Measurable D)
    (hP : Measurable P) (hL : Measurable L)
    (hsummary : iIndepFun ![centered, D, P, L] Pmeasure) :
    IndepFun centered (fun ω => (D ω, (P ω, L ω))) Pmeasure := by
  classical
  have hmeas :=
    measurable_summaryFamily4 hcentered hD hP hL
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

/--
Estimator-level probability bridge with one four-way summary-independence
hypothesis in place of the three independence hypotheses of
`canonicalClippedEstimatorRiskDifference13_neg_of_summary_laws`.

This is the intended target for the raw normal mean/residual decomposition.
-/
theorem canonicalClippedEstimatorRiskDifference13_neg_of_summary_laws_iIndep
    (μ varianceSum s : ℝ) (centered D P L : Ω → ℝ) (Pmeasure : Measure Ω)
    (hvarianceSum : 0 < varianceSum) (hs : |s| < 1)
    (hPmeas : Measurable P) (hLmeas : Measurable L)
    (hDmeas : Measurable D) (hcentered_meas : Measurable centered)
    (hP :
      HasLaw P (betaMeasure 6 6) Pmeasure)
    (hL :
      HasLaw L (gammaMeasure 12 (1 / 2)) Pmeasure)
    (hV :
      HasLaw
        (fun ω => standardizedDifference13 varianceSum (D ω))
        (gammaMeasure (1 / 2) (1 / 2)) Pmeasure)
    (hsummary : iIndepFun ![centered, D, P, L] Pmeasure)
    (hcentered_sq : Integrable (fun ω => (centered ω) ^ 2) Pmeasure)
    (hcentered_zero : (∫ ω, centered ω ∂Pmeasure) = 0) :
    sqRisk μ
        (fun ω =>
          μ + centered ω + D ω
            * (canonicalClippedWeight13 epsilon13 s (P ω) (L ω)
                (standardizedDifference13 varianceSum (D ω))
              - canonicalTheta s)) Pmeasure
      <
    sqRisk μ
        (fun ω =>
          μ + centered ω
            + D ω * (canonicalR s (P ω) - canonicalTheta s)) Pmeasure := by
  exact canonicalClippedEstimatorRiskDifference13_neg_of_summary_laws
    μ varianceSum s centered D P L Pmeasure hvarianceSum hs
    hPmeas hLmeas hDmeas hcentered_meas hP hL hV
    (indepFun_p_l_standardizedDifference13_of_iIndepFun_summary4
      varianceSum centered D P L Pmeasure
      hcentered_meas hDmeas hPmeas hLmeas hsummary)
    (indepFun_standardizedDifference13_l_of_iIndepFun_summary4
      varianceSum centered D P L Pmeasure
      hcentered_meas hDmeas hPmeas hLmeas hsummary)
    (indepFun_centered_d_p_l_of_iIndepFun_summary4
      centered D P L Pmeasure
      hcentered_meas hDmeas hPmeas hLmeas hsummary)
    hcentered_sq hcentered_zero

end

end GraybillDeal
