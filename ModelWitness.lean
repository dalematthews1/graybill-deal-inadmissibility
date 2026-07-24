import GraybillDeal

/-!
Non-vacuity witness: the hypotheses of the final theorem are satisfiable.
We realize the two-sample normal model on the canonical product space
`(Fin 2 × Fin 13) → ℝ` with the product of the 26 Gaussian laws.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

abbrev ModelOmega : Type := (Fin 2 × Fin 13) → ℝ

noncomputable def modelP (μ : ℝ) (variance : Fin 2 → NNReal) : Measure ModelOmega :=
  Measure.pi fun gi : Fin 2 × Fin 13 => gaussianReal μ (variance gi.1)

def modelX (g : Fin 2) (i : Fin 13) : ModelOmega → ℝ := fun ω => ω (g, i)

theorem modelWitness (μ : ℝ) (variance : Fin 2 → NNReal) :
    GraybillDeal.TwoNormalSamples13 modelX (modelP μ variance) μ variance where
  law g i :=
    { aemeasurable := (measurable_pi_apply (g, i)).aemeasurable
      map_eq := (measurePreserving_eval _ (g, i)).map_eq }
  indep := by
    exact iIndepFun_pi
      (μ := fun gi : Fin 2 × Fin 13 => gaussianReal μ (variance gi.1))
      (X := fun _ => id) (fun _ => aemeasurable_id)

theorem modelX_measurable : ∀ g i, Measurable (modelX g i) :=
  fun g i => measurable_pi_apply (g, i)

/-- The final dominance theorem instantiated at the concrete model. -/
example (μ : ℝ) (variance : Fin 2 → NNReal)
    (h0 : 0 < (variance 0 : ℝ)) (h1 : 0 < (variance 1 : ℝ)) :
    GraybillDeal.sqRisk μ
        (GraybillDeal.rawClippedPerturbedEstimator13 modelX)
        (modelP μ variance)
      <
    GraybillDeal.sqRisk μ
        (GraybillDeal.rawGraybillDealEstimator13 modelX)
        (modelP μ variance) :=
  GraybillDeal.rawClippedPerturbedEstimator13_sqRisk_lt_rawGraybillDealEstimator13
    (modelWitness μ variance) modelX_measurable h0 h1

end
