import GraybillDeal

/-!
Non-vacuity witness for the general model: for every ν, the hypotheses of
`rawGraybillDealEstimatorN_strictly_dominated` are satisfiable on the
canonical product space `(Fin 2 × Fin (ν+1)) → ℝ`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

abbrev ModelOmegaN (ν : ℕ) : Type := (Fin 2 × Fin (ν + 1)) → ℝ

noncomputable def modelPN (ν : ℕ) (μ : ℝ) (variance : Fin 2 → NNReal) :
    Measure (ModelOmegaN ν) :=
  Measure.pi fun gi : Fin 2 × Fin (ν + 1) => gaussianReal μ (variance gi.1)

def modelXN (ν : ℕ) (g : Fin 2) (i : Fin (ν + 1)) : ModelOmegaN ν → ℝ :=
  fun ω => ω (g, i)

theorem modelWitnessN (ν : ℕ) (μ : ℝ) (variance : Fin 2 → NNReal) :
    GraybillDeal.TwoNormalSamplesN ν (modelXN ν) (modelPN ν μ variance)
      μ variance where
  law g i :=
    { aemeasurable := (measurable_pi_apply (g, i)).aemeasurable
      map_eq := (measurePreserving_eval _ (g, i)).map_eq }
  indep := by
    exact iIndepFun_pi
      (μ := fun gi : Fin 2 × Fin (ν + 1) => gaussianReal μ (variance gi.1))
      (X := fun _ => id) (fun _ => aemeasurable_id)

theorem modelXN_measurable (ν : ℕ) : ∀ g i, Measurable (modelXN ν g i) :=
  fun g i => measurable_pi_apply (g, i)

/-- The all-n dominance theorem instantiated at the concrete model:
for every ν ≥ 9 and every parameter point, the clipped perturbation with
the fixed coefficient `generalGraybillDealEpsilon ν` strictly beats the
Graybill--Deal estimator. -/
example (ν : ℕ) (hν : 9 ≤ ν) (μ : ℝ) (variance : Fin 2 → NNReal)
    (h0 : 0 < (variance 0 : ℝ)) (h1 : 0 < (variance 1 : ℝ)) :
    GraybillDeal.sqRisk μ
        (GraybillDeal.rawClippedPerturbedEstimatorN
          (GraybillDeal.generalGraybillDealEpsilon ν) ν (modelXN ν))
        (modelPN ν μ variance)
      <
    GraybillDeal.sqRisk μ
        (GraybillDeal.rawGraybillDealEstimatorN ν (modelXN ν))
        (modelPN ν μ variance) :=
  GraybillDeal.rawClippedPerturbedEstimatorN_sqRisk_lt_rawGraybillDealEstimatorN
    ν hν (modelWitnessN ν μ variance) (modelXN_measurable ν) h0 h1

end
