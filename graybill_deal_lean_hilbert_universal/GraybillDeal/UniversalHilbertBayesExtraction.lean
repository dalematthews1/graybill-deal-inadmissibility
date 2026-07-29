import GraybillDeal.UniversalHilbertBayesSequence
import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Almost-everywhere extraction from strong `L²` Bayes convergence

Strong convergence in `L²(μ)` implies convergence in measure, and hence
admits an almost-everywhere convergent subsequence.  This file packages that
standard Mathlib route in the exact finite-prior form required by the
complete-class conclusion.

The result is stated for a second measure `ρ ≪ μ`, since the Hilbert
probability measure and the canonical sigma-finite dominating measure have
the same null sets in the universal reduced experiment.
-/

namespace GraybillDeal

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

variable {X Θ : Type*} [MeasurableSpace X]
variable {μ ρ : Measure X}

/-- Strong `L²(μ)` convergence of finite-prior Bayes actions produces an
almost-everywhere finite-Bayes approximation under every `ρ ≪ μ`. -/
theorem hasPositiveFiniteBayesApproximation_of_tendsto_Lp
    {density : Θ → X → ℝ}
    {target : Θ → ℝ}
    {estimator : X → ℝ}
    (hρμ : ρ ≪ μ)
    (f : ℕ → Lp ℝ 2 μ)
    (g : Lp ℝ 2 μ)
    (priors : ℕ → PositiveFinitePrior Θ)
    (hfg : Tendsto f atTop (𝓝 g))
    (hbayes :
      ∀ n,
        (fun x => f n x)
          =ᵐ[ρ]
        (priors n).bayesAction density target)
    (hg : (fun x => g x) =ᵐ[ρ] estimator) :
    HasPositiveFiniteBayesApproximation
      ρ density target estimator := by
  obtain ⟨ns, _hns, hpointμ⟩ :
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ x ∂μ,
          Tendsto (fun n => f (ns n) x) atTop (𝓝 (g x)) :=
    (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  refine ⟨fun n => priors (ns n), ?_⟩
  have hpointρ :
      ∀ᵐ x ∂ρ,
        Tendsto (fun n => f (ns n) x) atTop (𝓝 (g x)) :=
    hρμ.ae_le hpointμ
  have hbayes_all :
      ∀ᵐ x ∂ρ, ∀ n,
        f n x = (priors n).bayesAction density target x :=
    ae_all_iff.mpr hbayes
  filter_upwards [hpointρ, hbayes_all, hg] with x hx hbx hgx
  have hfunctions :
      (fun n =>
        (priors (ns n)).bayesAction density target x)
        =
      (fun n => f (ns n) x) := by
    funext n
    exact (hbx (ns n)).symm
  rw [hfunctions, ← hgx]
  exact hx

/-- Norm-gap form of
`hasPositiveFiniteBayesApproximation_of_tendsto_Lp`. -/
theorem hasPositiveFiniteBayesApproximation_of_tendsto_Lp_norm
    {density : Θ → X → ℝ}
    {target : Θ → ℝ}
    {estimator : X → ℝ}
    (hρμ : ρ ≪ μ)
    (f : ℕ → Lp ℝ 2 μ)
    (g : Lp ℝ 2 μ)
    (priors : ℕ → PositiveFinitePrior Θ)
    (hfg : Tendsto (fun n => ‖f n - g‖) atTop (𝓝 0))
    (hbayes :
      ∀ n,
        (fun x => f n x)
          =ᵐ[ρ]
        (priors n).bayesAction density target)
    (hg : (fun x => g x) =ᵐ[ρ] estimator) :
    HasPositiveFiniteBayesApproximation
      ρ density target estimator := by
  exact
    hasPositiveFiniteBayesApproximation_of_tendsto_Lp
      hρμ f g priors
      (tendsto_iff_norm_sub_tendsto_zero.mpr hfg)
      hbayes hg

end

end GraybillDeal
