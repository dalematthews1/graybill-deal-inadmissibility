import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# A convergence-extraction lemma for complete-class arguments

One analytic step in the Brown--Lehmann--Casella finite-Bayes
approximation theorem is independent of statistical decision theory.
If the integrated squared gap between a sequence of procedures and a
candidate limit tends to zero, then a subsequence converges almost
everywhere.  The same conclusion holds for a *weighted* squared gap
whenever the weight has a strictly positive lower bound (with respect
to the measure currently under consideration).

This file proves that step without any finiteness assumption on the
measure.  The proof passes from the `L²` gap to convergence in measure,
then uses Mathlib's Borel--Cantelli subsequence theorem.  Consequently,
the result can be applied directly to a restricted measure on one set
of a sigma-finite exhaustion.

The genuinely decision-theoretic work still needed for the full
complete-class theorem is to construct finite priors whose Bayes-risk
gaps vanish on a compatible exhaustion.
-/

namespace GraybillDeal

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CompleteClass

variable {X : Type*} [MeasurableSpace X]
variable {m : Measure X}

/-- Vanishing integrated squared error produces an almost-everywhere
convergent subsequence.  No finite-measure hypothesis is needed. -/
theorem exists_ae_tendsto_subsequence_of_tendsto_lintegral_sq
    {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) m)
    (hg : AEStronglyMeasurable g m)
    (hgap :
      Tendsto
        (fun n =>
          ∫⁻ x, ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m)
        atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂m,
        Tendsto (fun n => f (ns n) x) atTop (𝓝 (g x)) := by
  have heLp :
      Tendsto
        (fun n => eLpNorm (f n - g) (2 : ℝ≥0∞) m)
        atTop (𝓝 0) := by
    have hrpow :=
      hgap.ennrpow_const (1 / (2 : ℝ))
    simpa [eLpNorm_eq_lintegral_rpow_enorm_toReal, Pi.sub_apply] using hrpow
  exact
    (tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ℝ≥0∞))
      (by norm_num) hf hg heLp).exists_seq_tendsto_ae

/-- If `c` is positive and finite and `c ≤ weight` almost everywhere,
then a vanishing weighted squared gap forces the unweighted squared gap
to vanish. -/
theorem tendsto_lintegral_sq_of_weighted_lower_bound
    {f : ℕ → X → ℝ} {g : X → ℝ}
    {weight : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hlower : ∀ᵐ x ∂m, c ≤ weight x)
    (hgap :
      Tendsto
        (fun n =>
          ∫⁻ x, weight x * ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m)
        atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        ∫⁻ x, ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m)
      atTop (𝓝 0) := by
  have hle (n : ℕ) :
      (∫⁻ x, ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m) ≤
        c⁻¹ *
          (∫⁻ x, weight x * ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m) := by
    apply (ENNReal.mul_le_iff_le_inv hc0 hctop).mp
    calc
      c * (∫⁻ x, ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m) =
          ∫⁻ x, c * ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m := by
            symm
            exact lintegral_const_mul' c _ hctop
      _ ≤ ∫⁻ x, weight x * ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m := by
        apply lintegral_mono_ae
        filter_upwards [hlower] with x hx
        exact mul_le_mul_of_nonneg_right hx zero_le
  have hupper :
      Tendsto
        (fun n =>
          c⁻¹ *
            (∫⁻ x, weight x * ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m))
        atTop (𝓝 0) := by
    simpa using
      ENNReal.Tendsto.const_mul (a := c⁻¹) hgap
        (Or.inr (by simp [hc0]))
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => zero_le) hle

/-- A vanishing weighted squared gap, together with an almost-everywhere
positive uniform lower bound on the weight, produces an almost-everywhere
convergent subsequence.  Applying this theorem with `m.restrict s`
gives the corresponding local statement on a set `s`. -/
theorem exists_ae_tendsto_subsequence_of_tendsto_weighted_lintegral_sq
    {f : ℕ → X → ℝ} {g : X → ℝ}
    {weight : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ n, AEStronglyMeasurable (f n) m)
    (hg : AEStronglyMeasurable g m)
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hlower : ∀ᵐ x ∂m, c ≤ weight x)
    (hgap :
      Tendsto
        (fun n =>
          ∫⁻ x, weight x * ‖f n x - g x‖ₑ ^ (2 : ℝ) ∂m)
        atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂m,
        Tendsto (fun n => f (ns n) x) atTop (𝓝 (g x)) := by
  apply exists_ae_tendsto_subsequence_of_tendsto_lintegral_sq hf hg
  exact
    tendsto_lintegral_sq_of_weighted_lower_bound
      hc0 hctop hlower hgap

end CompleteClass

end

end GraybillDeal
