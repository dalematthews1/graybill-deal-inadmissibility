import GraybillDeal.CollectedPointwise
import GraybillDeal.IntegratedCoefficients
import GraybillDeal.SeriesIntegration

/-!
# Termwise integration of the collected coefficient series

The collected target-indexed summands admit the same summable uniform
majorant as the original negative-binomial summands.  Dominated convergence
therefore identifies their integrated sum with `I13`.
-/

namespace GraybillDeal

open MeasureTheory Set

noncomputable section

theorem collectedPointwiseSummand13_norm_le {s x : ℝ} (m : ℕ)
    (_hs : |s| < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖collectedPointwiseSummand13 s x m‖ ≤ pointwiseMajorant13 s m := by
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hx2_le : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hs2_nonneg : 0 ≤ s ^ 2 := sq_nonneg s
  have ht_nonneg : 0 ≤ s ^ 2 * x ^ 2 := mul_nonneg hs2_nonneg hx2_nonneg
  have ht_le : s ^ 2 * x ^ 2 ≤ s ^ 2 := by
    nlinarith [mul_nonneg hs2_nonneg (sub_nonneg.mpr hx2_le)]
  have hpow :
      (s ^ 2 * x ^ 2) ^ m ≤ (s ^ 2) ^ m :=
    pow_le_pow_left₀ ht_nonneg ht_le m
  let B : ℝ := ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m
  have hB_nonneg : 0 ≤ B := by
    unfold B
    positivity
  have hchoose1 :
      ((m + 3).choose 4 : ℝ) ≤ ((m + 4).choose 4 : ℝ) := by
    exact_mod_cast Nat.choose_le_choose 4 (by omega)
  have hchoose2 :
      ((m + 2).choose 4 : ℝ) ≤ ((m + 4).choose 4 : ℝ) := by
    exact_mod_cast Nat.choose_le_choose 4 (by omega)
  have hchoose3 :
      ((m + 1).choose 4 : ℝ) ≤ ((m + 4).choose 4 : ℝ) := by
    exact_mod_cast Nat.choose_le_choose 4 (by omega)
  have hC0_nonneg :
      0 ≤ shiftedBinomialC0 (s ^ 2 * x ^ 2) m := by
    unfold shiftedBinomialC0
    positivity
  have hC1_nonneg :
      0 ≤ shiftedBinomialC1 (s ^ 2 * x ^ 2) m := by
    unfold shiftedBinomialC1
    positivity
  have hC2_nonneg :
      0 ≤ shiftedBinomialC2 (s ^ 2 * x ^ 2) m := by
    unfold shiftedBinomialC2
    positivity
  have hC3_nonneg :
      0 ≤ shiftedBinomialC3 (s ^ 2 * x ^ 2) m := by
    unfold shiftedBinomialC3
    positivity
  have hC0_le :
      shiftedBinomialC0 (s ^ 2 * x ^ 2) m ≤ B := by
    unfold shiftedBinomialC0 B
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hC1_le :
      shiftedBinomialC1 (s ^ 2 * x ^ 2) m ≤ B := by
    unfold shiftedBinomialC1 B
    exact mul_le_mul hchoose1 hpow (pow_nonneg ht_nonneg m) (by positivity)
  have hC2_le :
      shiftedBinomialC2 (s ^ 2 * x ^ 2) m ≤ B := by
    unfold shiftedBinomialC2 B
    exact mul_le_mul hchoose2 hpow (pow_nonneg ht_nonneg m) (by positivity)
  have hC3_le :
      shiftedBinomialC3 (s ^ 2 * x ^ 2) m ≤ B := by
    unfold shiftedBinomialC3 B
    exact mul_le_mul hchoose3 hpow (pow_nonneg ht_nonneg m) (by positivity)
  let c0 := shiftedBinomialC0 (s ^ 2 * x ^ 2) m
  let c1 := shiftedBinomialC1 (s ^ 2 * x ^ 2) m
  let c2 := shiftedBinomialC2 (s ^ 2 * x ^ 2) m
  let c3 := shiftedBinomialC3 (s ^ 2 * x ^ 2) m
  have hc0_nonneg : 0 ≤ c0 := hC0_nonneg
  have hc1_nonneg : 0 ≤ c1 := hC1_nonneg
  have hc2_nonneg : 0 ≤ c2 := hC2_nonneg
  have hc3_nonneg : 0 ≤ c3 := hC3_nonneg
  have hc0_le : c0 ≤ B := hC0_le
  have hc1_le : c1 ≤ B := hC1_le
  have hc2_le : c2 ≤ B := hC2_le
  have hc3_le : c3 ≤ B := hC3_le
  let a : ℝ := (4 / 11) * x ^ 2 * c0
  let b : ℝ := (2 / 11) * c1
  let c : ℝ := (70 / 11) * x ^ 2 * c1
  let d : ℝ := (180 / 11) * c2
  let e : ℝ := (200 / 11) * x ^ 2 * c2
  let f : ℝ := (106 / 11) * c3
  let g : ℝ := 2 * x ^ 2 * c3
  have ha : |a| ≤ (4 / 11 : ℝ) * B := by
    rw [abs_of_nonneg]
    · unfold a
      gcongr
      nlinarith
    · unfold a
      positivity
  have hb : |b| ≤ (2 / 11 : ℝ) * B := by
    rw [abs_of_nonneg]
    · unfold b
      gcongr
    · unfold b
      positivity
  have hc : |c| ≤ (70 / 11 : ℝ) * B := by
    rw [abs_of_nonneg]
    · unfold c
      gcongr
      nlinarith
    · unfold c
      positivity
  have hd : |d| ≤ (180 / 11 : ℝ) * B := by
    rw [abs_of_nonneg]
    · unfold d
      gcongr
    · unfold d
      positivity
  have he : |e| ≤ (200 / 11 : ℝ) * B := by
    rw [abs_of_nonneg]
    · unfold e
      gcongr
      nlinarith
    · unfold e
      positivity
  have hf : |f| ≤ (106 / 11 : ℝ) * B := by
    rw [abs_of_nonneg]
    · unfold f
      gcongr
    · unfold f
      positivity
  have hg : |g| ≤ 2 * B := by
    rw [abs_of_nonneg]
    · unfold g
      gcongr
      nlinarith
    · unfold g
      positivity
  have htri :
      |a + b - c + d - e + f - g|
        ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    calc
      |a + b - c + d - e + f - g|
          ≤ |a + b - c + d - e + f| + |g| := abs_sub _ _
      _ ≤ (|a + b - c + d - e| + |f|) + |g| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|a + b - c + d| + |e|) + |f|) + |g| := by
        gcongr
        exact abs_sub _ _
      _ ≤ (((|a + b - c| + |d|) + |e|) + |f|) + |g| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((((|a + b| + |c|) + |d|) + |e|) + |f|) + |g| := by
        gcongr
        exact abs_sub _ _
      _ ≤ (((((|a| + |b|) + |c|) + |d|) + |e|) + |f|) + |g| := by
        gcongr
        exact abs_add_le _ _
      _ = |a| + |b| + |c| + |d| + |e| + |f| + |g| := by ring
  have hinner : |a + b - c + d - e + f - g| ≤ 60 * B := by
    calc
      |a + b - c + d - e + f - g|
          ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := htri
      _ ≤
          (4 / 11 : ℝ) * B + (2 / 11 : ℝ) * B
            + (70 / 11 : ℝ) * B + (180 / 11 : ℝ) * B
            + (200 / 11 : ℝ) * B + (106 / 11 : ℝ) * B + 2 * B := by
        linarith
      _ ≤ 60 * B := by
        nlinarith
  have hweight_nonneg : 0 ≤ (1 - x ^ 2) ^ 6 := by positivity
  have hweight_le : (1 - x ^ 2) ^ 6 ≤ 1 := by
    have hbase_nonneg : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr hx2_le
    have hbase_le : 1 - x ^ 2 ≤ 1 := sub_le_self 1 hx2_nonneg
    simpa using pow_le_pow_left₀ hbase_nonneg hbase_le 6
  unfold collectedPointwiseSummand13 pointwiseMajorant13
  change
    ‖(1 - x ^ 2) ^ 6 * (a + b - c + d - e + f - g)‖
      ≤ 60 * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight_nonneg]
  calc
    (1 - x ^ 2) ^ 6 * |a + b - c + d - e + f - g|
        ≤ 1 * (60 * B) := by gcongr
    _ = 60 * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m := by
      unfold B
      ring

/--
The collected pointwise summands may be integrated term by term, and their
integrals sum to the paired kernel integral `I13`.
-/
theorem hasSum_integral_collectedPointwiseSummand13 {s : ℝ}
    (hs : |s| < 1) :
    HasSum
      (fun m => ∫ x in (0 : ℝ)..1, collectedPointwiseSummand13 s x m)
      (I13 s) := by
  have h :
      HasSum
        (fun m => ∫ x in (0 : ℝ)..1, collectedPointwiseSummand13 s x m)
        (∫ x in (0 : ℝ)..1,
          (1 - x ^ 2) ^ 6 * x ^ 2
            * pairedPolynomial13 (s ^ 2) (x ^ 2)
            / (1 - s ^ 2 * x ^ 2) ^ 5) := by
    apply hasSum_intervalIntegral_of_uniform_majorant
      (c := pointwiseMajorant13 s)
    · intro m
      apply Continuous.continuousOn
      unfold collectedPointwiseSummand13
        shiftedBinomialC0 shiftedBinomialC1
        shiftedBinomialC2 shiftedBinomialC3
      fun_prop
    · intro m x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le] using hx
      exact collectedPointwiseSummand13_norm_le m hs hx'
    · exact summable_pointwiseMajorant13 hs
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le] using hx
      exact hasSum_collectedPointwiseSummand13 hs hx'
  simpa only [I13_eq_paired hs] using h

/-- The equivalent collected-integrand sequence also sums to `I13`. -/
theorem hasSum_integral_collectedIntegrand13 {s : ℝ} (hs : |s| < 1) :
    HasSum
      (fun m => ∫ x in (0 : ℝ)..1, collectedIntegrand13 s x m)
      (I13 s) := by
  have h := hasSum_integral_collectedPointwiseSummand13 hs
  convert h using 1
  funext m
  apply intervalIntegral.integral_congr
  intro x hx
  exact (collectedPointwiseSummand13_eq_collectedIntegrand13 s x m).symm

/-- The certified coefficient series has sum `I13`. -/
theorem hasSum_seriesTerm13_sq_eq_I13 {s : ℝ} (hs : |s| < 1) :
    HasSum (seriesTerm13 (s ^ 2)) (I13 s) := by
  have h := hasSum_integral_collectedIntegrand13 hs
  convert h using 1
  funext m
  exact (integral_collectedIntegrand13 s m).symm

/-- Exact identification of the analytic integral with the certified series. -/
theorem I13_eq_seriesSum13_sq {s : ℝ} (hs : |s| < 1) :
    I13 s = seriesSum13 (s ^ 2) := by
  exact (hasSum_seriesTerm13_sq_eq_I13 hs).tsum_eq.symm

/-- The exact uniform certificate inherited from the first three series terms. -/
theorem certificate_le_I13 {s : ℝ} (hs : |s| < 1) :
    M 1 * (1489 / 5610 : ℝ) ≤ I13 s := by
  rw [I13_eq_seriesSum13_sq hs]
  exact certificate_le_seriesSum13 (sq_nonneg s)
    (hasSum_seriesTerm13_sq_eq_I13 hs).summable

/-- The paired integral is strictly positive throughout `|s| < 1`. -/
theorem I13_pos {s : ℝ} (hs : |s| < 1) : 0 < I13 s := by
  rw [I13_eq_seriesSum13_sq hs]
  exact seriesSum13_pos (sq_nonneg s)
    (hasSum_seriesTerm13_sq_eq_I13 hs).summable

end

end GraybillDeal
