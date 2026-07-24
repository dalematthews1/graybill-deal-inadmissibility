import GraybillDeal.GeneralCollectedPointwise
import GraybillDeal.SeriesIntegration

/-!
# Uniform domination of the generalized collected series

For every `ν ≥ 9`, the centered parameter
`generalAlpha ν = (ν-4)/(4(ν-1))` lies in `[0,1/4]`.  This gives a simple
universal bound `65` for the seven polynomial coefficients and hence a
summable uniform majorant for the target-indexed collected series.
-/

namespace GraybillDeal

open Set

noncomputable section

def generalCollectedMajorant (s : ℝ) (m : ℕ) : ℝ :=
  65 * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m

theorem generalAlpha_nonneg {ν : ℝ} (hν : 9 ≤ ν) :
    0 ≤ generalAlpha ν := by
  unfold generalAlpha
  have hnum : 0 ≤ ν - 4 := by linarith
  have hsub : 0 ≤ ν - 1 := by linarith
  have hden : 0 ≤ 4 * (ν - 1) :=
    mul_nonneg (by norm_num) hsub
  exact div_nonneg hnum hden

theorem generalAlpha_le_one_div_four {ν : ℝ} (hν : 9 ≤ ν) :
    generalAlpha ν ≤ 1 / 4 := by
  unfold generalAlpha
  have hsub : 0 < ν - 1 := by linarith
  have hden : 0 < 4 * (ν - 1) :=
    mul_pos (by norm_num) hsub
  rw [div_le_iff₀ hden]
  nlinarith

theorem generalCollectedPointwiseSummand_norm_le
    {ν s x : ℝ} (m : ℕ) (hν : 9 ≤ ν)
    (_hs : |s| < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖generalCollectedPointwiseSummand ν s x m‖
      ≤ generalCollectedMajorant s m := by
  let α := generalAlpha ν
  have hα0 : 0 ≤ α := generalAlpha_nonneg hν
  have hα1 : α ≤ 1 / 4 := generalAlpha_le_one_div_four hν
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hx2_le : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hs2_nonneg : 0 ≤ s ^ 2 := sq_nonneg s
  have ht_nonneg : 0 ≤ s ^ 2 * x ^ 2 :=
    mul_nonneg hs2_nonneg hx2_nonneg
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
  let c0 := shiftedBinomialC0 (s ^ 2 * x ^ 2) m
  let c1 := shiftedBinomialC1 (s ^ 2 * x ^ 2) m
  let c2 := shiftedBinomialC2 (s ^ 2 * x ^ 2) m
  let c3 := shiftedBinomialC3 (s ^ 2 * x ^ 2) m
  have hc0_nonneg : 0 ≤ c0 := by
    unfold c0 shiftedBinomialC0
    positivity
  have hc1_nonneg : 0 ≤ c1 := by
    unfold c1 shiftedBinomialC1
    positivity
  have hc2_nonneg : 0 ≤ c2 := by
    unfold c2 shiftedBinomialC2
    positivity
  have hc3_nonneg : 0 ≤ c3 := by
    unfold c3 shiftedBinomialC3
    positivity
  have hc0_le : c0 ≤ B := by
    unfold c0 shiftedBinomialC0 B
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hc1_le : c1 ≤ B := by
    unfold c1 shiftedBinomialC1 B
    exact mul_le_mul hchoose1 hpow
      (pow_nonneg ht_nonneg m) (by positivity)
  have hc2_le : c2 ≤ B := by
    unfold c2 shiftedBinomialC2 B
    exact mul_le_mul hchoose2 hpow
      (pow_nonneg ht_nonneg m) (by positivity)
  have hc3_le : c3 ≤ B := by
    unfold c3 shiftedBinomialC3 B
    exact mul_le_mul hchoose3 hpow
      (pow_nonneg ht_nonneg m) (by positivity)
  have hcoef0 : |2 * α| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hcoef1 : |2 - 10 * α| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hcoef2 : |-10 + 20 * α| ≤ 10 := by
    rw [abs_le]
    constructor <;> linarith
  have hcoef3 : |20 - 20 * α| ≤ 20 := by
    rw [abs_le]
    constructor <;> linarith
  have hcoef4 : |-20 + 10 * α| ≤ 20 := by
    rw [abs_le]
    constructor <;> linarith
  have hcoef5 : |10 - 2 * α| ≤ 10 := by
    rw [abs_le]
    constructor <;> linarith
  let a : ℝ := (2 * α) * x ^ 2 * c0
  let b : ℝ := (2 - 10 * α) * c1
  let c : ℝ := (-10 + 20 * α) * x ^ 2 * c1
  let d : ℝ := (20 - 20 * α) * c2
  let e : ℝ := (-20 + 10 * α) * x ^ 2 * c2
  let f : ℝ := (10 - 2 * α) * c3
  let g : ℝ := 2 * x ^ 2 * c3
  have ha : |a| ≤ 1 * B := by
    unfold a
    rw [abs_mul, abs_mul, abs_of_nonneg hx2_nonneg,
      abs_of_nonneg hc0_nonneg]
    calc
      |2 * α| * x ^ 2 * c0 ≤ 1 * 1 * B := by gcongr
      _ = 1 * B := by ring
  have hb : |b| ≤ 2 * B := by
    unfold b
    rw [abs_mul, abs_of_nonneg hc1_nonneg]
    gcongr
  have hc : |c| ≤ 10 * B := by
    unfold c
    rw [abs_mul, abs_mul, abs_of_nonneg hx2_nonneg,
      abs_of_nonneg hc1_nonneg]
    calc
      |-10 + 20 * α| * x ^ 2 * c1 ≤ 10 * 1 * B := by gcongr
      _ = 10 * B := by ring
  have hd : |d| ≤ 20 * B := by
    unfold d
    rw [abs_mul, abs_of_nonneg hc2_nonneg]
    gcongr
  have he : |e| ≤ 20 * B := by
    unfold e
    rw [abs_mul, abs_mul, abs_of_nonneg hx2_nonneg,
      abs_of_nonneg hc2_nonneg]
    calc
      |-20 + 10 * α| * x ^ 2 * c2 ≤ 20 * 1 * B := by gcongr
      _ = 20 * B := by ring
  have hf : |f| ≤ 10 * B := by
    unfold f
    rw [abs_mul, abs_of_nonneg hc3_nonneg]
    gcongr
  have hg : |g| ≤ 2 * B := by
    rw [abs_of_nonneg (by unfold g; positivity)]
    unfold g
    calc
      2 * x ^ 2 * c3 ≤ 2 * 1 * B := by gcongr
      _ = 2 * B := by ring
  have htri :
      |a + b + c + d + e + f - g|
        ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    calc
      |a + b + c + d + e + f - g|
          ≤ |a + b + c + d + e + f| + |g| := abs_sub _ _
      _ ≤ (|a + b + c + d + e| + |f|) + |g| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|a + b + c + d| + |e|) + |f|) + |g| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (((|a + b + c| + |d|) + |e|) + |f|) + |g| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((((|a + b| + |c|) + |d|) + |e|) + |f|) + |g| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (((((|a| + |b|) + |c|) + |d|) + |e|) + |f|) + |g| := by
        gcongr
        exact abs_add_le _ _
      _ = |a| + |b| + |c| + |d| + |e| + |f| + |g| := by ring
  have hinner : |a + b + c + d + e + f - g| ≤ 65 * B := by
    calc
      |a + b + c + d + e + f - g|
          ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := htri
      _ ≤
          1 * B + 2 * B + 10 * B + 20 * B
            + 20 * B + 10 * B + 2 * B := by
        linarith
      _ = 65 * B := by ring
  have hbase_nonneg : 0 ≤ 1 - x ^ 2 :=
    sub_nonneg.mpr hx2_le
  have hbase_le : 1 - x ^ 2 ≤ 1 :=
    sub_le_self 1 hx2_nonneg
  have hexponent : 0 ≤ ν / 2 := by linarith
  have hweight_nonneg :
      0 ≤ (1 - x ^ 2) ^ (ν / 2) :=
    Real.rpow_nonneg hbase_nonneg _
  have hweight_le :
      (1 - x ^ 2) ^ (ν / 2) ≤ 1 :=
    Real.rpow_le_one hbase_nonneg hbase_le hexponent
  unfold generalCollectedPointwiseSummand generalCollectedMajorant
  dsimp only
  change
    ‖(1 - x ^ 2) ^ (ν / 2) * (a + b + c + d + e + f - g)‖
      ≤ 65 * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight_nonneg]
  calc
    (1 - x ^ 2) ^ (ν / 2) * |a + b + c + d + e + f - g|
        ≤ 1 * (65 * B) := by gcongr
    _ = 65 * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m := by
      unfold B
      ring

theorem summable_generalCollectedMajorant
    {s : ℝ} (hs : |s| < 1) :
    Summable (generalCollectedMajorant s) := by
  have hs2 : ‖s ^ 2‖ < 1 := by
    simpa using
      (sq_mul_sq_norm_lt_one hs (x := (1 : ℝ)) (by norm_num))
  have h :=
    (summable_choose_four_mul_geometric hs2).mul_left (65 : ℝ)
  change Summable
    (fun m => 65 * ((m + 4).choose 4 : ℝ) * (s ^ 2) ^ m)
  simpa only [mul_assoc] using h

end

end GraybillDeal
