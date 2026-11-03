import Yau.Proofs.V04ClockRefinedLoss

/-! The actual radius assumptions make both logarithmic support costs
small in the original outer index limit. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem setup_fiberRadius_tendsto {d : VariationData X q} (hd : VariationSetup d) :
    Tendsto d.B atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
  intro j
  have hB := (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.1
  linarith

theorem log_plus_radius_div_square_tendsto {d : VariationData X q} (hd : VariationSetup d)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun j : ℕ => (Real.log c + Real.log (d.B j)) / d.B j ^ 2) atTop (𝓝 0) := by
  have hB := setup_fiberRadius_tendsto hd
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hB
  have hconst := (hB.const_div_atTop (Real.log c)).div_atTop hB
  have hlog := hl.div_atTop hB
  convert hconst.add hlog using 1
  · funext j
    simp only [Function.comp_def, id_eq, div_div]
    ring
  · norm_num

theorem clock_log_index_over_radius_tendsto {d : VariationData X q} (hd : VariationSetup d) :
    Tendsto (fun j : ℕ => Real.log (j + 3) / d.B j ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero (fun j : ℕ => div_nonneg (Real.log_nonneg (by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith)) (sq_nonneg _)) _
    (log_plus_radius_div_square_tendsto hd 3 (by norm_num))
  intro j
  have hB := (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.1
  have hBp := (setup_index_bounds hd j).2
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < j + 3)
    (show (j : ℝ) + 3 ≤ 3 * d.B j by linarith)
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hBp.ne'] at hh
  exact div_le_div_of_nonneg_right hh (sq_nonneg _)

theorem clock_log_one_add_radius_tendsto {d : VariationData X q} (hd : VariationSetup d) :
    Tendsto (fun j : ℕ => Real.log (1 + d.B j) / d.B j ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero (fun j : ℕ => div_nonneg (Real.log_nonneg (by
    linarith [(setup_index_bounds hd j).2])) (sq_nonneg _)) _
    (log_plus_radius_div_square_tendsto hd 2 (by norm_num))
  intro j
  have hB := (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.1
  have hBp := (setup_index_bounds hd j).2
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < 1 + d.B j)
    (show 1 + d.B j ≤ 2 * d.B j by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hBp.ne'] at hh
  exact div_le_div_of_nonneg_right hh (sq_nonneg _)

theorem clockFiberLossCoefficient_tendsto {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) :
    Tendsto (clockFiberLossCoefficient d k) atTop (𝓝 0) := by
  have hh := ((hk.2.2.2.2.add ((clock_log_index_over_radius_tendsto hd).const_mul (k.dampingPower : ℝ))).add
    ((clock_log_one_add_radius_tendsto hd).const_mul (k.dampingPower : ℝ))).div_const k.fiberSupportScale
  convert hh using 1
  · funext j
    dsimp only [clockFiberLossCoefficient]
    ring
  · simp only [zero_mul, mul_zero, zero_add, zero_div]

theorem clockBaseLossCoefficient_tendsto (k : ClockData X) :
    Tendsto (clockBaseLossCoefficient k) atTop (𝓝 1) := by
  have hN : Tendsto (fun j : ℕ => (j + 3 : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro j
    linarith
  have hL := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hN
  have hI : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hR : Tendsto (fun j : ℕ => (j + 3 : ℝ) / (j + 1)) atTop (𝓝 1) := by
    have hh : Tendsto (fun j : ℕ => (1 : ℝ) + 2 * (1 / (j + 1))) atTop (𝓝 (1 + 2 * 0)) :=
      tendsto_const_nhds.add (hI.const_mul (2 : ℝ))
    have heq : (fun j : ℕ => (j + 3 : ℝ) / (j + 1)) =
        (fun j : ℕ => (1 : ℝ) + 2 * (1 / (j + 1))) := by
      funext j
      have hj : (j + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      <;> ring
    rw [heq]
    simpa only [mul_zero, add_zero] using hh
  have hsmall : Tendsto (fun j : ℕ => (k.dampingPower : ℝ) * Real.log (j + 3) /
      (j + 1)) atTop (𝓝 0) := by
    convert (hL.mul hR).const_mul (k.dampingPower : ℝ) using 1 <;> norm_num
    funext j
    have hj : (j + 3 : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  change Tendsto (fun j : ℕ => 1 + (k.dampingPower : ℝ) * Real.log (j + 3) / (j + 1))
    atTop (𝓝 1)
  simpa only [add_zero] using (tendsto_const_nhds.add hsmall)

end Yau.Blueprint.V04Proof
