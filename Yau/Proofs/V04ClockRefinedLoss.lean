import Yau.Proofs.V04ClockNormalizerBounds

/-! The original logarithmic loss retains both cutoff support gains.
In particular the fiber error is divided by the actual squared radius. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

def clockBaseLossCoefficient (k : ClockData X) (j : ℕ) : ℝ :=
  1 + k.dampingPower * Real.log (j + 3) / (j + 1)

def clockFiberLossCoefficient (d : VariationData X q) (k : ClockData X) (j : ℕ) : ℝ :=
  (Real.log (k.fiberCoefficient j) + k.dampingPower * Real.log (j + 3) +
    k.dampingPower * Real.log (1 + d.B j)) / (k.fiberSupportScale * d.B j ^ 2)

theorem clockLoss_coefficients_nonneg {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j : ℕ) :
    0 ≤ clockBaseLossCoefficient k j ∧ 0 ≤ clockFiberLossCoefficient d k j := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hjlog : 0 ≤ Real.log (j + 3) := Real.log_nonneg (by linarith)
  have hClog := Real.log_nonneg (hk.2.2.2.1 j).1
  have hBlog : 0 ≤ Real.log (1 + d.B j) :=
    Real.log_nonneg (by linarith [(setup_index_bounds hd j).2])
  constructor
  · exact add_nonneg zero_le_one (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hjlog) (by positivity))
  · exact div_nonneg (add_nonneg (add_nonneg hClog
      (mul_nonneg (Nat.cast_nonneg _) hjlog)) (mul_nonneg (Nat.cast_nonneg _) hBlog))
      (mul_nonneg hk.1.le (sq_nonneg _))

theorem clockWeightRaw_loss_le_refined {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    -Real.log (clockWeightRaw d k j a F θ) ≤
      (4 * (a : ℝ) + clockBaseLossCoefficient k j) *
        wallCost d j (F.f (circlePoint θ)) (discTime F (circlePoint θ)) F.s +
      clockFiberLossCoefficient d k j *
        dualNorm (d.h (discTime F (circlePoint θ))) (F.f (circlePoint θ)).1
          (F.f (circlePoint θ)).2 := by
  let y := F.f (circlePoint θ)
  let t := discTime F (circlePoint θ)
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have hb := clockBaseCutoff_cost_bounds hd hk j y.1 ⟨ht.1.le, ht.2.le⟩
  have hf := clockFiberCutoff_norm_bound hd hk j y ht.1.le
  have hj : 0 < (j + 1 : ℝ) := by positivity
  have hdB : 0 < k.fiberSupportScale * d.B j ^ 2 :=
    mul_pos hk.1 (sq_pos_of_pos (setup_index_bounds hd j).2)
  have hχ : clockBaseCutoff d k j y.1 ≤ baseCost d j y.1 t / (j + 1) :=
    (le_div_iff₀ hj).2 hb.2
  have hψ : clockFiberCutoff d k j y ≤ dualNorm (d.h t) y.1 y.2 /
      (k.fiberSupportScale * d.B j ^ 2) := (le_div_iff₀ hdB).2 hf
  have hjlog : 0 ≤ (k.dampingPower : ℝ) * Real.log (j + 3) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith))
  have hClog := Real.log_nonneg (hk.2.2.2.1 j).1
  have hBlog : 0 ≤ (k.dampingPower : ℝ) * Real.log (1 + d.B j) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [(setup_index_bounds hd j).2]))
  have hbase := mul_le_mul_of_nonneg_right hχ hjlog
  have hfiber := mul_le_mul_of_nonneg_right hψ
    (add_nonneg (add_nonneg hClog hjlog) hBlog)
  have hw := wallPower_log_loss_le hd (hF.2.2.2.2.2.2.2.1 θ) a
  have heq := clockWeightRaw_neg_log (k := k) (a := a) hd hF θ
  have hbasefull : clockBaseCutoff d k j y.1 *
      (d.rho y.1 t + k.dampingPower * Real.log (j + 3)) ≤
      clockBaseLossCoefficient k j * baseCost d j y.1 t := by
    calc
      _ = clockBaseCutoff d k j y.1 * d.rho y.1 t +
        clockBaseCutoff d k j y.1 * (k.dampingPower * Real.log (j + 3)) := by ring
      _ ≤ baseCost d j y.1 t + baseCost d j y.1 t / (j + 1) *
          (k.dampingPower * Real.log (j + 3)) := add_le_add hb.1 hbase
      _ = _ := by dsimp only [clockBaseLossCoefficient]; ring
  have hfiberfull : clockFiberCutoff d k j y *
      (Real.log (k.fiberCoefficient j) + k.dampingPower * Real.log (j + 3) +
        k.dampingPower * Real.log (1 + d.B j)) ≤
      clockFiberLossCoefficient d k j * dualNorm (d.h t) y.1 y.2 := by
    convert hfiber using 1 <;> dsimp only [clockFiberLossCoefficient] <;> ring
  have hcut : -Real.log (clockWeightRaw d k j a F θ) ≤
      4 * (a : ℝ) * (wallBase d j y.1 + wallFiber d j y) +
        clockBaseLossCoefficient k j * baseCost d j y.1 t +
        clockFiberLossCoefficient d k j * dualNorm (d.h t) y.1 y.2 := by
    rw [heq]
    exact add_le_add (add_le_add hw hbasefull) hfiberfull
  have hp := setup_wallProfiles hd
  have hy := hF.2.2.2.2.2.2.2.1 θ
  have hwb := wallBase_nonneg hp (deltaBase_pos hp (setup_index_bounds hd j).1 hy.1)
  have hwf := wallFiber_nonneg hp (deltaFiber_pos hp (setup_index_bounds hd j).2 hy.2)
  have hbc := baseCost_nonneg hd j y.1 ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩
  have hs := hF.2.2.2.1
  have hwall : wallBase d j y.1 + wallFiber d j y ≤ wallCost d j y t F.s := by
    dsimp only [wallCost]
    dsimp only [y] at hbc ⊢
    nlinarith only [hwb, hwf, hbc, hs]
  have hbcwall : baseCost d j y.1 t ≤ wallCost d j y t F.s := by
    dsimp only [wallCost]
    dsimp only [y] at hbc ⊢
    nlinarith only [hwb, hwf, hs]
  have hscaled := mul_le_mul_of_nonneg_left hwall (show 0 ≤ 4 * (a : ℝ) by positivity)
  have hbscaled := mul_le_mul_of_nonneg_left hbcwall (clockLoss_coefficients_nonneg hd hk j).1
  change -Real.log (clockWeightRaw d k j a F θ) ≤
    (4 * (a : ℝ) + clockBaseLossCoefficient k j) * wallCost d j y t F.s +
      clockFiberLossCoefficient d k j * dualNorm (d.h t) y.1 y.2
  nlinarith only [hcut, hscaled, hbscaled]

theorem clockWeightRaw_average_loss_le_refined {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ)) ≤
      (4 * (a : ℝ) + clockBaseLossCoefficient k j) *
        circleAverage (fun θ => wallCost d j (F.f (circlePoint θ))
          (discTime F (circlePoint θ)) F.s) +
      clockFiberLossCoefficient d k j * circleAverage (fun θ =>
        dualNorm (d.h (discTime F (circlePoint θ))) (F.f (circlePoint θ)).1
          (F.f (circlePoint θ)).2) := by
  have hraw := (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
  have hl : Continuous (fun θ => -Real.log (clockWeightRaw d k j a F θ)) :=
    (hraw.log (fun θ => (clockWeightRaw_pos hd hF θ).ne')).neg
  have hw := (admissible_wallTrace_contDiff hd hF).continuous
  have hn := (admissible_normTrace_contDiff hd hF).continuous
  have hws : Continuous (fun θ => (4 * (a : ℝ) + clockBaseLossCoefficient k j) *
      wallCost d j (F.f (circlePoint θ)) (discTime F (circlePoint θ)) F.s) := continuous_const.mul hw
  have hns : Continuous (fun θ => clockFiberLossCoefficient d k j *
      dualNorm (d.h (discTime F (circlePoint θ))) (F.f (circlePoint θ)).1
        (F.f (circlePoint θ)).2) := continuous_const.mul hn
  have hh := circleAverage_mono_of_continuous hl (hws.add hns)
    (clockWeightRaw_loss_le_refined hd hk hF)
  change circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ)) ≤
    circleAverage (fun θ => (4 * (a : ℝ) + clockBaseLossCoefficient k j) *
      wallCost d j (F.f (circlePoint θ)) (discTime F (circlePoint θ)) F.s +
      clockFiberLossCoefficient d k j * dualNorm (d.h (discTime F (circlePoint θ)))
        (F.f (circlePoint θ)).1 (F.f (circlePoint θ)).2) at hh
  rw [circleAverage_add_of_continuous hws hns, circleAverage_const_mul,
    circleAverage_const_mul] at hh
  exact hh

end Yau.Blueprint.V04Proof
