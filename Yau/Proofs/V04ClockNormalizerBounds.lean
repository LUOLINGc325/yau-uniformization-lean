import Yau.Proofs.V04ClockLossPointwise
import Yau.Proofs.V04ClockJensen
import Yau.Proofs.V04UniformCosts
import Yau.Proofs.V03FunctionalLower

/-! The normalizer is bounded below on minimizing tails by a constant
chosen before every penalty and every minimizing family. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

def clockLossCoarseConstant (d : VariationData X q) (k : ClockData X) (j : ℕ) : ℝ :=
  2 * k.dampingPower * Real.log (j + 3) + Real.log (k.fiberCoefficient j) +
    k.dampingPower * Real.log (1 + d.B j)

theorem clockWeightRaw_loss_le_boundaryDensity {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    -Real.log (clockWeightRaw d k j a F θ) ≤
      (4 * (a : ℝ) + 1) * boundaryDensity d j F (circlePoint θ) +
        clockLossCoarseConstant d k j := by
  have hl := clockWeightRaw_loss_le_coarse (a := a) hd hk hF θ
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have hN := dualNorm_nonneg (d.h (discTime F (circlePoint θ)))
    (F.f (circlePoint θ)).1 (F.f (circlePoint θ)).2
  have hb := baseCost_nonneg hd j (F.f (circlePoint θ)).1
    ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩
  have hp := setup_wallProfiles hd
  have hy := hF.2.2.2.2.2.2.2.1 θ
  have hwb := wallBase_nonneg hp (deltaBase_pos hp (setup_index_bounds hd j).1 hy.1)
  have hwf := wallFiber_nonneg hp (deltaFiber_pos hp (setup_index_bounds hd j).2 hy.2)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hs := hF.2.2.2.1
  have hwall : wallBase d j (F.f (circlePoint θ)).1 +
      wallFiber d j (F.f (circlePoint θ)) ≤ boundaryDensity d j F (circlePoint θ) := by
    dsimp only [boundaryDensity, wallCost]
    nlinarith only [hN, hb, hwb, hwf, hs]
  have hbase : baseCost d j (F.f (circlePoint θ)).1 (discTime F (circlePoint θ)) ≤
      boundaryDensity d j F (circlePoint θ) := by
    dsimp only [boundaryDensity, wallCost]
    nlinarith only [hN, hwb, hwf, hs]
  have hscaled := mul_le_mul_of_nonneg_left hwall (show 0 ≤ 4 * (a : ℝ) by positivity)
  dsimp only [clockLossCoarseConstant]
  nlinarith only [hl, hscaled, hbase]

theorem clockWeightRaw_average_loss_le {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ)) ≤
      (4 * (a : ℝ) + 1) * boundaryCost d j F + clockLossCoarseConstant d k j := by
  have hraw := (clockWeightRaw_contDiff (a := a) hd hk hF).continuous
  have hlog := hraw.log (fun θ => (clockWeightRaw_pos hd hF θ).ne')
  have hden := (admissible_boundaryDensity_circle_contDiff hd hF).continuous
  have hprod : Continuous (fun θ => (4 * (a : ℝ) + 1) * boundaryDensity d j F (circlePoint θ)) :=
    continuous_const.mul hden
  have hh := circleAverage_mono_of_continuous hlog.neg (hprod.add continuous_const)
    (clockWeightRaw_loss_le_boundaryDensity hd hk hF)
  change circleAverage (fun θ => -Real.log (clockWeightRaw d k j a F θ)) ≤
    circleAverage (fun θ => (4 * (a : ℝ) + 1) * boundaryDensity d j F (circlePoint θ) +
      clockLossCoarseConstant d k j) at hh
  rw [circleAverage_add_of_continuous hprod continuous_const, circleAverage_const_value,
    circleAverage_const_mul] at hh
  exact hh

theorem fixed_index_clock_normalizer_lower {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ) :
    ∃ z : ℝ, 0 < z ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ F : ℕ → VariationDisc X, MinimizingSequence d j ε F →
        ∀ᶠ ν in atTop, z ≤ circleAverage (clockWeightRaw d k j a (F ν)) := by
  obtain ⟨M, _, hM⟩ := fixed_index_boundary_cost_cap hd j
  let A := (4 * (a : ℝ) + 1) * M + clockLossCoarseConstant d k j
  refine ⟨Real.exp (-A), Real.exp_pos _, fun ε hε hε1 F hF => ?_⟩
  filter_upwards [hM ε hε hε1 F hF] with ν hν
  apply clockWeightRaw_average_lower_of_loss hd hk (hF.1 ν)
  have hscale : (4 * (a : ℝ) + 1) * boundaryCost d j (F ν) ≤
      (4 * (a : ℝ) + 1) * M := mul_le_mul_of_nonneg_left hν (by positivity)
  have hloss := clockWeightRaw_average_loss_le (a := a) hd hk (hF.1 ν)
  dsimp only [A]
  linarith only [hscale, hloss]

end Yau.Blueprint.V04Proof
