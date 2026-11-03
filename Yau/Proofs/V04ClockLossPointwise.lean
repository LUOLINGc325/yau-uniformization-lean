import Yau.Proofs.V04ClockWeightBounds
import Yau.Proofs.V04DualNormOrder

/-! Pointwise loss bounds retain the support of each original cutoff.
The initial covector norm is bounded by the actual later norm. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem clockBaseCutoff_cost_bounds {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j : ℕ) (x : X.manifold.Carrier)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.T) :
    clockBaseCutoff d k j x * d.rho x t ≤ baseCost d j x t ∧
      clockBaseCutoff d k j x * (j + 1 : ℝ) ≤ baseCost d j x t := by
  have hb := (hk.2.2.2.1 j).2.2.1 x
  have hρ := setup_rho_nonneg hd x ht.1
  have hcost := baseCost_nonneg hd j x ⟨ht.1, ht.2.trans hd.2.1.le⟩
  by_cases hz : clockBaseCutoff d k j x = 0
  · simpa only [hz, zero_mul] using And.intro hcost hcost
  · have hsupport := (hk.2.2.2.1 j).2.2.2.1 (Function.mem_support.mpr hz)
    have hlarge := (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.2.2 x t ht hsupport
    constructor
    · exact (mul_le_of_le_one_left hρ hb.2.1).trans (by linarith)
    · exact (mul_le_of_le_one_left (by positivity : (0 : ℝ) ≤ j + 1) hb.2.1).trans
        (by linarith)

theorem clockFiberCutoff_norm_bound {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j : ℕ) (y : CotangentPoint X.manifold)
    {t : ℝ} (ht : 0 ≤ t) :
    clockFiberCutoff d k j y * (k.fiberSupportScale * d.B j ^ 2) ≤
      dualNorm (d.h t) y.1 y.2 := by
  have hb := (hk.2.2.2.1 j).2.2.2.2.1 y
  have hn := dualNorm_nonneg (d.h t) y.1 y.2
  by_cases hz : clockFiberCutoff d k j y = 0
  · simpa only [hz, zero_mul] using hn
  · have hsupport := (hk.2.2.2.1 j).2.2.2.2.2.1 (Function.mem_support.mpr hz)
    exact (mul_le_of_le_one_left (mul_nonneg hk.1.le (sq_nonneg _)) hb.2.1).trans
      (hsupport.le.trans (setup_dualNorm_initial_le hd y.1 y.2 ht))

theorem wallPower_log_loss_le {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {y : CotangentPoint X.manifold} (hy : y ∈ boundaryRegion d j) (a : ℕ) :
    -4 * Real.log (wallPower d j a y) ≤
      4 * (a : ℝ) * (wallBase d j y.1 + wallFiber d j y) := by
  have hp := setup_wallProfiles hd
  have hδ := deltaBase_pos hp (setup_index_bounds hd j).1 hy.1
  have hη := deltaFiber_pos hp (setup_index_bounds hd j).2 hy.2
  have hb := Real.one_sub_inv_le_log_of_pos hδ
  have hf := Real.one_sub_inv_le_log_of_pos hη
  rw [wallPower, Real.log_pow, wallProduct, Real.log_mul hδ.ne' hη.ne']
  dsimp only [wallBase, wallFiber]
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  nlinarith

theorem clockWeightRaw_loss_le_coarse {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    -Real.log (clockWeightRaw d k j a F θ) ≤
      4 * (a : ℝ) * (wallBase d j (F.f (circlePoint θ)).1 +
        wallFiber d j (F.f (circlePoint θ))) +
      baseCost d j (F.f (circlePoint θ)).1 (discTime F (circlePoint θ)) +
      2 * k.dampingPower * Real.log (j + 3) + Real.log (k.fiberCoefficient j) +
      k.dampingPower * Real.log (1 + d.B j) := by
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  have hb := clockBaseCutoff_cost_bounds hd hk j (F.f (circlePoint θ)).1 ⟨ht.1.le, ht.2.le⟩
  have hχ := ((hk.2.2.2.1 j).2.2.1 (F.f (circlePoint θ)).1).2.1
  have hψ := ((hk.2.2.2.1 j).2.2.2.2.1 (F.f (circlePoint θ))).2.1
  have hj : 0 ≤ (k.dampingPower : ℝ) * Real.log (j + 3) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith))
  have hC : 0 ≤ Real.log (k.fiberCoefficient j) := Real.log_nonneg (hk.2.2.2.1 j).1
  have hB : 0 ≤ (k.dampingPower : ℝ) * Real.log (1 + d.B j) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [(setup_index_bounds hd j).2]))
  have hbase := mul_le_of_le_one_left hj hχ
  have hfiber := mul_le_of_le_one_left (add_nonneg (add_nonneg hC hj) hB) hψ
  rw [clockWeightRaw_neg_log hd hF θ]
  have hw := wallPower_log_loss_le hd (hF.2.2.2.2.2.2.2.1 θ) a
  nlinarith only [hb.1, hbase, hfiber, hw]

end Yau.Blueprint.V04Proof
