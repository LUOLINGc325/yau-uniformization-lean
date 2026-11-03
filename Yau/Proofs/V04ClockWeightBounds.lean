import Yau.Proofs.V04ClockRegularity

/-! Positivity, the upper bound one, and the exact logarithmic loss of
the original raw clock. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem setup_rho_nonneg {d : VariationData X q} (hd : VariationSetup d)
    (x : X.manifold.Carrier) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ d.rho x t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hρ, _⟩ := hd.2.2.1.1
  exact (hρ x t ht).2

theorem clockWeightRaw_le_one {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k)
    {j a : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    clockWeightRaw d k j a F θ ≤ 1 := by
  have hc : (0 : ℝ) ≤ k.dampingPower := Nat.cast_nonneg _
  have hp := admissible_wallPower_bounds hd hF a θ
  have hbase := (hk.2.2.2.1 j).2.2.1 (F.f (circlePoint θ)).1
  have hfiber := (hk.2.2.2.1 j).2.2.2.2.1 (F.f (circlePoint θ))
  have hlogj : 0 ≤ Real.log (j + 3) := Real.log_nonneg (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith)
  have hlogC : 0 ≤ Real.log (k.fiberCoefficient j) := Real.log_nonneg (hk.2.2.2.1 j).1
  have hlogB : 0 ≤ Real.log (1 + d.B j) :=
    Real.log_nonneg (by linarith [(setup_index_bounds hd j).2])
  have hρ := setup_rho_nonneg hd (F.f (circlePoint θ)).1
    (admissible_discTime_mem hF (circlePoint_mem_closedBall θ)).1.le
  have hb : Real.exp (-clockBaseCutoff d k j (F.f (circlePoint θ)).1 *
      (d.rho (F.f (circlePoint θ)).1 (discTime F (circlePoint θ)) +
        k.dampingPower * Real.log (j + 3))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbase.1)
      (add_nonneg hρ (mul_nonneg hc hlogj))
  have hf : Real.exp (-clockFiberCutoff d k j (F.f (circlePoint θ)) *
      (Real.log (k.fiberCoefficient j) + k.dampingPower * Real.log (j + 3) +
        k.dampingPower * Real.log (1 + d.B j))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hfiber.1)
      (add_nonneg (add_nonneg hlogC (mul_nonneg hc hlogj)) (mul_nonneg hc hlogB))
  exact mul_le_one₀ (mul_le_one₀ (pow_le_one₀ hp.1.le hp.2)
    (Real.exp_nonneg _) hb) (Real.exp_nonneg _) hf

theorem clockWeightRaw_neg_log {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} {j a : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    -Real.log (clockWeightRaw d k j a F θ) =
      -4 * Real.log (wallPower d j a (F.f (circlePoint θ))) +
      clockBaseCutoff d k j (F.f (circlePoint θ)).1 *
        (d.rho (F.f (circlePoint θ)).1 (discTime F (circlePoint θ)) +
          k.dampingPower * Real.log (j + 3)) +
      clockFiberCutoff d k j (F.f (circlePoint θ)) *
        (Real.log (k.fiberCoefficient j) + k.dampingPower * Real.log (j + 3) +
          k.dampingPower * Real.log (1 + d.B j)) := by
  have hp := (admissible_wallPower_bounds hd hF a θ).1
  dsimp only [clockWeightRaw]
  rw [Real.log_mul (mul_pos (pow_pos hp 4) (Real.exp_pos _)).ne' (Real.exp_pos _).ne',
    Real.log_mul (pow_pos hp 4).ne' (Real.exp_pos _).ne', Real.log_pow,
    Real.log_exp, Real.log_exp]
  ring

end Yau.Blueprint.V04Proof
