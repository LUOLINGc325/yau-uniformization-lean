import Yau.Proofs.V04ClockWeightBounds

/-! On each actual cutoff support, the frozen exponential clock cancels
the complete corresponding wall error with its original powers. -/

open scoped Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem clockRaw_base_damping {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ} (ha : 3 ≤ 4 * a)
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (θ : ℝ)
    (hχ : clockBaseCutoff d k j (F.f (circlePoint θ)).1 = 1) :
    clockWeightRaw d k j a F θ * Real.exp (d.rho (F.f (circlePoint θ)).1
      (discTime F (circlePoint θ))) * (deltaBase d j (F.f (circlePoint θ)).1 ^ 3)⁻¹ ≤
        ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ := by
  have hy := hF.2.2.2.2.2.2.2.1 θ
  have hp := setup_wallProfiles hd
  have hδ := deltaBase_pos hp (setup_index_bounds hd j).1 hy.1
  have hη := deltaFiber_pos hp (setup_index_bounds hd j).2 hy.2
  have hδlog := Real.log_nonpos hδ.le (deltaBase_le_one hp j (F.f (circlePoint θ)).1)
  have hηlog := Real.log_nonpos hη.le (deltaFiber_le_one hp j (F.f (circlePoint θ)))
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hJ : 0 < (j + 3 : ℝ) := by positivity
  have hClog := Real.log_nonneg (hk.2.2.2.1 j).1
  have hjlog : 0 ≤ (k.dampingPower : ℝ) * Real.log (j + 3) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have hBlog : 0 ≤ (k.dampingPower : ℝ) * Real.log (1 + d.B j) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [(setup_index_bounds hd j).2]))
  have hfiber := mul_nonneg (((hk.2.2.2.1 j).2.2.2.2.1 (F.f (circlePoint θ))).1)
    (add_nonneg (add_nonneg hClog hjlog) hBlog)
  have heq := clockWeightRaw_neg_log (k := k) (a := a) hd hF θ
  rw [hχ, one_mul, wallPower, Real.log_pow, wallProduct, Real.log_mul hδ.ne' hη.ne'] at heq
  have hbase := mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℝ) ≤ 4 * (a : ℝ) - 3 from sub_nonneg.mpr (by exact_mod_cast ha)) hδlog
  have hf := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℝ) ≤ 4 * (a : ℝ) by positivity) hηlog
  have hraw := clockWeightRaw_pos (k := k) (a := a) hd hF θ
  have he : 0 < Real.exp (d.rho (F.f (circlePoint θ)).1 (discTime F (circlePoint θ))) := Real.exp_pos _
  apply (Real.log_le_log_iff (mul_pos (mul_pos hraw he) (inv_pos.mpr (pow_pos hδ 3)))
    (inv_pos.mpr (pow_pos hJ k.dampingPower))).mp
  rw [Real.log_mul (mul_pos hraw he).ne' (inv_pos.mpr (pow_pos hδ 3)).ne',
    Real.log_mul hraw.ne' he.ne', Real.log_exp]
  simp only [Real.log_inv, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [heq, hbase, hf, hfiber]

theorem clockRaw_fiber_damping {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) {j a : ℕ}
    (ha : k.fiberPower ≤ 4 * a) (hc : k.fiberPower ≤ k.dampingPower)
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (θ : ℝ)
    (hχ : clockFiberCutoff d k j (F.f (circlePoint θ)) = 1) :
    clockWeightRaw d k j a F θ * k.fiberCoefficient j * (1 + d.B j) ^ k.fiberPower *
      (wallProduct d j (F.f (circlePoint θ)) ^ k.fiberPower)⁻¹ ≤
        ((j + 3 : ℝ) ^ k.dampingPower)⁻¹ := by
  have hW := admissible_wallProduct_bounds hd hF θ
  have hWlog := Real.log_nonpos hW.1.le hW.2
  have hR : 0 < 1 + d.B j := by linarith [(setup_index_bounds hd j).2]
  have hRlog : 0 ≤ Real.log (1 + d.B j) :=
    Real.log_nonneg (by linarith [(setup_index_bounds hd j).2])
  have hJ : 0 < (j + 3 : ℝ) := by positivity
  have hC : 0 < k.fiberCoefficient j := lt_of_lt_of_le zero_lt_one (hk.2.2.2.1 j).1
  have hρ := setup_rho_nonneg hd (F.f (circlePoint θ)).1
    (admissible_discTime_mem hF (circlePoint_mem_closedBall θ)).1.le
  have hjlog : 0 ≤ (k.dampingPower : ℝ) * Real.log (j + 3) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith))
  have hbase := mul_nonneg (((hk.2.2.2.1 j).2.2.1 (F.f (circlePoint θ)).1).1)
    (add_nonneg hρ hjlog)
  have heq := clockWeightRaw_neg_log (k := k) (a := a) hd hF θ
  rw [hχ, one_mul, wallPower, Real.log_pow] at heq
  have hwall := mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℝ) ≤ 4 * (a : ℝ) - k.fiberPower from sub_nonneg.mpr (by exact_mod_cast ha)) hWlog
  have hradius := mul_nonpos_of_nonpos_of_nonneg
    (show (k.fiberPower : ℝ) - k.dampingPower ≤ 0 from sub_nonpos.mpr (by exact_mod_cast hc)) hRlog
  have hraw := clockWeightRaw_pos (k := k) (a := a) hd hF θ
  apply (Real.log_le_log_iff (mul_pos (mul_pos (mul_pos hraw hC) (pow_pos hR k.fiberPower))
    (inv_pos.mpr (pow_pos hW.1 k.fiberPower))) (inv_pos.mpr (pow_pos hJ k.dampingPower))).mp
  rw [Real.log_mul (mul_pos (mul_pos hraw hC) (pow_pos hR k.fiberPower)).ne'
      (inv_pos.mpr (pow_pos hW.1 k.fiberPower)).ne',
    Real.log_mul (mul_pos hraw hC).ne' (pow_pos hR k.fiberPower).ne',
    Real.log_mul hraw.ne' hC.ne']
  simp only [Real.log_inv, Real.log_pow]
  nlinarith only [heq, hwall, hradius, hbase]

end Yau.Blueprint.V04Proof
