import Yau.Proofs.D06HardyShift

/-! The actual holomorphic power-series realization of Hardy coefficients. -/

open scoped lp

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def hardySeries (a : HardySeq r) (j : Fin r) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => a (n, j))

def hardyEvalEntry (a : HardySeq r) (j : Fin r) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (fun n => a (n, j))

def hardyEval (a : HardySeq r) (z : ℂ) : EuclideanSpace ℂ (Fin r) :=
  WithLp.toLp 2 (fun j => hardyEvalEntry a j z)

theorem hardySeries_radius (a : HardySeq r) (j : Fin r) :
    (1 : ENNReal) ≤ (hardySeries a j).radius := by
  apply (hardySeries a j).le_radius_of_bound (r := 1) ‖a‖
  intro n
  simpa only [hardySeries, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one,
    one_pow, mul_one] using lp.norm_apply_le_norm (p := 2) (by norm_num) a (n, j)

theorem hardyEvalEntry_differentiableOn (a : HardySeq r) (j : Fin r) :
    DifferentiableOn ℂ (hardyEvalEntry a j) (Metric.ball 0 1) := by
  intro z hz
  have hdist : dist z 0 < 1 := hz
  have he : edist z 0 < (1 : ENNReal) := by
    rw [edist_dist]
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hdist
  have hz' : z ∈ Metric.eball (0 : ℂ) (hardySeries a j).radius :=
    he.trans_le (hardySeries_radius a j)
  exact ((hardySeries a j).analyticOnNhd z hz').differentiableAt.differentiableWithinAt

theorem hardyEvalEntry_eq_tsum (a : HardySeq r) (j : Fin r) (z : ℂ) :
    hardyEvalEntry a j z = ∑' n : ℕ, z ^ n * a (n, j) := by
  rw [hardyEvalEntry, FormalMultilinearSeries.ofScalars_sum_eq]
  apply tsum_congr
  intro n
  exact mul_comm _ _

theorem hardyEval_summable (a : HardySeq r) (j : Fin r) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => z ^ n * a (n, j)) := by
  have hmajor : Summable (fun n : ℕ => ‖z‖ ^ n * ‖a‖) :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right ‖a‖
  apply hmajor.of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (p := 2) (by norm_num) a (n, j))
    (pow_nonneg (norm_nonneg _) _)

@[simp] theorem hardyEvalEntry_zero (a : HardySeq r) (j : Fin r) :
    hardyEvalEntry a j 0 = a (0, j) := by
  simp only [hardyEvalEntry, FormalMultilinearSeries.ofScalarsSum_zero, smul_eq_mul, mul_one]

theorem hardyEvalEntry_add (a b : HardySeq r) (j : Fin r) (z : ℂ) (hz : ‖z‖ < 1) :
    hardyEvalEntry (a + b) j z = hardyEvalEntry a j z + hardyEvalEntry b j z := by
  simp only [hardyEvalEntry_eq_tsum, lp.coeFn_add, Pi.add_apply, mul_add]
  exact (Summable.tsum_add (hardyEval_summable a j z hz) (hardyEval_summable b j z hz))

theorem hardyEvalEntry_smul (c : ℂ) (a : HardySeq r) (j : Fin r) (z : ℂ) :
    hardyEvalEntry (c • a) j z = c * hardyEvalEntry a j z := by
  simp only [hardyEvalEntry_eq_tsum, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (z ^ _) c]
  exact tsum_mul_left

theorem hardyEvalEntry_shift (a : HardySeq r) (j : Fin r) (z : ℂ) (hz : ‖z‖ < 1) :
    hardyEvalEntry (hardyShift a) j z = z * hardyEvalEntry a j z := by
  rw [hardyEvalEntry_eq_tsum,
    (hardyEval_summable (hardyShift a) j z hz).tsum_eq_zero_add]
  simp only [hardyShift_zero, mul_zero, zero_add, hardyShift_succ, pow_succ]
  rw [hardyEvalEntry_eq_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

end Yau.NodeProofs.D06Aux
