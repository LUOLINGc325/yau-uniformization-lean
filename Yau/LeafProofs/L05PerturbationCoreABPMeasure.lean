import Yau.LeafProofs.L05ABP

noncomputable section

open MeasureTheory Set
open scoped Topology Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perturbCoreABPUnitVolume (n : ℕ) : ℝ := (volume (unitOpen n)).toReal

theorem perturb_core_abp_unit_volume_eq (n : ℕ) :
    volume (unitOpen n)=volume (Metric.ball (0 : Space n) 1) := by
  rw [unitOpen,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ioo]
  norm_num

theorem perturb_core_abp_unit_measure_ne_top (n : ℕ) : volume (unitOpen n) ≠ ⊤ := by
  rw [perturb_core_abp_unit_volume_eq]
  exact ne_of_lt measure_ball_lt_top

theorem perturb_core_abp_unit_volume_pos (n : ℕ) : 0 < perturbCoreABPUnitVolume n := by
  unfold perturbCoreABPUnitVolume
  apply ENNReal.toReal_pos _ (perturb_core_abp_unit_measure_ne_top n)
  rw [perturb_core_abp_unit_volume_eq]
  exact ne_of_gt (Metric.measure_ball_pos volume (0 : Space n) (by norm_num : (0:ℝ) < 1))

theorem perturb_core_abp_constant_integrable (n : ℕ) (k : ℝ) :
    IntegrableOn (fun _ : Point n => (max k 0)^(2*n+1)) (unitOpen n) :=
  integrableOn_const (perturb_core_abp_unit_measure_ne_top n)

theorem perturb_core_abp_constant_integral (n : ℕ) {k : ℝ} (hk : 0 ≤ k) :
    (∫ _z in unitOpen n, (max k 0)^(2*n+1))=perturbCoreABPUnitVolume n*k^(2*n+1) := by
  rw [max_eq_left hk,setIntegral_const,smul_eq_mul]
  rfl

theorem perturb_core_abp_constant_root (n : ℕ) {k : ℝ} (hk : 0 ≤ k) :
    (∫ _z in unitOpen n, (max k 0)^(2*n+1))^(1/((2*n+1 : ℕ):ℝ))=
      k*(perturbCoreABPUnitVolume n)^(1/((2*n+1 : ℕ):ℝ)) := by
  rw [perturb_core_abp_constant_integral n hk,
    Real.mul_rpow (perturb_core_abp_unit_volume_pos n).le (pow_nonneg hk _),one_div,
    Real.pow_rpow_inv_natCast hk (by omega)]
  ring

end Yau.LeafProofs.L05Aux
