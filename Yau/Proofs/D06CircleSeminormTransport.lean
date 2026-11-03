import Yau.Proofs.D06CircleDifferences
import Yau.Proofs.D06AveragedSeminorm

/-! Exact normalized Haar-circle difference bounds transport to the original
real-angle ENNReal half-Sobolev seminorm, including its zero denominator. -/

open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}

theorem circleDifference_congr_ae
    (A B : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (hAB : A =ᵐ[hardyCircleMeasure] B)
    (θ : HardyCircle) : circleDifference A θ = circleDifference B θ := by
  have hθ := (measurePreserving_add_right hardyCircleMeasure θ).quasiMeasurePreserving.ae hAB
  apply integral_congr_ae
  filter_upwards [hAB, hθ] with t ht htθ
  rw [ht, htθ]

theorem angularDifference_circle_coe (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (θ : ℝ) :
    angularDifference (fun t : ℝ => A (t : HardyCircle)) θ =
      (2 * Real.pi) * circleDifference A (θ : HardyCircle) := by
  rw [angularDifference, integral_Icc_eq_integral_Ioc]
  have h := AddCircle.integral_preimage (2 * Real.pi) 0
    (fun t : HardyCircle => frobSq (A (t + (θ : HardyCircle)) - A t))
  have heq : (fun t : ℝ => frobSq (A ((t + θ : ℝ) : HardyCircle) - A (t : HardyCircle))) =
      fun t : ℝ => frobSq (A ((t : HardyCircle) + (θ : HardyCircle)) - A (t : HardyCircle)) := by
    funext t
    rw [QuotientAddGroup.mk_add]
  rw [heq]
  simp only [zero_add] at h
  rw [h, AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), smul_eq_mul]
  rfl

theorem halfSobolevSq_of_circleDifference_bound
    (A B : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (hA : Continuous A) (hB : Continuous B)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ θ, circleDifference A θ ≤ C * circleDifference B θ) :
    halfSobolevSq (fun t : ℝ => A (t : HardyCircle)) ≤
      ENNReal.ofReal C * halfSobolevSq (fun t : ℝ => B (t : HardyCircle)) := by
  apply halfSobolevSq_le_of_angularDifference_le _ _
    (hA.comp (AddCircle.continuous_mk' _)) (hB.comp (AddCircle.continuous_mk' _)) C hC
  intro θ
  change angularDifference (fun t : ℝ => A (t : HardyCircle)) θ ≤
    C * angularDifference (fun t : ℝ => B (t : HardyCircle)) θ
  rw [angularDifference_circle_coe, angularDifference_circle_coe]
  have h := mul_le_mul_of_nonneg_left (hbound (θ : HardyCircle)) (by positivity : 0 ≤ 2 * Real.pi)
  simpa only [mul_assoc, mul_left_comm C] using h

end Yau.NodeProofs.D06Aux
