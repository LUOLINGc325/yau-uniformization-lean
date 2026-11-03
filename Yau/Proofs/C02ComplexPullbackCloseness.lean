import Yau.Proofs.C02ComplexPullbackOperator
import Yau.Proofs.C02OperatorSmoothInverse

noncomputable section
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ}

theorem complexPullback_sub_standard_norm_le
    (B : ComplexVector n →L[ℝ] ComplexVector n)
    (hB : ‖B - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4) :
    ‖B.inverse.comp ((complexStructureCLM n).comp B) - complexStructureCLM n‖ ≤
      4 * ‖B - ContinuousLinearMap.id ℝ (ComplexVector n)‖ := by
  let I := complexStructureCLM n
  let D := B - ContinuousLinearMap.id ℝ (ComplexVector n)
  have hCB := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => fun z => L z)
    (actual_inverse_identities_of_close_identity B hB).1
  have hEq : B.inverse.comp (I.comp B) - I = B.inverse.comp (I.comp D - D.comp I) := by
    apply ContinuousLinearMap.ext
    intro z
    have hCz : B.inverse (B (I z)) = I z := congrFun hCB (I z)
    change B.inverse (I (B z)) - I z = _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub, D]
    rw [hCz]
    abel
  rw [hEq]
  calc
    _ ≤ ‖B.inverse‖ * (‖I.comp D‖ + ‖D.comp I‖) :=
      (B.inverse.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
    _ ≤ 2 * (1 * ‖D‖ + ‖D‖ * 1) := by
      gcongr
      · exact norm_actual_inverse_of_close_identity B hB
      · exact (I.opNorm_comp_le D).trans (mul_le_mul_of_nonneg_right
          (complexStructureCLM_norm_le_one n) (norm_nonneg _))
      · exact (D.opNorm_comp_le I).trans (mul_le_mul_of_nonneg_left
          (complexStructureCLM_norm_le_one n) (norm_nonneg _))
    _ = _ := by ring

end Yau.Blueprint.C02Proof
