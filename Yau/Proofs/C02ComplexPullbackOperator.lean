import Yau.LeafProofs.L12

noncomputable section
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable (n : ℕ)
local instance cp_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance cp_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem complexStructureCLM_norm_le_one : ‖complexStructureCLM n‖ ≤ 1 := by
  apply (complexStructureCLM n).opNorm_le_bound (by norm_num)
  intro z
  change ‖Complex.I • z‖ ≤ 1 * ‖z‖
  simp only [norm_smul, Complex.norm_I, one_mul]
  exact le_rfl

def complexPullbackOperator : (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ]
    (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n)).bilinearComp
    (ContinuousLinearMap.id ℝ (ComplexVector n →L[ℝ] ComplexVector n))
    (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n) (complexStructureCLM n))

theorem complexPullbackOperator_apply (C B : ComplexVector n →L[ℝ] ComplexVector n) :
    complexPullbackOperator n C B = C.comp ((complexStructureCLM n).comp B) := rfl

theorem complexPullbackOperator_norm_le_one : ‖complexPullbackOperator n‖ ≤ 1 := by
  apply (complexPullbackOperator n).opNorm_le_bound (by norm_num)
  intro C
  simp only [one_mul]
  apply (complexPullbackOperator n C).opNorm_le_bound (norm_nonneg C)
  intro B
  rw [complexPullbackOperator_apply]
  calc
    _ ≤ ‖C‖ * (‖complexStructureCLM n‖ * ‖B‖) :=
      (C.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left ((complexStructureCLM n).opNorm_comp_le B) (norm_nonneg C))
    _ ≤ ‖C‖ * (1 * ‖B‖) := by gcongr; exact complexStructureCLM_norm_le_one n
    _ = _ := by rw [one_mul]

end Yau.Blueprint.C02Proof
