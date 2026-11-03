import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
open scoped InnerProductSpace
namespace Yau.Blueprint.C02Proof
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance gram_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance gram_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance gram_dual_group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gram_dual_space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance gram_form_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance gram_form_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def gramOperator : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  ((innerSL ℝ).precompR E).precompL E

theorem gramOperator_apply (B C : E →L[ℝ] E) (u v : E) :
    gramOperator E B C u v = ⟪B u, C v⟫_ℝ := rfl

theorem gramOperator_norm_le_one : ‖gramOperator E‖ ≤ 1 := by
  apply (gramOperator E).opNorm_le_bound (by norm_num)
  intro B
  simp only [one_mul]
  apply (gramOperator E B).opNorm_le_bound (norm_nonneg B)
  intro C
  apply (gramOperator E B C).opNorm_le_bound (by positivity)
  intro u
  apply (gramOperator E B C u).opNorm_le_bound (by positivity)
  intro v
  change ‖⟪B u, C v⟫_ℝ‖ ≤ _
  calc
    _ ≤ ‖B u‖ * ‖C v‖ := norm_inner_le_norm _ _
    _ ≤ (‖B‖ * ‖u‖) * (‖C‖ * ‖v‖) := mul_le_mul (B.le_opNorm u) (C.le_opNorm v)
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end Yau.Blueprint.C02Proof
