import Yau.Proofs.C02TensorSlotOperator

noncomputable section
namespace Yau.Blueprint.C02Proof
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance slotc_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance slotc_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance slotc_tensor_group (k : ℕ) : NormedAddCommGroup (HomogeneousTensor E k) := inferInstance
local instance slotc_tensor_space (k : ℕ) : NormedSpace ℝ (HomogeneousTensor E k) := inferInstance
local instance slotc_linear_group (k : ℕ) : NormedAddCommGroup (E →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance slotc_linear_space (k : ℕ) : NormedSpace ℝ (E →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance slotc_insert_group (k : ℕ) : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance slotc_insert_space (k : ℕ) : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] HomogeneousTensor E k) := inferInstance

local instance slotc_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance slotc_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance slotc_outer_group (k : ℕ) : NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance slotc_outer_space (k : ℕ) : NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] HomogeneousTensor E k) := inferInstance

def tensorSlotOperatorAll : {r : ℕ} → Fin r → HomogeneousTensor E r →L[ℝ]
    (E →L[ℝ] E) →L[ℝ] HomogeneousTensor E r
  | 0, s => Fin.elim0 s
  | _ + 1, s => tensorSlotOperator E s

theorem tensorSlotOperatorAll_apply {r : ℕ} (s : Fin r)
    (T : HomogeneousTensor E r) (B : E →L[ℝ] E) (V : Fin r → E) :
    tensorSlotOperatorAll E s T B V = T (Function.update V s (B (V s))) := by
  cases r with
  | zero => exact Fin.elim0 s
  | succ r => exact tensorSlotOperator_apply E s T B V

theorem tensorSlotOperatorAll_norm_le_one {r : ℕ} (s : Fin r) : ‖tensorSlotOperatorAll E s‖ ≤ 1 := by
  cases r with
  | zero => exact Fin.elim0 s
  | succ r => exact tensorSlotOperator_norm_le_one E s

def tensorSlotConnectionOperator {r : ℕ} (s : Fin r) : HomogeneousTensor E r →L[ℝ]
    (E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] HomogeneousTensor E r :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (HomogeneousTensor E r)).comp (tensorSlotOperatorAll E s)

theorem tensorSlotConnectionOperator_apply {r : ℕ} (s : Fin r)
    (T : HomogeneousTensor E r) (A : E →L[ℝ] E →L[ℝ] E) (u : E) (V : Fin r → E) :
    tensorSlotConnectionOperator E s T A u V = T (Function.update V s (A u (V s))) :=
  tensorSlotOperatorAll_apply E s T (A u) V

theorem tensorSlotConnectionOperator_norm_le_one {r : ℕ} (s : Fin r) :
    ‖tensorSlotConnectionOperator E s‖ ≤ 1 := by
  apply (tensorSlotConnectionOperator E s).opNorm_le_bound (by norm_num)
  intro T
  simp only [one_mul]
  apply (tensorSlotConnectionOperator E s T).opNorm_le_bound (norm_nonneg T)
  intro A
  change ‖(tensorSlotOperatorAll E s T).comp A‖ ≤ _
  have hT : ‖tensorSlotOperatorAll E s T‖ ≤ ‖T‖ :=
    ((tensorSlotOperatorAll E s).le_opNorm T).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (tensorSlotOperatorAll_norm_le_one E s) (norm_nonneg T))
  exact ((tensorSlotOperatorAll E s T).opNorm_comp_le A).trans
    (mul_le_mul_of_nonneg_right hT (norm_nonneg A))

end Yau.Blueprint.C02Proof
