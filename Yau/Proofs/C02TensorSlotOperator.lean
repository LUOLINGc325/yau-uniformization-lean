import Yau.Proofs.C02TensorMetricDual

/-! Insertion of one endomorphism into a covariant tensor slot, bundled
as a bilinear contraction of operator norm at most one. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℕ}

local instance slot_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance slot_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance slot_tensor_group (k : ℕ) : NormedAddCommGroup (HomogeneousTensor E k) := inferInstance
local instance slot_tensor_space (k : ℕ) : NormedSpace ℝ (HomogeneousTensor E k) := inferInstance
local instance slot_linear_group (k : ℕ) : NormedAddCommGroup (E →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance slot_linear_space (k : ℕ) : NormedSpace ℝ (E →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance slot_insert_group (k : ℕ) : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance slot_insert_space (k : ℕ) : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance slot_mixed_group (k : ℕ) : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance slot_mixed_space (k : ℕ) : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] HomogeneousTensor E k) := inferInstance

def tensorSlotOperator (s : Fin (r + 1)) :
    HomogeneousTensor E (r + 1) →L[ℝ] (E →L[ℝ] E) →L[ℝ] HomogeneousTensor E (r + 1) :=
  let c := ContinuousMultilinearMap.curryMidEquiv ℝ (fun _ : Fin (r + 1) => E) ℝ s
  let cL := c.toContinuousLinearEquiv.toContinuousLinearMap
  let uL := c.symm.toContinuousLinearEquiv.toContinuousLinearMap
  ((ContinuousLinearMap.compL ℝ (E →L[ℝ] E) (E →L[ℝ] HomogeneousTensor E r)
    (HomogeneousTensor E (r + 1))) uL).comp
      ((ContinuousLinearMap.compL ℝ E E (HomogeneousTensor E r)).comp cL)

theorem tensorSlotOperator_apply (s : Fin (r + 1))
    (T : HomogeneousTensor E (r + 1)) (B : E →L[ℝ] E) (V : Fin (r + 1) → E) :
    tensorSlotOperator E s T B V = T (Function.update V s (B (V s))) := by
  change T (s.insertNth (B (V s)) (s.removeNth V)) = _
  rw [Fin.insertNth_removeNth]

theorem tensorSlotOperator_norm_le_one (s : Fin (r + 1)) : ‖tensorSlotOperator E s‖ ≤ 1 := by
  apply (tensorSlotOperator E s).opNorm_le_bound (by norm_num)
  intro T
  simp only [one_mul]
  apply (tensorSlotOperator E s T).opNorm_le_bound (norm_nonneg T)
  intro B
  let c := ContinuousMultilinearMap.curryMidEquiv ℝ (fun _ : Fin (r + 1) => E) ℝ s
  change ‖c.symm ((c T).comp B)‖ ≤ _
  rw [c.symm.norm_map]
  exact ((c T).opNorm_comp_le B).trans_eq (by rw [c.norm_map])

end Yau.Blueprint.C02Proof
