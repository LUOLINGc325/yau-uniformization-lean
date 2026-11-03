import Yau.Proofs.C02TensorMetricDual

noncomputable section
namespace Yau.Blueprint.C02Proof
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℕ}
local instance head_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance head_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance head_tensor_group (k : ℕ) : NormedAddCommGroup (HomogeneousTensor E k) := inferInstance
local instance head_tensor_space (k : ℕ) : NormedSpace ℝ (HomogeneousTensor E k) := inferInstance
local instance head_linear_group (k : ℕ) : NormedAddCommGroup (E →L[ℝ] HomogeneousTensor E k) := inferInstance
local instance head_linear_space (k : ℕ) : NormedSpace ℝ (E →L[ℝ] HomogeneousTensor E k) := inferInstance

def tensorHeadOperator : HomogeneousTensor E (r + 1) →L[ℝ]
    (E →L[ℝ] E) →L[ℝ] E →L[ℝ] HomogeneousTensor E r :=
  (ContinuousLinearMap.compL ℝ E E (HomogeneousTensor E r)).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => E) ℝ).toContinuousLinearEquiv.toContinuousLinearMap

theorem tensorHeadOperator_apply (T : HomogeneousTensor E (r + 1))
    (B : E →L[ℝ] E) (u : E) (V : Fin r → E) :
    tensorHeadOperator E T B u V = T (Fin.cons (B u) V) := rfl

theorem tensorHeadOperator_norm_le_one : ‖tensorHeadOperator (r := r) E‖ ≤ 1 := by
  apply (tensorHeadOperator (r := r) E).opNorm_le_bound (by norm_num)
  intro T
  simp only [one_mul]
  apply (tensorHeadOperator E T).opNorm_le_bound (norm_nonneg T)
  intro B
  change ‖T.curryLeft.comp B‖ ≤ _
  exact (T.curryLeft.opNorm_comp_le B).trans_eq (by rw [T.curryLeft_norm])

end Yau.Blueprint.C02Proof
