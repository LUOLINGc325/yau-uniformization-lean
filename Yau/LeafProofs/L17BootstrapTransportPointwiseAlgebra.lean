import Yau.LeafProofs.L17BootstrapTransportProfiles

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17SchauderAux
variable {n : ℕ}

theorem gradient_precompose_sub_norm_le (p q : D1 n)
    (J : ComplexVector n →L[ℝ] ComplexVector n) :
    ‖q.comp J-p‖ ≤ ‖q-p‖*‖J‖+‖p‖*‖J-ContinuousLinearMap.id ℝ (ComplexVector n)‖ := by
  have hEq : q.comp J-p=(q-p).comp J+p.comp (J-ContinuousLinearMap.id ℝ (ComplexVector n)) := by
    ext a
    simp only [_root_.sub_apply,_root_.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,map_sub]
    abel
  rw [hEq]
  exact (norm_add_le _ _).trans (add_le_add ((q-p).opNorm_comp_le J)
    (p.opNorm_comp_le (J-ContinuousLinearMap.id ℝ (ComplexVector n))))

def precomposeHessian (J K : ComplexVector n →L[ℝ] ComplexVector n) (Q : D2 n) : D2 n :=
  ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ).flip K).comp (Q.comp J)

theorem precomposeHessian_apply (J K : ComplexVector n →L[ℝ] ComplexVector n) (Q : D2 n)
    (a b : ComplexVector n) : precomposeHessian J K Q a b=Q (J a) (K b) := rfl

theorem precomposeHessian_norm_le (J K : ComplexVector n →L[ℝ] ComplexVector n) (Q : D2 n) :
    ‖precomposeHessian J K Q‖ ≤ ‖Q‖*‖J‖*‖K‖ := by
  have hPost : ‖(ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ).flip K‖ ≤ ‖K‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K)
    intro p
    exact (p.opNorm_comp_le K).trans_eq (mul_comm _ _)
  apply (((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ).flip K).opNorm_comp_le (Q.comp J)).trans
  exact (mul_le_mul hPost (Q.opNorm_comp_le J) (norm_nonneg _) (norm_nonneg K)).trans_eq (by ring)

theorem precomposeHessian_sub_identity (J : ComplexVector n →L[ℝ] ComplexVector n) (Q R : D2 n) :
    precomposeHessian J J R-Q=
      precomposeHessian J J (R-Q)+
      precomposeHessian (J-ContinuousLinearMap.id ℝ (ComplexVector n)) J Q+
      precomposeHessian (ContinuousLinearMap.id ℝ (ComplexVector n))
        (J-ContinuousLinearMap.id ℝ (ComplexVector n)) Q := by
  ext a b
  simp only [precomposeHessian_apply,_root_.sub_apply,_root_.add_apply,
    ContinuousLinearMap.id_apply,map_sub]
  abel

theorem precomposeHessian_sub_norm_le (J : ComplexVector n →L[ℝ] ComplexVector n) (Q R : D2 n) :
    ‖precomposeHessian J J R-Q‖ ≤
      ‖R-Q‖*‖J‖^2+‖Q‖*‖J-ContinuousLinearMap.id ℝ (ComplexVector n)‖*(‖J‖+1) := by
  rw [precomposeHessian_sub_identity]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  have hId : ‖ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc
    _ ≤ (‖R-Q‖*‖J‖*‖J‖+‖Q‖*‖J-ContinuousLinearMap.id ℝ (ComplexVector n)‖*‖J‖)+
        ‖Q‖*1*‖J-ContinuousLinearMap.id ℝ (ComplexVector n)‖ := by
      apply add_le_add
      · exact add_le_add (precomposeHessian_norm_le J J (R-Q))
          (precomposeHessian_norm_le (J-ContinuousLinearMap.id ℝ (ComplexVector n)) J Q)
      · exact (precomposeHessian_norm_le (ContinuousLinearMap.id ℝ (ComplexVector n))
          (J-ContinuousLinearMap.id ℝ (ComplexVector n)) Q).trans (by gcongr)
    _ = _ := by ring

end Yau.LeafProofs.L17BootstrapTransportAux
