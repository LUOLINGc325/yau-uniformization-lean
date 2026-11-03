import Yau.LeafProofs.L23JetNaturality

/-! Simultaneous slot permutation commutes with the actual tensor pullback. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ}

theorem tensorEvalCLM_permute (e : Equiv.Perm (Fin r)) (A : CovTensor n r) :
    tensorEvalCLM (fun v => A (v ∘ e))=
      ContinuousMultilinearMap.domDomCongr e (tensorEvalCLM A) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin r => L12Aux.realVec_basis n)
  intro v
  change tensorEvalCLM (fun v => A (v ∘ e)) (fun j => L12Aux.realVec_basis n (v j))=_
  simp only [L12Aux.realVec_basis_apply,ContinuousMultilinearMap.domDomCongr_apply]
  change tensorEvalCLM (fun v => A (v ∘ e)) (fun j => realVec (v j))=
    tensorEvalCLM A (fun j => realVec ((v ∘ e) j))
  rw [tensorEvalCLM_basis,tensorEvalCLM_basis]

theorem tensorPermute_comp (e : Equiv.Perm (Fin r)) (T : RealTensorForm n r)
    (J : ComplexVector n →L[ℝ] ComplexVector n) :
    ContinuousMultilinearMap.domDomCongr e
      (T.compContinuousLinearMap (fun _ : Fin r => J))=
      (ContinuousMultilinearMap.domDomCongr e T).compContinuousLinearMap
        (fun _ : Fin r => J) := by
  ext V
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem tensorFrameTransform_permute (e : Equiv.Perm (Fin r))
    (J : ComplexVector n →L[ℝ] ComplexVector n) (A : CovTensor n r) :
    (fun v => tensorFrameTransform (realLinearMatrix J) A (v ∘ e))=
      tensorFrameTransform (realLinearMatrix J) (fun v => A (v ∘ e)) := by
  apply tensorEvalCLM_injective
  rw [tensorEvalCLM_permute,tensorEvalCLM_frameTransform,tensorPermute_comp,
    tensorEvalCLM_frameTransform,tensorEvalCLM_permute]

end Yau.LeafProofs.L23Aux
