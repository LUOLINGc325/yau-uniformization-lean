import Yau.Proofs.C04BoundedGeometryChartsCurvatureForms

/-! A finite basis detects qualitative smoothness of vector-valued multilinear forms. -/

noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n r : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

def vectorTensorEvalMap : ((Fin r → RIdx n) → ComplexVector n) →L[ℝ]
    ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexVector n) (ComplexVector n) :=
  ∑ idx : Fin r → RIdx n,
    ((ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin r => ComplexVector n) (ComplexVector n))
      (tensorMonomial idx)).comp (ContinuousLinearMap.proj idx)

theorem vectorTensorEvalMap_basis (C : (Fin r → RIdx n) → ComplexVector n)
    (idx : Fin r → RIdx n) : vectorTensorEvalMap C (fun j => realVec (idx j)) = C idx := by
  classical
  simp only [vectorTensorEvalMap, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousMultilinearMap.smulRightL_apply,
    ContinuousMultilinearMap.smulRight_apply, tensorMonomial,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, realCoordCLM_apply]
  rw [Finset.sum_eq_single idx]
  · simp [realCoord_realVec]
  · intro a _ hne
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hp : (∏ k : Fin r, realCoord (realVec (idx k)) (a k)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [realCoord_realVec, hj, Ne.symm hj]
    rw [hp, zero_smul]
  · simp

theorem vectorTensorEvalMap_coefficients
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexVector n) (ComplexVector n)) :
    vectorTensorEvalMap (fun idx => T (fun j => realVec (idx j))) = T := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin r => realVec_basis n)
  intro idx
  change vectorTensorEvalMap (fun idx => T (fun j => realVec (idx j)))
    (fun j => realVec_basis n (idx j)) = T (fun j => realVec_basis n (idx j))
  simpa only [realVec_basis_apply] using vectorTensorEvalMap_basis (fun idx => T (fun j => realVec (idx j))) idx

theorem vectorForm_smooth_of_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexVector n) (ComplexVector n))
    (hF : ∀ idx : Fin r → RIdx n, ContDiff ℝ ∞ (fun x => F x (fun j => realVec (idx j)))) :
    ContDiff ℝ ∞ F := by
  have H := vectorTensorEvalMap.contDiff.comp (contDiff_pi.mpr hF)
  convert H using 1
  funext x
  exact (vectorTensorEvalMap_coefficients (F x)).symm

end Yau.Proofs.C04ChartsAux
