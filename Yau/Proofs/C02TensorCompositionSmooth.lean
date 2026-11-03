import Yau.LeafProofs.L23TensorMultilinear

/-! Smooth finite tensor composition, established from its actual coefficients
to avoid ambiguity between inherited operator-space module instances. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n r : ℕ} {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem contDiffOn_tensor_composition {O : Set D} {A : D → CovTensor n r}
    {Q : D → ComplexVector n →L[ℝ] ComplexVector n}
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun x => A x v) O) (hQ : ContDiffOn ℝ ∞ Q O) :
    ContDiffOn ℝ ∞ (fun x => (tensorEvalCLM (A x)).compContinuousLinearMap
      (fun _ : Fin r => Q x)) O := by
  let T := fun x => (tensorEvalCLM (A x)).compContinuousLinearMap (fun _ : Fin r => Q x)
  let C : D → CovTensor n r := fun x v => T x (fun i => realVec (v i))
  have hC : ∀ v, ContDiffOn ℝ ∞ (fun x => C x v) O := by
    intro v
    simp only [C, T, ContinuousMultilinearMap.compContinuousLinearMap_apply, tensorEvalCLM_apply]
    apply ContDiffOn.sum
    intro w hw
    apply (hA w).mul
    apply contDiffOn_prod
    intro i hi
    have hQi : ContDiffOn ℝ ∞ (fun x => Q x (realVec (v i))) O :=
      hQ.clm_apply (contDiffOn_const (c := realVec (v i)))
    simpa only [Function.comp_def, realCoordCLM_apply] using
      (realCoordCLM (w i)).contDiff.comp_contDiffOn hQi
  have hEval := tensorEvalCLM_contDiffOn C hC
  apply (contDiffOn_congr (fun x hx => (tensorEvalCLM_coefficients (T x)).symm)).mpr
  exact hEval

end Yau.Blueprint.C02Proof
