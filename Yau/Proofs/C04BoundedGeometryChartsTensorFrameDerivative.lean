import Yau.Proofs.C04BoundedGeometryChartsFrameConnection
import Yau.LeafProofs.L23TensorPullback

/-! The derivative of an actual tensor evaluated in a moving frame. -/

noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n r : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem tensorForm_movingFrame_fderiv (F : ComplexVector n → RealTensorForm n r)
    (Z : ComplexVector n → ComplexVector n)
    (P : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (v u : ComplexVector n) (V : Fin r → ComplexVector n)
    (hF : DifferentiableAt ℝ F (Z v)) (hZ : DifferentiableAt ℝ Z v)
    (hP : DifferentiableAt ℝ P v) :
    fderiv ℝ (fun x => (F (Z x)).compContinuousLinearMap (fun _ : Fin r => P x)) v u V =
      (fderiv ℝ F (Z v) (fderiv ℝ Z v u)) (fun j => P v (V j)) +
        ∑ s : Fin r, F (Z v) (Function.update (fun j => P v (V j)) s (fderiv ℝ P v u (V s))) := by
  have hcomp : DifferentiableAt ℝ (fun x => F (Z x)) v := hF.comp v hZ
  have hd := fderiv_continuousMultilinearMapCompContinuousLinearMap
    (f := fun x => F (Z x)) (g := fun (_ : Fin r) x => P x) hcomp (fun _ => hP)
  have he := congrArg (fun L : ComplexVector n →L[ℝ] RealTensorForm n r => L u V) hd
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply,
    ContinuousLinearMap.pi_apply] at he
  have hcompD : fderiv ℝ (fun x => F (Z x)) v = (fderiv ℝ F (Z v)).comp (fderiv ℝ Z v) := by
    simpa only [Function.comp_def] using fderiv_comp v hF hZ
  rw [hcompD] at he
  have hmaps (s : Fin r) :
      (fun j => Function.update (fun _ : Fin r => P v) s (fderiv ℝ P v u) j (V j)) =
        Function.update (fun j => P v (V j)) s (fderiv ℝ P v u (V s)) :=
    apply_update_linearMaps (fun _ => P v) (fun _ => fderiv ℝ P v u) V s
  simpa only [ContinuousLinearMap.comp_apply, hmaps] using he

theorem tensorForm_movingFrame_covariantD
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (F : ComplexVector n → RealTensorForm n r) (N : RealTensorForm n (r + 1))
    (Z : ComplexVector n → ComplexVector n)
    (P : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (v u : ComplexVector n) (V : Fin r → ComplexVector n)
    (hF : DifferentiableAt ℝ F (Z v)) (hZ : DifferentiableAt ℝ Z v)
    (hP : DifferentiableAt ℝ P v) (hiP : (P v).IsInvertible)
    (hN : ∀ a, N.curryLeft a = fderiv ℝ F (Z v) a - tensorConnectionForm (Γ (Z v)) (F (Z v)) a) :
    fderiv ℝ (fun x => (F (Z x)).compContinuousLinearMap (fun _ : Fin r => P x)) v u V =
      N (Fin.cons (fderiv ℝ Z v u) (fun j => P v (V j))) +
        ∑ s : Fin r, F (Z v) (Function.update (fun j => P v (V j)) s
          (P v (coordinateFrameConnection Γ Z P v u (V s)))) := by
  rw [tensorForm_movingFrame_fderiv F Z P v u V hF hZ hP]
  have hd := congrArg (fun T : RealTensorForm n r => T (fun j => P v (V j)))
    (hN (fderiv ℝ Z v u))
  simp only [ContinuousMultilinearMap.curryLeft_apply, sub_apply, tensorConnectionForm_apply] at hd
  have hDF : (fderiv ℝ F (Z v) (fderiv ℝ Z v u)) (fun j => P v (V j)) =
      N (Fin.cons (fderiv ℝ Z v u) (fun j => P v (V j))) +
        ∑ s : Fin r, F (Z v) (Function.update (fun j => P v (V j)) s
          (Γ (Z v) (fderiv ℝ Z v u) (P v (V s)))) := by linarith
  rw [hDF, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [← (F (Z v)).map_update_add]
  rw [coordinateFrameConnection_equation Γ Z P v u (V s) hiP, add_comm]

end Yau.Proofs.C04ChartsAux
