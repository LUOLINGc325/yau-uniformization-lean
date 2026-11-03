import Yau.LeafProofs.L23TensorPullback

/-! Differentiation of an actual tensor in a separately varying frame.
The frame is not required to be the Jacobian of the base map. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L23Aux
variable {n r : ℕ}

theorem tensorForm_frame_fderiv (F : ComplexVector n → RealTensorForm n r)
    (f : ComplexVector n → ComplexVector n)
    (Q : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (x u : ComplexVector n) (V : Fin r → ComplexVector n)
    (hF : DifferentiableAt ℝ F (f x)) (hf : DifferentiableAt ℝ f x)
    (hQ : DifferentiableAt ℝ Q x) :
    fderiv ℝ (fun w => (F (f w)).compContinuousLinearMap (fun _ : Fin r => Q w)) x u V =
      (fderiv ℝ F (f x) (fderiv ℝ f x u)) (fun j => Q x (V j)) +
        ∑ s : Fin r, F (f x) (Function.update (fun j => Q x (V j)) s (fderiv ℝ Q x u (V s))) := by
  have hcomp : DifferentiableAt ℝ (fun w => F (f w)) x := hF.comp x hf
  have hd := fderiv_continuousMultilinearMapCompContinuousLinearMap
    (f := fun w => F (f w)) (g := fun (_ : Fin r) w => Q w) hcomp (fun _ => hQ)
  have he := congrArg (fun L : ComplexVector n →L[ℝ] RealTensorForm n r => L u V) hd
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply,
    ContinuousLinearMap.pi_apply] at he
  have hcompD : fderiv ℝ (fun w => F (f w)) x = (fderiv ℝ F (f x)).comp (fderiv ℝ f x) := by
    simpa only [Function.comp_def] using fderiv_comp x hF hf
  rw [hcompD] at he
  have hmaps (s : Fin r) :
      (fun j => Function.update (fun _ : Fin r => Q x) s (fderiv ℝ Q x u) j (V j)) =
        Function.update (fun j => Q x (V j)) s (fderiv ℝ Q x u (V s)) :=
    apply_update_linearMaps (fun _ => Q x) (fun _ => fderiv ℝ Q x u) V s
  simpa only [ContinuousLinearMap.comp_apply, hmaps] using he

end Yau.Blueprint.C02Proof
