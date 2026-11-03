import Yau.Proofs.C02TensorFrameDerivative

/-! Covariant-to-ordinary differentiation in an arbitrary genuine frame.
Connection terms have positive signs after differentiating the frame slots. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n r : ℕ} {M : ComplexManifold n}

theorem tensorGauge_fderiv (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (f : ComplexVector n → ComplexVector n)
    (Q : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (x u : ComplexVector n) (V : Fin r → ComplexVector n)
    (hA : ∀ v, DifferentiableAt ℝ (fun y => A y v) (f x))
    (hf : DifferentiableAt ℝ f x) (hQ : DifferentiableAt ℝ Q x) :
    fderiv ℝ (fun y => (tensorEvalCLM (A (f y))).compContinuousLinearMap
        (fun _ : Fin r => Q y)) x u V =
      tensorEvalCLM (covariantD h c A (f x)) (Fin.cons (fderiv ℝ f x u) (fun i => Q x (V i))) +
        ∑ s : Fin r, tensorEvalCLM (A (f x))
          (Function.update (fun i => Q x (V i)) s
            (fderiv ℝ Q x u (V s) + chartChristoffelBilin h c (f x)
              (fderiv ℝ f x u) (Q x (V s)))) := by
  have hF : DifferentiableAt ℝ (fun y => tensorEvalCLM (A y)) (f x) :=
    tensorEvalCLMMap.differentiableAt.comp (f x) (differentiableAt_pi.mpr hA)
  have hd := tensorForm_frame_fderiv (fun y => tensorEvalCLM (A y)) f Q x u V hF hf hQ
  have hc := congrArg (fun T : RealTensorForm n r => T (fun i => Q x (V i)))
    (tensorEvalCLM_covariantD h c A (f x) (fderiv ℝ f x u) hA)
  change tensorEvalCLM (covariantD h c A (f x)) (Fin.cons (fderiv ℝ f x u) (fun i => Q x (V i))) =
    (fderiv ℝ (fun y => tensorEvalCLM (A y)) (f x) (fderiv ℝ f x u)) (fun i => Q x (V i)) -
      tensorConnectionForm (chartChristoffelBilin h c (f x)) (tensorEvalCLM (A (f x)))
        (fderiv ℝ f x u) (fun i => Q x (V i)) at hc
  rw [tensorConnectionForm_apply] at hc
  have hsum : (∑ s : Fin r, tensorEvalCLM (A (f x))
      (Function.update (fun i => Q x (V i)) s
        (fderiv ℝ Q x u (V s) + chartChristoffelBilin h c (f x)
          (fderiv ℝ f x u) (Q x (V s))))) =
      (∑ s : Fin r, tensorEvalCLM (A (f x))
        (Function.update (fun i => Q x (V i)) s (fderiv ℝ Q x u (V s)))) +
      ∑ s : Fin r, tensorEvalCLM (A (f x))
        (Function.update (fun i => Q x (V i)) s
          (chartChristoffelBilin h c (f x) (fderiv ℝ f x u) (Q x (V s)))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    exact ((tensorEvalCLM (A (f x))).toContinuousLinearMap (fun i => Q x (V i)) s).map_add _ _
  rw [hsum]
  linarith [hd, hc]

end Yau.Blueprint.C02Proof
