import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Exact derivative of a frame changed by the derivative of a coordinate map. -/

noncomputable section
open Filter
open scoped Topology
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transformed_frame_fderiv {y ψ : E → E} {Q Q' : E → E →L[ℝ] E} {x : E}
    (hy : DifferentiableAt ℝ y x)
    (hψ : DifferentiableAt ℝ (fderiv ℝ ψ) (y x))
    (hQ : DifferentiableAt ℝ Q x)
    (heq : Q' =ᶠ[𝓝 x] (fun z => (fderiv ℝ ψ (y z)).comp (Q z))) (u z : E) :
    fderiv ℝ Q' x u z =
      fderiv ℝ ψ (y x) (fderiv ℝ Q x u z) +
        fderiv ℝ (fderiv ℝ ψ) (y x) (fderiv ℝ y x u) (Q x z) := by
  have hG : HasFDerivAt (fun z => fderiv ℝ ψ (y z))
      ((fderiv ℝ (fderiv ℝ ψ) (y x)).comp (fderiv ℝ y x)) x :=
    hψ.hasFDerivAt.comp x hy.hasFDerivAt
  have hProd : HasFDerivAt (fun z => (fderiv ℝ ψ (y z)).comp (Q z))
      ((ContinuousLinearMap.compL ℝ E E E (fderiv ℝ ψ (y x))).comp (fderiv ℝ Q x) +
        ((ContinuousLinearMap.compL ℝ E E E).flip (Q x)).comp
          ((fderiv ℝ (fderiv ℝ ψ) (y x)).comp (fderiv ℝ y x))) x :=
    hG.clm_comp hQ.hasFDerivAt
  rw [heq.fderiv_eq, hProd.fderiv]
  rfl

end Yau.Blueprint.C02Proof
