import Yau.Proofs.V03ExteriorTwoForm

/-! Native cyclic evaluation of the exterior derivative of a real
two-form, with all three actual directional derivatives. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem extDeriv_twoForm_cyclic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {z : E} (hΩ : DifferentiableAt ℝ Ω z) (u v w : E) :
    extDeriv Ω z ![u, v, w] =
      fderiv ℝ (fun p => Ω p ![v, w]) z u +
        fderiv ℝ (fun p => Ω p ![w, u]) z v +
          fderiv ℝ (fun p => Ω p ![u, v]) z w := by
  have he : (fun p => Ω p ![u, w]) = (fun p => -Ω p ![w, u]) := by
    funext p
    exact twoForm_swap (Ω p) u w
  rw [extDeriv_twoForm_apply hΩ, he, fderiv_fun_neg]
  simp only [ContinuousLinearMap.neg_apply]
  ring

end Yau.Blueprint.V03Proof
