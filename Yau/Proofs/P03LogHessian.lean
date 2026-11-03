import Yau.Geometry.Calculus

open scoped Topology ContDiff
open Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- The Hessian of the actual real logarithm is computed from its first
Fréchet derivative on a neighbourhood where its argument is nonzero. -/
theorem secondFDeriv_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E → ℝ) (hq : ContDiff ℝ ∞ q) (z v w : E) (hzero : q z ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun x => Real.log (q x))) z v w =
      (q z)⁻¹ * fderiv ℝ (fderiv ℝ q) z v w -
        ((q z) ^ 2)⁻¹ * fderiv ℝ q z v * fderiv ℝ q z w := by
  have he : fderiv ℝ (fun x => Real.log (q x)) =ᶠ[𝓝 z]
      (fun x => (q x)⁻¹ • fderiv ℝ q x) := by
    filter_upwards [hq.continuous.continuousAt.eventually_ne hzero] with x hx
    exact fderiv.log (hq.differentiable (by simp) x) hx
  have hInv : HasFDerivAt (fun x => (q x)⁻¹) (-(q z ^ 2)⁻¹ • fderiv ℝ q z) z :=
    (hasDerivAt_inv hzero).comp_hasFDerivAt z (hq.differentiable (by simp) z).hasFDerivAt
  have hD : DifferentiableAt ℝ (fderiv ℝ q) z :=
    (hq.contDiffAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [he.fderiv_eq, fderiv_fun_smul hInv.differentiableAt hD, hInv.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

end Yau.NodeProofs.P03Aux
