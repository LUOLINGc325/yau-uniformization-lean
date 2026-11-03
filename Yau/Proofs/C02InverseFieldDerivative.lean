import Yau.Proofs.C02OperatorFactorDerivative
import Yau.Proofs.C02OperatorSmoothInverse

/-! The derivative of the actual operator inverse is derived by
differentiating its genuine two-sided identity on the open invertible set. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem actualInverseField_fderiv {B : E → E →L[ℝ] E} (hB : ContDiff ℝ ∞ B)
    {x : E} (hx : (B x).IsInvertible) (u v : E) :
    fderiv ℝ (fun y => (B y).inverse) x u v =
      -(B x).inverse (fderiv ℝ B x u ((B x).inverse v)) := by
  let C := fun y => (B y).inverse
  have hC : ContDiffAt ℝ ∞ C x :=
    (hx.contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).comp x hB.contDiffAt
  have hNear : ∀ᶠ y in 𝓝 x, (B y).IsInvertible := hB.continuous.continuousAt.eventually hx.eventually_nhds
  have heq : (fun y => (C y).comp (B y)) =ᶠ[𝓝 x] fderiv ℝ (id : E → E) := by
    filter_upwards [hNear] with y hy
    simpa only [fderiv_id] using hy.inverse_comp_self
  have hId : fderiv ℝ (fderiv ℝ (id : E → E)) x = 0 := by
    have he : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E := funext (fun y => fderiv_id)
    rw [he]
    exact (hasFDerivAt_const _ x).fderiv
  have hv := congrArg (fun L : E →L[ℝ] E => L v) hx.self_comp_inverse
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hv
  have h := operator_factor_fderiv (hC.differentiableAt (by simp)) (hB.differentiable (by simp) x)
    heq u (C x v)
  rw [hId, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, hv] at h
  exact eq_neg_of_add_eq_zero_right h

end Yau.Blueprint.C02Proof
