import Yau.Proofs.C02InverseDerivativeOperators

/-! The inverse derivative needs only differentiability at the actual
point. This permits fixed open smooth domains without extending germs. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem actualInverseField_fderiv_at {B : E → E →L[ℝ] E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hx : (B x).IsInvertible) (u v : E) :
    fderiv ℝ (fun y => (B y).inverse) x u v =
      -(B x).inverse (fderiv ℝ B x u ((B x).inverse v)) := by
  let C := fun y => (B y).inverse
  have hC : DifferentiableAt ℝ C x :=
    ((hx.contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).differentiableAt (by simp)).comp x hB
  have hNear : ∀ᶠ y in 𝓝 x, (B y).IsInvertible :=
    hB.continuousAt.eventually hx.eventually_nhds
  have heq : (fun y => (C y).comp (B y)) =ᶠ[𝓝 x] fderiv ℝ (id : E → E) := by
    filter_upwards [hNear] with y hy
    simpa only [fderiv_id] using hy.inverse_comp_self
  have hId : fderiv ℝ (fderiv ℝ (id : E → E)) x = 0 := by
    have he : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
      funext (fun y => fderiv_id)
    rw [he]
    exact (hasFDerivAt_const _ x).fderiv
  have hv := congrArg (fun L : E →L[ℝ] E => L v) hx.self_comp_inverse
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hv
  have hh := operator_factor_fderiv hC hB heq u (C x v)
  rw [hId, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, hv] at hh
  exact eq_neg_of_add_eq_zero_right hh

theorem actualInverseField_fderiv_operator_at {B : E → E →L[ℝ] E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hx : (B x).IsInvertible) :
    fderiv ℝ (fun y => (B y).inverse) x =
      -inverseDerivativeRight E (inverseDerivativeLeft E (B x).inverse (fderiv ℝ B x)) (B x).inverse := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact actualInverseField_fderiv_at hB hx u v

end Yau.Blueprint.C02Proof
