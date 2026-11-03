import Yau.Proofs.C02ConnectionCurvature

/-! Curvature transformation obtained by twice differentiating the actual
frame equation DQ + Omega Q = Q A. No invertibility of a base-map Jacobian
is assumed, and no curvature identity is supplied as a premise. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance transform_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance transform_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance transform_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance transform_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem gauge_curvature_transform (Q : E → E →L[ℝ] E)
    (A Ω : E → E →L[ℝ] E →L[ℝ] E) (x u v : E)
    (hQ : ContDiffAt ℝ 2 Q x) (hA : DifferentiableAt ℝ A x) (hΩ : DifferentiableAt ℝ Ω x)
    (hConn : ∀ a : E,
      (fun y => fderiv ℝ Q y a + (Ω y a).comp (Q y)) =ᶠ[𝓝 x]
        (fun y => (Q y).comp (A y a))) :
    (Q x).comp (connectionCurvature A x u v) =
      (connectionCurvature Ω x u v).comp (Q x) := by
  have hQD : DifferentiableAt ℝ Q x := hQ.differentiableAt (by norm_num)
  have hQDD : DifferentiableAt ℝ (fderiv ℝ Q) x :=
    (hQ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDir (a b : E) :
      fderiv ℝ (fderiv ℝ Q) x b a + (Ω x a).comp (fderiv ℝ Q x b) +
        (fderiv ℝ Ω x b a).comp (Q x) =
      (Q x).comp (fderiv ℝ A x b a) + (fderiv ℝ Q x b).comp (A x a) := by
    have hConst : HasFDerivAt (fun _ : E => a) (0 : E →L[ℝ] E) x := hasFDerivAt_const a x
    have hDQa := hQDD.hasFDerivAt.clm_apply hConst
    have hΩa := hΩ.hasFDerivAt.clm_apply hConst
    have hAa := hA.hasFDerivAt.clm_apply hConst
    have hLeft := hDQa.add (hΩa.clm_comp hQD.hasFDerivAt)
    have hRight := hQD.hasFDerivAt.clm_comp hAa
    have he := hLeft.fderiv.symm.trans
      (((hConn a).fderiv_eq (𝕜 := ℝ)).trans hRight.fderiv)
    have he' := congrArg (fun L : E →L[ℝ] E →L[ℝ] E => L b) he
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.zero_apply, map_zero, add_zero, zero_add, add_assoc] using he'
  have hDQ (a : E) : fderiv ℝ Q x a = (Q x).comp (A x a) - (Ω x a).comp (Q x) := by
    have h0 := (hConn a).self_of_nhds
    change fderiv ℝ Q x a + (Ω x a).comp (Q x) = (Q x).comp (A x a) at h0
    calc
      _ = (fderiv ℝ Q x a + (Ω x a).comp (Q x)) - (Ω x a).comp (Q x) := by abel
      _ = _ := by rw [h0]
  have hQA (a b : E) : (Q x).comp (fderiv ℝ A x b a) =
      fderiv ℝ (fderiv ℝ Q) x b a + (Ω x a).comp (fderiv ℝ Q x b) +
        (fderiv ℝ Ω x b a).comp (Q x) - (fderiv ℝ Q x b).comp (A x a) := by
    calc
      _ = ((Q x).comp (fderiv ℝ A x b a) + (fderiv ℝ Q x b).comp (A x a)) -
          (fderiv ℝ Q x b).comp (A x a) := by abel
      _ = _ := by rw [← hDir a b]
  have hSymm := hQ.isSymmSndFDerivAt (by norm_num) u v
  have hQAuv := hQA v u
  have hQAvu := hQA u v
  have hDQu := hDQ u
  have hDQv := hDQ v
  change Q x * fderiv ℝ A x u v = fderiv ℝ (fderiv ℝ Q) x u v +
    Ω x v * fderiv ℝ Q x u + fderiv ℝ Ω x u v * Q x - fderiv ℝ Q x u * A x v at hQAuv
  change Q x * fderiv ℝ A x v u = fderiv ℝ (fderiv ℝ Q) x v u +
    Ω x u * fderiv ℝ Q x v + fderiv ℝ Ω x v u * Q x - fderiv ℝ Q x v * A x u at hQAvu
  change fderiv ℝ Q x u = Q x * A x u - Ω x u * Q x at hDQu
  change fderiv ℝ Q x v = Q x * A x v - Ω x v * Q x at hDQv
  change Q x * (fderiv ℝ A x u v - fderiv ℝ A x v u + A x u * A x v - A x v * A x u) =
    (fderiv ℝ Ω x u v - fderiv ℝ Ω x v u + Ω x u * Ω x v - Ω x v * Ω x u) * Q x
  rw [mul_sub, mul_add, mul_sub, hQAuv, hQAvu, hDQu, hDQv, hSymm]
  noncomm_ring

end Yau.Blueprint.C02Proof
