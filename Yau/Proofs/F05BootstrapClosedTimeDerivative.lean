import Yau.Proofs.F05BootstrapClosedDerivative

/-! Uniform limits retain the actual within-time derivative at both closed
endpoints. No value beyond the terminal time is involved. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux

theorem F05_uniform_deriv_closed_interval {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {l r : ℝ} (hlr : l < r)
    {f J : ℕ → ℝ → V} {fLim JLim : ℝ → V}
    (hf : ∀ k, ContinuousOn (f k) (Icc l r))
    (hJ : ∀ k, ContinuousOn (J k) (Icc l r))
    (hDeriv : ∀ k t, t ∈ Icc l r → HasDerivWithinAt (f k) (J k t) (Icc l r) t)
    (hLim : TendstoUniformlyOn f fLim atTop (Icc l r))
    (hJLim : TendstoUniformlyOn J JLim atTop (Icc l r))
    {t : ℝ} (ht : t ∈ Icc l r) : HasDerivWithinAt fLim (JLim t) (Icc l r) t := by
  let E : V →L[ℝ] (ℝ →L[ℝ] V) :=
    ContinuousLinearMap.smulRightL ℝ ℝ V (1 : ℝ →L[ℝ] ℝ)
  have hClosure : closure (interior (Icc l r)) = Icc l r := by
    rw [interior_Icc,closure_Ioo hlr.ne]
  have h := F05_uniform_derivative_closed_convex (convex_Icc l r) hClosure hf
    (fun k => E.continuous.comp_continuousOn (hJ k))
    (fun k s hs => (hDeriv k s hs).hasFDerivWithinAt) hLim
    (E.uniformContinuous.comp_tendstoUniformlyOn hJLim) ht
  simpa only [Function.comp_apply,E,ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.one_apply,one_smul]
    using h.hasDerivWithinAt

end Yau.Proofs.F05Aux
