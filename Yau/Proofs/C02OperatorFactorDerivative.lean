import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Differentiating an actual operator factorization, pointwise in its two
directions. Only genuine derivative and neighborhood equality data are used. -/

noncomputable section
open Filter
open scoped Topology
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem operator_factor_fderiv {Q B : E → E →L[ℝ] E} {f : E → E} {x : E}
    (hQ : DifferentiableAt ℝ Q x) (hB : DifferentiableAt ℝ B x)
    (heq : (fun y => (Q y).comp (B y)) =ᶠ[𝓝 x] fderiv ℝ f) (u v : E) :
    Q x (fderiv ℝ B x u v) + fderiv ℝ Q x u (B x v) =
      fderiv ℝ (fderiv ℝ f) x u v := by
  have hd := hQ.hasFDerivAt.clm_comp hB.hasFDerivAt
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] E => L u v)
    (hd.fderiv.symm.trans heq.fderiv_eq)
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply] using he

end Yau.Blueprint.C02Proof
