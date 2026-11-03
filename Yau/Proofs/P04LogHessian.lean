import Yau.Proofs.P04CanonicalNorm

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs

/-- The exact real Hessian chain rule used for all positive logarithms. -/
theorem secondFDeriv_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hpos : 0 < f x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) x v w =
      (f x)⁻¹*fderiv ℝ (fderiv ℝ f) x v w -
        ((f x)^2)⁻¹*(fderiv ℝ f x v)*(fderiv ℝ f x w) := by
  have hlog : ContDiffAt ℝ 2 Real.log (f x) := Real.contDiffAt_log.mpr hpos.ne'
  have HH := L18Aux.secondFDeriv_comp hf hlog v w
  rw [L18Aux.secondFDeriv_scalar_apply hlog,fderiv_eq_deriv_mul,Real.deriv_log,
    Real.deriv_log',deriv_inv] at HH
  exact HH.trans (by ring)

/-- Complexifying a real differential preserves the actual real derivative. -/
theorem fderiv_ofReal_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ (fun y => (f y : ℂ)) x v = (fderiv ℝ f x v : ℂ) := by
  have HH := Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
  exact congrArg (fun L => L v) HH.fderiv

end Yau.Proofs.P04Aux
