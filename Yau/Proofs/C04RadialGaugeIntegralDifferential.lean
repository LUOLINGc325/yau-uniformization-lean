import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-! Differentiate the actual radial gauge and coframe identities. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem radial_clm_differential (T : E → E →L[ℝ] F) (f : E → F)
    (hT : ContDiff ℝ ∞ T) (hf : ContDiff ℝ ∞ f)
    {U : Set E} (hU : IsOpen U) (hTf : ∀ x ∈ U, T x x = f x)
    {x : E} (hx : x ∈ U) (w : E) :
    (fderiv ℝ T x w) x + T x w = fderiv ℝ f x w := by
  have hc : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa only [one_smul, id_eq] using HasDerivAt.const_add x ((hasDerivAt_id (0 : ℝ)).smul_const w)
  have hdT := ((hT.differentiable (by simp)) (x + (0 : ℝ) • w)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hdf := ((hf.differentiable (by simp)) (x + (0 : ℝ) • w)).hasFDerivAt.comp_hasDerivAt 0 hc
  have heval := hdT.clm_apply hc
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • w ∈ U :=
    hc.continuousAt.eventually (hU.mem_nhds (by simpa only [zero_smul, add_zero] using hx))
  have heq : (fun t : ℝ => T (x + t • w) (x + t • w)) =ᶠ[𝓝 0]
      (fun t : ℝ => f (x + t • w)) := hmem.mono fun t ht => hTf _ ht
  have hh := heval.unique (hdf.congr_of_eventuallyEq heq)
  simpa only [Function.comp_apply, zero_smul, add_zero] using hh

theorem radial_connection_differential (conn : E → E →L[ℝ] E →L[ℝ] E)
    (hconn : ContDiff ℝ ∞ conn) {R : ℝ}
    (hrel : ∀ x ∈ Metric.ball (0 : E) R, conn x x = 0)
    {x : E} (hx : x ∈ Metric.ball (0 : E) R) (w : E) :
    (fderiv ℝ conn x w) x + conn x w = 0 := by
  simpa only [fderiv_const_apply, ContinuousLinearMap.zero_apply] using
    radial_clm_differential conn (fun _ => (0 : E →L[ℝ] E)) hconn contDiff_const
      Metric.isOpen_ball hrel hx w

theorem radial_coframe_differential (A : E → E →L[ℝ] E)
    (hA : ContDiff ℝ ∞ A) {R : ℝ}
    (hrel : ∀ x ∈ Metric.ball (0 : E) R, A x x = x)
    {x : E} (hx : x ∈ Metric.ball (0 : E) R) (w : E) :
    (fderiv ℝ A x w) x + A x w = w := by
  simpa only [fderiv_id, ContinuousLinearMap.id_apply] using
    radial_clm_differential A (id : E → E) hA contDiff_id Metric.isOpen_ball hrel hx w

def radialGaugeCurvature (conn : E → E →L[ℝ] E →L[ℝ] E) (x u w : E) : E →L[ℝ] E :=
  (fderiv ℝ conn x u) w - (fderiv ℝ conn x w) u + (conn x u).comp (conn x w) - (conn x w).comp (conn x u)

end Yau.Proofs.C04Aux
