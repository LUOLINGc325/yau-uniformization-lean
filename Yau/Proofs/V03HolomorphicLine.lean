import Yau.Proofs.V03Elementary
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Cauchy's formula for actual directional Fréchet derivatives on a complex
coordinate neighborhood. This is the local primitive for smoothness of G. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem holomorphic_line_hasDerivAt {f : E → F} {x : E}
    (hf : DifferentiableAt ℂ f x) (v : E) :
    HasDerivAt (fun t : ℂ => f (x + t • v)) (fderiv ℂ f x v) 0 := by
  have hl : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
    simpa only [zero_smul, add_zero] using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt 0 hl

theorem holomorphic_line_differentiableOn {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) (x v : E) {R : ℝ}
    (hline : ∀ t ∈ Metric.closedBall (0 : ℂ) R, x + t • v ∈ U) :
    DifferentiableOn ℂ (fun t : ℂ => f (x + t • v)) (Metric.closedBall 0 R) := by
  intro t ht
  exact ((hf _ (hline t ht)).differentiableAt (hU.mem_nhds (hline t ht))).comp t
    (((differentiable_id.smul_const v).const_add x).differentiableAt) |>.differentiableWithinAt

theorem holomorphic_directional_cauchy {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) (x v : E) {R : ℝ} (hR : 0 < R)
    (hline : ∀ t ∈ Metric.closedBall (0 : ℂ) R, x + t • v ∈ U) :
    (∮ t in C(0, R), (1 / t ^ 2 : ℂ) • f (x + t • v)) =
      (2 * Real.pi * Complex.I) • fderiv ℂ f x v := by
  have hx : x ∈ U := by
    simpa only [zero_smul, add_zero] using hline 0 (by simpa using hR.le)
  have hder := holomorphic_line_hasDerivAt
    ((hf x hx).differentiableAt (hU.mem_nhds hx)) v
  have hC := (holomorphic_line_differentiableOn hU hf x v hline).deriv_eq_smul_circleIntegral hR
  simpa only [sub_zero, hder.deriv] using hC

end Yau.Blueprint.V03Proof
