import Yau.Proofs.V03HolomorphicAngularFamily
import Yau.Proofs.V03TraceDerivativeEvaluation

/-! The actual boundary values of a jointly holomorphic closed-disc
family form a complex smooth uniform trace. Its derivative evaluates to
the genuine joint within derivative in the parameter direction. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def holomorphicFamilyUniformTrace {U : Set ℂ} {H : ℂ × ℂ → ℂ}
    (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) (z : ℂ) :
    C(BoundaryAngleInterval, ℂ) :=
  compactParamTrace (((holomorphicBoundaryFamily_contDiffOn hH).mono
    (show U ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ U ×ˢ Set.univ from
      fun p hp => ⟨hp.1, Set.mem_univ _⟩)).continuousOn) z

theorem holomorphicFamilyUniformTrace_apply {U : Set ℂ} {H : ℂ × ℂ → ℂ}
    (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) (θ : BoundaryAngleInterval) :
    holomorphicFamilyUniformTrace hH z θ = H (z, circlePoint θ) :=
  compactParamTrace_apply _ hz θ

theorem holomorphicFamilyUniformTrace_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℂ ∞ (holomorphicFamilyUniformTrace hH) U := by
  apply compactParamTrace_complex_contDiffOn hU (uniqueDiffOn_Icc (by positivity))
    ((holomorphicBoundaryFamily_contDiffOn hH).mono (fun p hp => ⟨hp.1, Set.mem_univ _⟩))
  intro z hz θ _
  exact (hasFDerivAt_complex_parameter_slice hU hz (circlePoint_mem_closedBall θ)
    ((hH.differentiableOn (by simp)) _ ⟨hz, circlePoint_mem_closedBall θ⟩)).differentiableAt

theorem fderiv_holomorphicFamilyUniformTrace_apply {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) (θ : BoundaryAngleInterval) :
    fderiv ℂ (holomorphicFamilyUniformTrace hH) z v θ =
      fderivWithin ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, circlePoint θ) (v, 0) := by
  have hd : DifferentiableAt ℂ (holomorphicFamilyUniformTrace hH) z :=
    ((holomorphicFamilyUniformTrace_contDiffOn hU hH).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  rw [fderiv_continuousMap_eval hd v θ]
  have heq : (fun p => holomorphicFamilyUniformTrace hH p θ) =ᶠ[𝓝 z]
      (fun p => H (p, circlePoint θ)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact holomorphicFamilyUniformTrace_apply hH hp θ
  rw [heq.fderiv_eq]
  exact fderiv_complex_parameter_slice hU hz (circlePoint_mem_closedBall θ)
    ((hH.differentiableOn (by simp)) _ ⟨hz, circlePoint_mem_closedBall θ⟩) v

end Yau.Blueprint.V03Proof
