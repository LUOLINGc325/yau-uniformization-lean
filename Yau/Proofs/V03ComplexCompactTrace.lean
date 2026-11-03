import Yau.Proofs.V03ComplexTraceDerivative
import Yau.Proofs.V03CompactParamSmoothness
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Actual complex smoothness of a compact uniform trace follows from
joint real smoothness and native holomorphic parameter slices. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem compactParamTrace_complex_differentiableOn {Q F : Type}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set ℂ} (hU : IsOpen U) {J : Set Q} [CompactSpace J]
    (hJ : UniqueDiffOn ℝ J) {f : ℂ × Q → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ J))
    (hc : ∀ p ∈ U, ∀ q ∈ J, DifferentiableAt ℂ (fun z => f (z, q)) p) :
    DifferentiableOn ℂ (compactParamTrace hf.continuousOn) U := by
  have hreal := compactParamTrace_contDiffOn hU hJ hf
  intro p hp
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_complex_trace
    ((hreal.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
  intro q
  apply (hc p hp q.1 q.2).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hp] with z hz
  exact compactParamTrace_apply hf.continuousOn hz q

theorem compactParamTrace_complex_contDiffOn {Q F : Type}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} (hU : IsOpen U) {J : Set Q} [CompactSpace J]
    (hJ : UniqueDiffOn ℝ J) {f : ℂ × Q → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ J))
    (hc : ∀ p ∈ U, ∀ q ∈ J, DifferentiableAt ℂ (fun z => f (z, q)) p) :
    ContDiffOn ℂ ∞ (compactParamTrace hf.continuousOn) U :=
  (compactParamTrace_complex_differentiableOn hU hJ hf hc).contDiffOn hU

end Yau.Blueprint.V03Proof
