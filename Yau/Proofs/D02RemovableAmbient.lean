import Yau.Proofs.D02RemovableTopology
import Mathlib.Analysis.Complex.RemovableSingularity

open Set Filter Topology Function
open scoped Topology

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux

/-- Bounded holomorphic ambient coordinates have an actual removable
extension. Continuity along the genuine radial path identifies its value
with `F p`; compact-boundary trapping then gives the full intrinsic limit. -/
theorem tendsto_of_bounded_holomorphic_ambient_and_radial
    {Y E : Type*} [MetricSpace Y] [ProperSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → Y} {F : Y → E} {p : Y} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < R})
    (hF : Continuous F) (hinj : Function.Injective F)
    (hd : DifferentiableOn ℂ (F ∘ f) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < R})
    {B : ℝ} (hbound : ∀ z, 0 < ‖z‖ ∧ ‖z‖ < R → ‖F (f z)‖ ≤ B)
    (θ : ℝ) (hradial : Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp (θ * Complex.I)))
      (𝓝[>] 0) (𝓝 p)) :
    Tendsto f (𝓝[≠] 0) (𝓝 p) := by
  let L := limUnder (𝓝[≠] (0 : ℂ)) (F ∘ f)
  let W := Function.update (F ∘ f) (0 : ℂ) L
  have hset : Metric.ball (0 : ℂ) R \ {0} = {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < R} := by
    ext z
    simp only [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff,
      Set.mem_ofPred_eq]
    exact ⟨fun hz ↦ ⟨norm_pos_iff.mpr hz.2, hz.1⟩, fun hz ↦ ⟨hz.2, norm_pos_iff.mp hz.1⟩⟩
  have hW : DifferentiableOn ℂ W (Metric.ball (0 : ℂ) R) := by
    apply Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds 0 hR)
    · rwa [hset]
    · refine ⟨B, ?_⟩
      rintro a ⟨z, hz, rfl⟩
      exact hbound z (by rwa [hset] at hz)
  have hlim : Tendsto (F ∘ f) (𝓝[≠] (0 : ℂ)) (𝓝 L) := by
    apply continuousAt_update_same.mp
    exact (hW.differentiableAt (Metric.ball_mem_nhds 0 hR)).continuousAt
  have heq : L = F p := tendsto_nhds_unique (hlim.comp (tendsto_radial_punctured θ))
    (hF.continuousAt.tendsto.comp hradial)
  apply tendsto_of_injective_ambient_and_radial hR hf hF hinj _ θ hradial
  simpa only [heq] using hlim

end Yau.NodeProofs.D02RemovableAux
