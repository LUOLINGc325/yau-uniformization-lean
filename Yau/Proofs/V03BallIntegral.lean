import Yau.Proofs.V03ParameterIntegral

/-! Domination for disc integrals is derived from actual compact joint
continuity, including one-sided continuity of a radial parameter. -/

open scoped Topology
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {P F : Type*} [NormedAddCommGroup P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuousWithinAt_ballIntegral_of_joint_compact
    {K : Set P} (hK : IsCompact K) {x : P} (hx : x ∈ K)
    {f : P → ℂ → F}
    (hf : ContinuousOn (fun p : P × ℂ => f p.1 p.2)
      (K ×ˢ Metric.closedBall 0 1)) :
    ContinuousWithinAt (fun y => ∫ z in Metric.ball (0 : ℂ) 1, f y z) K x := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have htime : ∀ y ∈ K, ContinuousOn (f y) (Metric.closedBall 0 1) := by
    intro y hy
    exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hy, hz⟩)
  have hparam : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ContinuousWithinAt (fun y => f y z) K x := by
    intro z hz
    exact (hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun y hy => ⟨hy, hz⟩)) x hx
  obtain ⟨C, hC⟩ :=
    ((hK.prod (isCompact_closedBall (0 : ℂ) 1)).image_of_continuousOn hf).isBounded.exists_norm_le
  apply continuousWithinAt_of_dominated (bound := fun _ => C)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((htime y hy).mono Metric.ball_subset_closedBall).aestronglyMeasurable
      measurableSet_ball
  · filter_upwards [self_mem_nhdsWithin] with y hy
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hC (f y z) ⟨(y, z), ⟨hy, Metric.ball_subset_closedBall hz⟩, rfl⟩
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hparam z (Metric.ball_subset_closedBall hz)

end Yau.Blueprint.V03Proof
