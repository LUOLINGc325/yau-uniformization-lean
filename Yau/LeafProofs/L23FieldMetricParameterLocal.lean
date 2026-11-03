import Yau.LeafProofs.L23FieldMetricNormalDistanceVariation

/-! Finite-order parameter families can be localized to a genuine open interval. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux

theorem exists_parameter_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : ℝ → E) (U : Set E) (hU : IsOpen U) (hQ : ContDiffAt ℝ 2 Q 0) (hQ₀ : Q 0 ∈ U) :
    ∃ a : ℝ, 0 < a ∧ ContDiffOn ℝ 2 Q (Set.Ioo (-a) a) ∧ Set.MapsTo Q (Set.Ioo (-a) a) U := by
  have hnear : {r : ℝ | ContDiffAt ℝ 2 Q r ∧ Q r ∈ U} ∈ 𝓝 (0 : ℝ) :=
    inter_mem (hQ.eventually (by norm_num)) (hQ.continuousAt.preimage_mem_nhds (hU.mem_nhds hQ₀))
  obtain ⟨a,ha,hasub⟩ := Metric.mem_nhds_iff.mp hnear
  have hsub (r : ℝ) (hr : r ∈ Set.Ioo (-a) a) : ContDiffAt ℝ 2 Q r ∧ Q r ∈ U := by
    apply hasub
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt] using
      (show -a < r ∧ r < a from hr)
  exact ⟨a,ha,(fun r hr => (hsub r hr).1.contDiffWithinAt),(fun r hr => (hsub r hr).2)⟩

end Yau.LeafProofs.L23Aux
