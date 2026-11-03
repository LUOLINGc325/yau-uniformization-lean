import Yau.Proofs.F01SpaceTimeChart

/-! Native space-time smoothness is local in the original time set,
including its closed time faces. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_of_local_time_cover
    (U : M.Carrier → ℝ → ℝ) (I : Set ℝ)
    (hLocal : ∀ t ∈ I, ∃ J : Set ℝ, t ∈ J ∧ J ∈ 𝓝[I] t ∧ SmoothSpaceTime U J) :
    SmoothSpaceTime U I := by
  intro a p hp
  obtain ⟨J, htJ, hJ, hSmooth⟩ := hLocal p.2 hp.2
  obtain ⟨V, hV, hVJ⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hJ
  apply (hSmooth a p ⟨hp.1, htJ⟩).mono_of_mem_nhdsWithin
  have hLift : {q : ComplexVector n × ℝ | q.2 ∈ V} ∈ 𝓝 p :=
    (continuous_snd.tendsto p).eventually hV
  filter_upwards [mem_nhdsWithin_of_mem_nhds hLift, self_mem_nhdsWithin] with q hqV hqI
  exact ⟨hqI.1, hVJ ⟨hqV, hqI.2⟩⟩

end Yau.NodeProofs.F01Aux
