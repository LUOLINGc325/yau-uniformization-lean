import Yau.Proofs.F05DefiningCoordinates

/-! Total chart functions use a sentinel outside their genuine source, so the
computed AtlasData source gains no spurious preimages of the radius-three ball. -/

open Set
open scoped Topology ContDiff
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.LeafProofs.L16Aux

def F05Sentinel (n : ℕ) (hn : 0 < n) : Space n :=
  (4 : ℝ) • realVec (⟨0,hn⟩,0)

theorem F05Sentinel_norm (n : ℕ) (hn : 0 < n) : ‖F05Sentinel n hn‖ = 4 := by
  simp [F05Sentinel,norm_smul,realVec_norm]

def F05TotalForward {E : Type*} [TopologicalSpace E] (s : E)
    (c : OpenPartialHomeomorph E E) (z : E) : E := by
  classical
  exact if z ∈ c.source then c z else s

theorem F05TotalForward_eq {E : Type*} [TopologicalSpace E] (s : E)
    (c : OpenPartialHomeomorph E E) {z : E} (hz : z ∈ c.source) :
    F05TotalForward s c z = c z := by
  simp only [F05TotalForward,ite_eq_left hz]

theorem F05TotalForward_source {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : E) (hs : ‖s‖ = 4) (c : OpenPartialHomeomorph E E)
    (V : Set E) (hcV : c.source ⊆ V) :
    V ∩ (F05TotalForward s c) ⁻¹' Metric.ball 0 3 = c.source ∩ c ⁻¹' Metric.ball 0 3 := by
  classical
  ext z
  by_cases hz : z ∈ c.source
  · constructor
    · intro h
      exact ⟨hz,by simpa only [mem_preimage,F05TotalForward_eq s c hz] using h.2⟩
    · intro h
      exact ⟨hcV hz,by simpa only [mem_preimage,F05TotalForward_eq s c hz] using h.2⟩
  · have hnot : F05TotalForward s c z ∉ Metric.ball 0 3 := by
      simp only [F05TotalForward,ite_eq_right hz,Metric.mem_ball,dist_zero_right,hs]
      norm_num
    exact ⟨fun h => False.elim (hnot h.2),fun h => False.elim (hz h.1)⟩

theorem F05TotalForward_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : E) (c : OpenPartialHomeomorph E E) (hc : ContDiffOn ℝ ∞ c c.source) :
    ContDiffOn ℝ ∞ (F05TotalForward s c) (c.source ∩ c ⁻¹' Metric.ball 0 3) := by
  exact (hc.mono inter_subset_left).congr fun z hz => F05TotalForward_eq s c hz.1

theorem F05TotalForward_inverse_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : E) (c : OpenPartialHomeomorph E E) (hbuffer : Metric.closedBall 0 4 ⊆ c.target)
    {z : E} (hz : z ∈ Metric.ball 0 3) :
    c.symm z ∈ c.source ∩ c ⁻¹' Metric.ball 0 3 ∧ F05TotalForward s c (c.symm z) = z := by
  have hzT : z ∈ c.target := hbuffer
    ((Metric.closedBall_subset_closedBall (by norm_num : (3 : ℝ) ≤ 4))
      (Metric.ball_subset_closedBall hz))
  have hsource := c.map_target hzT
  have hright := c.right_inv hzT
  exact ⟨⟨hsource,by change c (c.symm z) ∈ Metric.ball 0 3; rwa [hright]⟩,
    (F05TotalForward_eq s c hsource).trans hright⟩

theorem F05TotalForward_left_inverse {E : Type*} [TopologicalSpace E]
    (s : E) (c : OpenPartialHomeomorph E E) {z : E} (hz : z ∈ c.source) :
    c.symm (F05TotalForward s c z) = z := by
  rw [F05TotalForward_eq s c hz]
  exact c.left_inv hz

end Yau.Proofs.F05Aux
