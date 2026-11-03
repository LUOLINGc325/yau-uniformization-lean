import Yau.Proofs.F05DefiningCoordinates
import Yau.Proofs.F05AtlasModel

/-! The genuine manifold defining function supplies local smooth physical charts,
including the actual closure and frontier faces. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.HeatConcreteBindings Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem coordinate_halfSpace_closure (j : RIdx n) :
    closure {z : Space n | realCoord z j < 0} = {z | realCoord z j ≤ 0} := by
  let e := -(realVec j)
  have he : ‖e‖ = 1 := by simp only [e,norm_neg,realVec_norm]
  have hi (z : Space n) : inner ℝ e z = -realCoord z j := by
    rw [show e = -(realVec j) from rfl, inner_neg_left, real_inner_comm, real_inner_realVec]
  have hset : {z : Space n | realCoord z j < 0} = {z | 0 < inner ℝ e z} := by
    ext z
    simp only [mem_ofPred_eq,hi,neg_pos]
  rw [hset,unitNormal_halfSpace_closure he]
  ext z
  simp only [mem_ofPred_eq,hi,neg_nonneg]

theorem coordinate_halfSpace_frontier (j : RIdx n) :
    frontier {z : Space n | realCoord z j < 0} = {z | realCoord z j = 0} := by
  let e := -(realVec j)
  have he : ‖e‖ = 1 := by simp only [e,norm_neg,realVec_norm]
  have hi (z : Space n) : inner ℝ e z = -realCoord z j := by
    rw [show e = -(realVec j) from rfl, inner_neg_left, real_inner_comm, real_inner_realVec]
  have hset : {z : Space n | realCoord z j < 0} = {z | 0 < inner ℝ e z} := by
    ext z
    simp only [mem_ofPred_eq,hi,neg_pos]
  rw [hset,unitNormal_halfSpace_frontier he]
  ext z
  simp only [mem_ofPred_eq,hi,neg_eq_zero]

theorem smoothPrecompact_boundary_chart {O : Set M.Carrier}
    (hO : SmoothPrecompactDomain O) {p : M.Carrier} (hp : p ∈ frontier O) :
    ∃ (x : M.Carrier) (j : RIdx n) (c : OpenPartialHomeomorph (Space n) (Space n)),
      p ∈ (extChartAt (ComplexModel n) x).source ∧ chartPt x p ∈ c.source ∧
      c (chartPt x p) = 0 ∧ c.source ⊆ chartTarget x ∧
      ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target ∧
      ∀ z ∈ c.source,
        (chartInv x z ∈ O ↔ realCoord (c z) j < 0) ∧
        (chartInv x z ∈ closure O ↔ realCoord (c z) j ≤ 0) ∧
        (chartInv x z ∈ frontier O ↔ realCoord (c z) j = 0) := by
  obtain ⟨x,V,ρ,hpx,hV,hpV,hVT,hρ,hρ0,hD,hinside⟩ := hO.2.2.2.2 p hp
  have hpx' : p ∈ (extChartAt (ComplexModel n) x).source := by
    simpa only [extChartAt_source] using hpx
  obtain ⟨j,c,hpc,hcV,hcp,hc,hci,hlevel⟩ :=
    defining_function_smooth_coordinate_chart hV hρ hpV hρ0 hD
  let a : OpenPartialHomeomorph M.Carrier (Space n) := chartAt (Space n) x
  have haPt : (a : M.Carrier → Space n) = chartPt x := by
    funext y
    simp [a, chartPt, extChartAt_coe, ComplexModel, modelWithCornersSelf_coe]
  have haInv : (a.symm : Space n → M.Carrier) = chartInv x := by
    funext z
    simp [a, chartInv, extChartAt_coe_symm, ComplexModel, modelWithCornersSelf_coe_symm]
  let e := a.trans c
  have hInside (y : M.Carrier) (hy : y ∈ e.source) :
      y ∈ O ↔ realCoord (e y) j < 0 := by
    have hm := hinside (a y) (hcV hy.2)
    rw [← haInv, a.left_inv hy.1] at hm
    change y ∈ O ↔ realCoord (c (a y)) j < 0
    rw [hlevel]
    exact hm
  have hImage : e.IsImage O {z : Space n | realCoord z j < 0} :=
    fun y hy => (hInside y hy).symm
  refine ⟨x,j,c,hpx',hpc,hcp,hcV.trans hVT,hc,hci,?_⟩
  intro z hz
  have hzT : z ∈ chartTarget x := hVT (hcV hz)
  have hright : chartPt x (chartInv x z) = z :=
    (extChartAt (ComplexModel n) x).right_inv hzT
  have hzRaw : z ∈ a.target := by
    simpa [a, chartTarget, ComplexModel] using hzT
  have hyRaw : chartInv x z ∈ a.source := by
    have hm := a.map_target hzRaw
    rw [haInv] at hm
    exact hm
  have heSource : chartInv x z ∈ e.source :=
    ⟨hyRaw, by change a (chartInv x z) ∈ c.source; rwa [haPt,hright]⟩
  have heVal : e (chartInv x z) = c z := by
    change c (a (chartInv x z)) = c z
    rw [haPt,hright]
  refine ⟨?_,?_,?_⟩
  · rw [hlevel]
    exact hinside z (hcV hz)
  · have hm := (hImage.closure.apply_mem_iff heSource).symm
    rw [coordinate_halfSpace_closure] at hm
    simpa only [mem_ofPred_eq, heVal] using hm
  · have hm := (hImage.frontier.apply_mem_iff heSource).symm
    rw [coordinate_halfSpace_frontier] at hm
    simpa only [mem_ofPred_eq, heVal] using hm

end Yau.Proofs.F05Aux
