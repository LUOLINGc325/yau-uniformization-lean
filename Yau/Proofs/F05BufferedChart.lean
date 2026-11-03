import Yau.Proofs.F05SmoothInverseChart

/-! A genuine smooth coordinate chart is dilated to a fixed buffered target ball. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

theorem buffered_smooth_chart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c₀ : OpenPartialHomeomorph E E) {x : E} (hx : x ∈ c₀.source) (hcx : c₀ x = 0)
    (hc₀ : ContDiffOn ℝ ∞ c₀ c₀.source) (hci₀ : ContDiffOn ℝ ∞ c₀.symm c₀.target) :
    ∃ (q : ℝ) (c : OpenPartialHomeomorph E E), 0 < q ∧
      c.source = c₀.source ∧ Metric.closedBall 0 4 ⊆ c.target ∧ c x = 0 ∧
      (∀ z, c z = q⁻¹ • c₀ z) ∧ (∀ z, c.symm z = c₀.symm (q • z)) ∧
      ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target := by
  have hzero : (0 : E) ∈ c₀.target := hcx ▸ c₀.map_source hx
  obtain ⟨ε,hε,hεsub⟩ := Metric.isOpen_iff.mp c₀.open_target 0 hzero
  let q : ℝ := ε/8
  have hq : 0 < q := by dsimp only [q]; positivity
  have hbuffer : Metric.closedBall (0 : E) (4*q) ⊆ c₀.target :=
    (Metric.closedBall_subset_ball (by dsimp only [q]; linarith)).trans hεsub
  let d : E ≃ₜ E := Homeomorph.smulOfNeZero q⁻¹ (inv_ne_zero hq.ne')
  let c := c₀.trans d.toOpenPartialHomeomorph
  have hsource : c.source = c₀.source := by
    change c₀.source ∩ c₀ ⁻¹' univ = c₀.source
    simp only [preimage_univ, inter_univ]
  have hcf : (c : E → E) = fun z => q⁻¹ • c₀ z := rfl
  have hci : (c.symm : E → E) = fun z => c₀.symm (q • z) := by
    funext z
    change c₀.symm ((q⁻¹)⁻¹ • z) = c₀.symm (q • z)
    rw [inv_inv]
  have hmap : MapsTo (fun z : E => q • z) c.target c₀.target := by
    intro z hz
    change z ∈ univ ∧ (q⁻¹)⁻¹ • z ∈ c₀.target at hz
    simpa only [inv_inv] using hz.2
  refine ⟨q,c,hq,hsource,?_,?_,fun z => congrFun hcf z,fun z => congrFun hci z,?_,?_⟩
  · intro z hz
    change z ∈ univ ∧ (q⁻¹)⁻¹ • z ∈ c₀.target
    refine ⟨mem_univ _, ?_⟩
    rw [inv_inv]
    apply hbuffer
    have hn : ‖z‖ ≤ 4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    nlinarith
  · rw [hcf]
    change q⁻¹ • c₀ x = 0
    rw [hcx, smul_zero]
  · rw [hsource, hcf]
    exact hc₀.const_smul q⁻¹
  · rw [hci]
    exact hci₀.comp (by fun_prop) hmap

end Yau.Proofs.F05Aux
