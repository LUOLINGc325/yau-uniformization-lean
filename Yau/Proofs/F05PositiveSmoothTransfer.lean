import Yau.Proofs.F05HolderTransitionNeighborhood

/-! Positive-time within smoothness transfers from buffered source charts
onto the complete closed receiving charts, including their radius-two rims. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_positive_inner_smooth_to_full {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (w : M.Carrier → ℝ → ℝ) {τ T : ℝ}
    (hInner : ∀ j, ContDiffOn ℝ ∞ (pull A j w)
      (region (A.normal j) (3/2) ×ˢ Icc τ T)) :
    ∀ i, ContDiffOn ℝ ∞ (pull A i w) (F05D A i ×ˢ Icc τ T) := by
  intro i z hz
  obtain ⟨j,r,L,hr,hL,hMap,hLip⟩ := F05_inner_holder_neighborhood hA i z.1 hz.1
  let V : Set (Point n) := (F05D A i ∩ Metric.closedBall z.1 r) ×ˢ Icc τ T
  let ψ : Point n → Point n := fun y => (F05Transition A i j y.1,y.2)
  have hzBall : z.1 ∈ Metric.closedBall z.1 r := Metric.mem_closedBall_self hr.le
  have hzV : z ∈ V := ⟨⟨hz.1,hzBall⟩,hz.2⟩
  have hAt := hMap z.1 ⟨hz.1,hzBall⟩
  have hDomain : z.1 ∈ F05TransitionDomain A i j := by
    refine ⟨F05D_mem_ball hz.1,F05Transition A i j z.1,?_,hAt.2⟩
    simpa only [Metric.mem_ball,dist_zero_right] using lt_of_le_of_lt hAt.1.1 (by norm_num : (3/2 : ℝ) < 3)
  have hTransition : ContDiffAt ℝ ∞ (F05Transition A i j) z.1 :=
    (F05Transition_contDiffOn hA i j).contDiffAt
      ((F05TransitionDomain_isOpen hA i j).mem_nhds hDomain)
  have hψ : ContDiffWithinAt ℝ ∞ ψ V z :=
    ((hTransition.comp z contDiffAt_fst).prodMk contDiffAt_snd).contDiffWithinAt
  have hMaps : MapsTo ψ V (region (A.normal j) (3/2) ×ˢ Icc τ T) :=
    fun y hy => ⟨(hMap y.1 hy.1).1,hy.2⟩
  have hComposite := (hInner j (ψ z) (hMaps hzV)).comp z hψ hMaps
  have hEq : EqOn (pull A i w) ((pull A j w) ∘ ψ) V := by
    intro y hy
    change w (lift A i y.1) y.2 = w (lift A j (F05Transition A i j y.1)) y.2
    rw [(hMap y.1 hy.1).2]
  have hLocal := hComposite.congr_of_mem hEq hzV
  apply hLocal.mono_of_mem_nhdsWithin
  have hNear : (fun y : Point n => y.1) ⁻¹' Metric.ball z.1 r ∈ 𝓝 z :=
    continuous_fst.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hNear] with y hy hNearY
  exact ⟨⟨hy.1,Metric.ball_subset_closedBall hNearY⟩,hy.2⟩

end Yau.Proofs.F05Aux
