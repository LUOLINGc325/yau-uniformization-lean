import Yau.Proofs.F05HolderCaps
import Yau.Proofs.F05TransitionInverse
import Yau.LeafProofs.L16BoundaryPhysicalData

/-! A receiving radius-two point is transported into the genuine radius-one
atlas cover, with an actual Lipschitz transition on a fixed neighborhood. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_inner_holder_neighborhood {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) (z : Space n) (hz : z ∈ F05D A i) :
    ∃ (j : Fin A.count) (r L : ℝ), 0 < r ∧ 0 ≤ L ∧
      (∀ y ∈ F05D A i ∩ Metric.closedBall z r,
        F05Transition A i j y ∈ region (A.normal j) (3/2) ∧
        lift A j (F05Transition A i j y) = lift A i y) ∧
      ∀ x ∈ Metric.closedBall z r, ∀ y ∈ Metric.closedBall z r,
        ‖F05Transition A i j x-F05Transition A i j y‖ ≤ L*‖x-y‖ := by
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hA.2.1 (F05D_lift_mem_closure hA hz))
  obtain ⟨w,hw,heq⟩ := hj
  have hw2 : w ∈ F05D A j := region_mono (A.normal j) (by norm_num) hw
  have hw3 : w ∈ Metric.ball (0 : Space n) 3 := F05D_mem_ball hw2
  have hzV : z ∈ F05TransitionDomain A i j := ⟨F05D_mem_ball hz,w,hw3,heq⟩
  have hValue : F05Transition A i j z = w := by
    change F05Coord A j (lift A i z) = w
    rw [← heq,F05Coord_lift hA hw2]
  have hSmall : F05Transition A i j z ∈ Metric.ball (0 : Space n) (3/2) := by
    rw [hValue,Metric.mem_ball,dist_zero_right]
    linarith [hw.1]
  have hCont := (F05Transition_contDiffOn hA i j).continuousOn.continuousAt
    ((F05TransitionDomain_isOpen hA i j).mem_nhds hzV)
  have hNear : F05TransitionDomain A i j ∩
      (F05Transition A i j) ⁻¹' Metric.ball 0 (3/2) ∈ 𝓝 z :=
    inter_mem ((F05TransitionDomain_isOpen hA i j).mem_nhds hzV)
      (hCont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hSmall))
  obtain ⟨ε,hε,hBall⟩ := Metric.mem_nhds_iff.mp hNear
  let r := ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hClosed : Metric.closedBall z r ⊆ F05TransitionDomain A i j ∩
      (F05Transition A i j) ⁻¹' Metric.ball 0 (3/2) :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hBall
  have hSmooth := (F05Transition_contDiffOn hA i j).mono
    (show Metric.closedBall z r ⊆ F05TransitionDomain A i j from fun y hy => (hClosed hy).1)
  obtain ⟨L,hLip⟩ := hSmooth.exists_lipschitzOnWith (by simp)
    (convex_closedBall z r) (isCompact_closedBall z r)
  refine ⟨j,r,L,hr,L.coe_nonneg,?_,?_⟩
  · intro y hy
    have hyV := (hClosed hy.2).1
    have hySmall := (hClosed hy.2).2
    change F05Transition A i j y ∈ Metric.ball (0 : Space n) (3/2) at hySmall
    have hLift := F05Transition_lift hA i j hyV
    have hy3 : F05Transition A i j y ∈ Metric.ball (0 : Space n) 3 :=
      Metric.ball_subset_ball (by norm_num : (3/2 : ℝ) ≤ 3) hySmall
    have hPhysical := ((hA.1 j).2.2.2.2.2.2.2 _ hy3).2.1
    refine ⟨⟨(show ‖F05Transition A i j y‖ < 3/2 by
      simpa only [Metric.mem_ball,dist_zero_right] using hySmall).le,?_⟩,hLift⟩
    apply hPhysical.mp
    rw [hLift]
    exact F05D_lift_mem_closure hA hy.1
  · intro x hx y hy
    exact hLip.norm_sub_le hx hy

end Yau.Proofs.F05Aux
