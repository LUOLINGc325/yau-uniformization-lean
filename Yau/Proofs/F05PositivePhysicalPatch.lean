import Yau.Proofs.F05PositiveSmoothTransfer

/-! Actual atlas transitions carry buffered physical smoothness to any
physical radius-three point. The receiving radius-two rim is artificial. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_inner_smooth_to_physical_patch {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (w : M.Carrier → ℝ → ℝ) {τ T : ℝ}
    (hInner : ∀ j, ContDiffOn ℝ ∞ (pull A j w)
      (region (A.normal j) (3/2) ×ˢ Icc τ T)) :
    ∀ i, ContDiffOn ℝ ∞ (pull A i w)
      ({x | x ∈ Metric.ball 0 3 ∧ lift A i x ∈ closure O} ×ˢ Icc τ T) := by
  intro i z hz
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hA.2.1 hz.1.2)
  obtain ⟨v,hv,hLift⟩ := hj
  have hvD : v ∈ F05D A j := F05_region_mono (by norm_num) hv
  have hDomain : z.1 ∈ F05TransitionDomain A i j := ⟨hz.1.1,v,F05D_mem_ball hvD,hLift⟩
  have hValue : F05Transition A i j z.1 = v := by
    change F05Coord A j (lift A i z.1) = v
    rw [← hLift,F05Coord_lift hA hvD]
  have hTransition := (F05Transition_contDiffOn hA i j).contDiffAt
    ((F05TransitionDomain_isOpen hA i j).mem_nhds hDomain)
  have hSmall : F05Transition A i j z.1 ∈ Metric.ball (0 : Space n) (3/2) := by
    rw [hValue,Metric.mem_ball,dist_zero_right]
    linarith [hv.1]
  have hNear : F05TransitionDomain A i j ∩
      (F05Transition A i j) ⁻¹' Metric.ball 0 (3/2) ∈ 𝓝 z.1 :=
    inter_mem ((F05TransitionDomain_isOpen hA i j).mem_nhds hDomain)
      (hTransition.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hSmall))
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp hNear
  let X : Set (Space n) := {x | x ∈ Metric.ball 0 3 ∧ lift A i x ∈ closure O}
  let V : Set (Point n) := (X ∩ Metric.ball z.1 r) ×ˢ Icc τ T
  let ψ : Point n → Point n := fun y => (F05Transition A i j y.1,y.2)
  have hzV : z ∈ V := ⟨⟨hz.1,Metric.mem_ball_self hr⟩,hz.2⟩
  have hMap (y : Point n) (hy : y ∈ V) :
      ψ y ∈ region (A.normal j) (3/2) ×ˢ Icc τ T ∧
        lift A j (F05Transition A i j y.1) = lift A i y.1 := by
    have hyNear := hBall hy.1.2
    have hySmall : F05Transition A i j y.1 ∈ Metric.ball (0 : Space n) (3/2) := hyNear.2
    have hy3 : F05Transition A i j y.1 ∈ Metric.ball (0 : Space n) 3 :=
      Metric.ball_subset_ball (by norm_num : (3/2 : ℝ) ≤ 3) hySmall
    have hEq := F05Transition_lift hA i j hyNear.1
    have hPhysical := ((hA.1 j).2.2.2.2.2.2.2 _ hy3).2.1
    refine ⟨⟨⟨?_,?_⟩,hy.2⟩,hEq⟩
    · exact (show ‖F05Transition A i j y.1‖ < 3/2 by
        simpa only [Metric.mem_ball,dist_zero_right] using hySmall).le
    · apply hPhysical.mp
      rw [hEq]
      exact hy.1.1.2
  have hψ : ContDiffWithinAt ℝ ∞ ψ V z :=
    ((hTransition.comp z contDiffAt_fst).prodMk contDiffAt_snd).contDiffWithinAt
  have hComposite := (hInner j (ψ z) (hMap z hzV).1).comp z hψ (fun y hy => (hMap y hy).1)
  have hEq : EqOn (pull A i w) ((pull A j w) ∘ ψ) V := by
    intro y hy
    change w (lift A i y.1) y.2 = w (lift A j (F05Transition A i j y.1)) y.2
    rw [(hMap y hy).2]
  apply (hComposite.congr_of_mem hEq hzV).mono_of_mem_nhdsWithin
  have hNearZ : (fun y : Point n => y.1) ⁻¹' Metric.ball z.1 r ∈ 𝓝 z :=
    continuous_fst.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hNearZ] with y hy hyBall
  exact ⟨⟨hy.1,hyBall⟩,hy.2⟩

end Yau.Proofs.F05Aux
