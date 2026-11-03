import Yau.Proofs.F05CrossAtlasTransitions
import Yau.Proofs.F05PositivePhysicalPatch

/-! A solution's actual positive-time smoothness transfers from its own
finite physical atlas into a fixed raw chart of any other genuine atlas.
Only the actual overlap with the solution domain is queried. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_cross_atlas_positive_smooth {O V : Set M.Carrier} {A B : AtlasData M}
    (hA : GenuineAtlas O A) (hB : GenuineAtlas V B)
    (w : M.Carrier → ℝ → ℝ) {τ T : ℝ}
    (hInner : ∀ j, ContDiffOn ℝ ∞ (pull B j w)
      (region (B.normal j) (3/2) ×ˢ Icc τ T)) :
    ∀ i, ContDiffOn ℝ ∞ (pull A i w)
      ({x | x ∈ Metric.ball 0 3 ∧ lift A i x ∈ closure V} ×ˢ Icc τ T) := by
  intro i z hz
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hB.2.1 hz.1.2)
  obtain ⟨v,hv,hLift⟩ := hj
  have hvD : v ∈ F05D B j := F05_region_mono (by norm_num) hv
  have hDomain : z.1 ∈ F05CrossTransitionDomain A B i j := ⟨hz.1.1,v,F05D_mem_ball hvD,hLift⟩
  have hValue : F05CrossTransition A B i j z.1 = v := by
    change F05Coord B j (lift A i z.1) = v
    rw [← hLift,F05Coord_lift hB hvD]
  have hTransition := F05_cross_transition_contDiffAt hA hB i j hz.1.1 (F05D_mem_ball hvD) hLift.symm
  have hSmall : F05CrossTransition A B i j z.1 ∈ Metric.ball (0 : Space n) (3/2) := by
    rw [hValue,Metric.mem_ball,dist_zero_right]
    linarith [hv.1]
  have hNear : F05CrossTransitionDomain A B i j ∩
      (F05CrossTransition A B i j) ⁻¹' Metric.ball 0 (3/2) ∈ 𝓝 z.1 :=
    inter_mem ((F05_cross_transition_domain_isOpen hA hB i j).mem_nhds hDomain)
      (hTransition.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hSmall))
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp hNear
  let X : Set (Space n) := {x | x ∈ Metric.ball 0 3 ∧ lift A i x ∈ closure V}
  let V : Set (Point n) := (X ∩ Metric.ball z.1 r) ×ˢ Icc τ T
  let ψ : Point n → Point n := fun y => (F05CrossTransition A B i j y.1,y.2)
  have hzV : z ∈ V := ⟨⟨hz.1,Metric.mem_ball_self hr⟩,hz.2⟩
  have hMap (y : Point n) (hy : y ∈ V) :
      ψ y ∈ region (B.normal j) (3/2) ×ˢ Icc τ T ∧
        lift B j (F05CrossTransition A B i j y.1) = lift A i y.1 := by
    have hyNear := hBall hy.1.2
    have hySmall : F05CrossTransition A B i j y.1 ∈ Metric.ball (0 : Space n) (3/2) := hyNear.2
    have hy3 : F05CrossTransition A B i j y.1 ∈ Metric.ball (0 : Space n) 3 :=
      Metric.ball_subset_ball (by norm_num : (3/2 : ℝ) ≤ 3) hySmall
    have hEq := F05_cross_transition_lift A hB i j hyNear.1
    have hPhysical := ((hB.1 j).2.2.2.2.2.2.2 _ hy3).2.1
    refine ⟨⟨⟨?_,?_⟩,hy.2⟩,hEq⟩
    · exact (show ‖F05CrossTransition A B i j y.1‖ < 3/2 by
        simpa only [Metric.mem_ball,dist_zero_right] using hySmall).le
    · apply hPhysical.mp
      rw [hEq]
      exact hy.1.1.2
  have hψ : ContDiffWithinAt ℝ ∞ ψ V z :=
    ((hTransition.comp z contDiffAt_fst).prodMk contDiffAt_snd).contDiffWithinAt
  have hComposite := (hInner j (ψ z) (hMap z hzV).1).comp z hψ (fun y hy => (hMap y hy).1)
  have hEq : EqOn (pull A i w) ((pull B j w) ∘ ψ) V := by
    intro y hy
    change w (lift A i y.1) y.2 = w (lift B j (F05CrossTransition A B i j y.1)) y.2
    rw [(hMap y hy).2]
  apply (hComposite.congr_of_mem hEq hzV).mono_of_mem_nhdsWithin
  have hNearZ : (fun y : Point n => y.1) ⁻¹' Metric.ball z.1 r ∈ 𝓝 z :=
    continuous_fst.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hNearZ] with y hy hyBall
  exact ⟨⟨hy.1,hyBall⟩,hy.2⟩

end Yau.Proofs.F05Aux
