import Yau.Blueprint.Nodes

/-! Two concentric coordinate balls, their genuine compact image, and
an original-manifold neighbourhood on the same chart sheet. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau

theorem exists_compact_chart_neighborhood {n : ℕ} (M : ComplexManifold n) (x : M.Carrier) :
    ∃ r : ℝ, 0 < r ∧
      closedBall (chartPt x x) (2 * r) ⊆ chartTarget x ∧
      IsCompact (chartInv x '' closedBall (chartPt x x) (2 * r)) ∧
      MDifferentiableOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) (chartInv x)
        (ball (chartPt x x) (2 * r)) ∧
      ∃ V : Set M.Carrier, IsOpen V ∧ x ∈ V ∧
        Set.MapsTo (chartPt x) V (closedBall (chartPt x x) r) ∧
        (∀ y ∈ V, y ∈ (extChartAt (ComplexModel n) x).source ∧ chartInv x (chartPt x y) = y) := by
  have htarget : IsOpen (chartTarget x) := isOpen_extChartAt_target x
  have hxt : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp htarget (chartPt x x) hxt
  let r := eps / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hclosed : closedBall (chartPt x x) (2 * r) ⊆ chartTarget x := by
    intro z hz
    apply hball
    rw [mem_ball]
    have hh := mem_closedBall.mp hz
    dsimp [r] at hh
    linarith
  have hcompact : IsCompact (chartInv x '' closedBall (chartPt x x) (2 * r)) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm x).mono hclosed)
  have hmd : MDifferentiableOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) (chartInv x)
      (ball (chartPt x x) (2 * r)) := by
    exact ((contMDiffOn_extChartAt_symm (I := ComplexModel n) (n := ∞) x).mdifferentiableOn
      (by simp)).mono (ball_subset_closedBall.trans hclosed)
  let V := (extChartAt (ComplexModel n) x).source ∩
    (chartPt x) ⁻¹' ball (chartPt x x) r
  have hV : IsOpen V :=
    (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x) isOpen_ball
  have hxV : x ∈ V := ⟨mem_extChartAt_source x, mem_ball_self hr⟩
  refine ⟨r, hr, hclosed, hcompact, hmd, V, hV, hxV, ?_, ?_⟩
  · intro y hy
    exact ball_subset_closedBall hy.2
  · intro y hy
    exact ⟨hy.1, (extChartAt (ComplexModel n) x).left_inv hy.1⟩

end Yau.NodeProofs.U02Proof
