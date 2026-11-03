import Yau.Proofs.F05JetOverlap
import Yau.Proofs.F05ChartRegularity

/-! The overlap maps in the jet graph are the actual smooth coordinate
transitions at every physical overlap point. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1600000

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {O : Set M.Carrier} {A : AtlasData M}

theorem F05Transition_overlap_value (hA : GenuineAtlas O A) {T : ℝ}
    (p : F05OverlapPoint A T) :
    F05Transition A p.left p.right p.leftCoord.val = p.rightCoord.val := by
  unfold F05Transition
  rw [p.samePoint]
  exact F05Coord_lift hA p.rightCoord.property

theorem F05Transition_overlap_contDiffAt (hA : GenuineAtlas O A) {T : ℝ}
    (p : F05OverlapPoint A T) :
    ContDiffAt ℝ ∞ (F05Transition A p.left p.right) p.leftCoord.val := by
  let x := A.center p.left
  let y := A.center p.right
  let e : OpenPartialHomeomorph (Space n) M.Carrier := (chartAt (Space n) x).symm
  have hInv : (e : Space n → M.Carrier) = chartInv x := by
    funext z
    simp [e,chartInv,ComplexModel]
  have he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source := by
    simpa [e,ComplexModel,extChartAt] using
      (mdifferentiableOn_extChartAt_symm (I := ComplexModel n) (x := x))
  have hLeftT := F05D_inverse_mem_target hA p.leftCoord.property
  have hRightT := F05D_inverse_mem_target hA p.rightCoord.property
  have hLeftB := F05D_mem_ball p.leftCoord.property
  have hRightB := F05D_mem_ball p.rightCoord.property
  have hLeftSource := (hA.1 p.left).2.2.2.2.1 ⟨p.leftCoord.val,hLeftB,rfl⟩
  have hRightSource := (hA.1 p.right).2.2.2.2.1 ⟨p.rightCoord.val,hRightB,rfl⟩
  have hCross : lift A p.left p.leftCoord.val ∈ (extChartAt (ComplexModel n) y).source := by
    rw [p.samePoint]
    exact (extChartAt (ComplexModel n) y).map_target hRightT
  have hMem : A.inverse p.left p.leftCoord.val ∈ forwardChartDomain e y := by
    refine ⟨?_,?_⟩
    · simpa [e,chartTarget,ComplexModel] using hLeftT
    · rw [hInv]
      exact hCross
  have hChart : ContDiffAt ℝ ∞ (fun z => chartPt y (chartInv x z))
      (A.inverse p.left p.leftCoord.val) := by
    have hh := (forwardChart_real_contDiffOn e he y).contDiffAt
      ((forwardChartDomain_isOpen e y).mem_nhds hMem)
    rwa [hInv] at hh
  have hRaw : chartPt y (lift A p.left p.leftCoord.val) = A.inverse p.right p.rightCoord.val := by
    rw [p.samePoint]
    exact (extChartAt (ComplexModel n) y).right_inv hRightT
  have hInverse : ContDiffAt ℝ ∞ (A.inverse p.left) p.leftCoord.val :=
    ((hA.1 p.left).2.2.2.1).contDiffAt (Metric.isOpen_ball.mem_nhds hLeftB)
  have hForward : ContDiffAt ℝ ∞ (A.forward p.right)
      (chartPt y (lift A p.left p.leftCoord.val)) := by
    rw [hRaw]
    exact ((hA.1 p.right).2.2.1).contDiffAt ((hA.1 p.right).1.mem_nhds hRightSource)
  have hComposite := hForward.comp p.leftCoord.val (hChart.comp p.leftCoord.val hInverse)
  unfold F05Transition F05Coord lift
  exact hComposite

end Yau.Proofs.F05Aux
